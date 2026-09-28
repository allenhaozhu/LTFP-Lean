/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Calculus.FullNetworkHessianClosedForm
import LTFP.MathlibExt.Probability.ChizatBachAnalyticalL2
import LTFP.MathlibExt.Probability.FullNetworkFrechet
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
# Unconditional closed-form second Fréchet derivative for `fullNet`

**KDD 2027 R4 NTK — Phase L3-final (closes analytical Chizat-Bach
`O(1/√p)` unconditionally on `ParamL2`).**

Discharges the per-tangent-vector three-term `hHessBilinearApply`
hypothesis of `fullNetL2_hessian_L2_bound_unconditional` (L3-substrate)
by proving the closed-form second Fréchet derivative of `fullNet`.

## Derivation

We route through:

1. `iteratedFDeriv_two_apply`: `iteratedFDeriv 2 f θ ![u, v] = fderiv (fderiv f) θ u v`.
2. `fderiv_clm_apply` with the second argument constant `v` gives
   `fderiv (fderiv f) θ u v = fderiv (fun θ' => fderiv f θ' v) θ u`.
3. `fullNet_fderiv_eq` (FullNetworkFrechet.lean) rewrites the inner
   `fderiv f θ' v` as an explicit scalar sum.
4. Product rule + chain rule on that sum yields the classical
   three-term Chizat-Bach expression.
5. Termwise triangle inequality + Cauchy-Schwarz gives the
   `hessianPointwiseSum` absolute-value bound.

## Main results

* `fullNet_iteratedFDeriv_two_apply_closed_form` — closed-form value.
* `fullNet_iteratedFDeriv_two_apply_bound` — absolute-value bound.
* `fullNetL2_hessian_L2_bound_final` — fully unconditional L² Hessian
  operator-norm bound.
* `chizat_bach_analytical_softplus_L2_unconditional` — fully
  unconditional headline analytical Chizat-Bach `O(1/√p)` on `ParamL2`.

## References

* Chizat & Bach (2019) *On lazy training in differentiable programming*.
* Bach (2024) *Learning Theory from First Principles*, §12.4.
-/

namespace ProbabilityTheory

open BigOperators Real

variable {d m : ℕ}

/-! ### Auxiliary: differentiability of `deriv σ` and `iteratedDeriv 2 σ = deriv (deriv σ)` -/

/-- `iteratedDeriv 2 σ = deriv (deriv σ)` pointwise. -/
private theorem iteratedDeriv_two_eq (σ : ℝ → ℝ) (z : ℝ) :
    iteratedDeriv 2 σ z = deriv (deriv σ) z := by
  simp [iteratedDeriv_succ]

/-! ### The directional first derivative, as a function of `θ'` -/

/-- For a differentiable `σ` and a fixed direction `v`, the map
`θ' ↦ fderiv (fun θ'' => fullNet σ b θ'' x) θ' v` is differentiable
in `θ'`. This is the load-bearing "differentiate the first derivative"
lemma. -/
private theorem fderiv_fullNet_apply_differentiable
    (σ : ℝ → ℝ) (hσ : ContDiff ℝ 2 σ)
    (b : Fin m → ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (v : Param d m) :
    Differentiable ℝ (fun θ' : Param d m =>
      fderiv ℝ (fun θ'' : Param d m => fullNet σ b θ'' x) θ' v) := by
  classical
  have hσ_diff : Differentiable ℝ σ := hσ.differentiable (by norm_num)
  have hσ'_diff : Differentiable ℝ (deriv σ) := hσ.differentiable_deriv_two
  -- Rewrite via fullNet_fderiv_eq, then differentiate the explicit form.
  have h_rewrite : (fun θ' : Param d m =>
      fderiv ℝ (fun θ'' : Param d m => fullNet σ b θ'' x) θ' v)
    = (fun θ' : Param d m =>
        (∑ j, (gradFullNet σ (deriv σ) b θ' x).1 j * v.1 j) +
        (∑ j, inner ℝ ((gradFullNet σ (deriv σ) b θ' x).2 j) (v.2 j))) := by
    funext θ'
    exact fullNet_fderiv_eq σ hσ_diff b θ' x v
  rw [h_rewrite]
  unfold gradFullNet
  simp only
  apply Differentiable.add
  · -- a-block: Σ_j ((1/√m) · σ(z_j θ')) · v.1 j
    apply Differentiable.fun_sum
    intro j _
    have h_pre_diff : Differentiable ℝ
        (fun θ' : Param d m => inner ℝ (θ'.2 j) x + b j) := by
      have h_w : Differentiable ℝ
          (fun θ' : Param d m => θ'.2 j) := by fun_prop
      exact (h_w.inner ℝ (differentiable_const x)).add_const (b j)
    have h_sigma : Differentiable ℝ
        (fun θ' : Param d m => σ (inner ℝ (θ'.2 j) x + b j)) :=
      hσ_diff.comp h_pre_diff
    -- (1/√m) · σ(pre) is differentiable
    have h_scaled : Differentiable ℝ
        (fun θ' : Param d m =>
          (1 / Real.sqrt (m : ℝ)) * σ (inner ℝ (θ'.2 j) x + b j)) :=
      h_sigma.const_mul _
    exact h_scaled.mul_const (v.1 j)
  · -- w-block
    apply Differentiable.fun_sum
    intro j _
    -- ⟨(1/√m · θ'.1 j · σ'(pre)) • x, v.2 j⟩
    -- = (1/√m · θ'.1 j · σ'(pre)) · ⟨x, v.2 j⟩  by linearity of inner
    have h_a_diff : Differentiable ℝ (fun θ' : Param d m => θ'.1 j) := by
      fun_prop
    have h_pre_diff : Differentiable ℝ
        (fun θ' : Param d m => inner ℝ (θ'.2 j) x + b j) := by
      have h_w : Differentiable ℝ
          (fun θ' : Param d m => θ'.2 j) := by fun_prop
      exact (h_w.inner ℝ (differentiable_const x)).add_const (b j)
    have h_sigma' : Differentiable ℝ
        (fun θ' : Param d m => deriv σ (inner ℝ (θ'.2 j) x + b j)) :=
      hσ'_diff.comp h_pre_diff
    have h_coeff : Differentiable ℝ
        (fun θ' : Param d m =>
          (1 / Real.sqrt (m : ℝ)) * θ'.1 j * deriv σ (inner ℝ (θ'.2 j) x + b j)) :=
      (h_a_diff.const_mul _).mul h_sigma'
    -- The full term is `inner ℝ (coeff • x) (v.2 j)`
    -- = coeff * inner ℝ x (v.2 j) by real_inner_smul_left.
    have h_eq :
        (fun θ' : Param d m => inner ℝ
            (((1 / Real.sqrt (m : ℝ)) * θ'.1 j *
                deriv σ (inner ℝ (θ'.2 j) x + b j)) • x) (v.2 j))
        = fun θ' : Param d m =>
            ((1 / Real.sqrt (m : ℝ)) * θ'.1 j *
              deriv σ (inner ℝ (θ'.2 j) x + b j)) *
              inner ℝ x (v.2 j) := by
      funext θ'
      rw [real_inner_smul_left]
    rw [h_eq]
    exact h_coeff.mul_const _

/-! ### Explicit closed-form second directional derivative -/

/-- **Closed-form second directional derivative.**

`(1/√m) · Σ_j [ u.1 j · σ'(z_j) · ⟨v.2 j, x⟩ + v.1 j · σ'(z_j) · ⟨u.2 j, x⟩`
  `+ θ.1 j · σ''(z_j) · ⟨u.2 j, x⟩ · ⟨v.2 j, x⟩ ]` with
`z_j = ⟨θ.2 j, x⟩ + b j`, `σ' = deriv σ`, `σ'' = deriv (deriv σ)`. -/
noncomputable def hessianClosedForm
    (σ : ℝ → ℝ) (b : Fin m → ℝ) (θ : Param d m)
    (x : EuclideanSpace ℝ (Fin d)) (u v : Param d m) : ℝ :=
  (1 / Real.sqrt (m : ℝ)) *
    ∑ j : Fin m,
      ( u.1 j * deriv σ (inner ℝ (θ.2 j) x + b j) * inner ℝ (v.2 j) x
      + v.1 j * deriv σ (inner ℝ (θ.2 j) x + b j) * inner ℝ (u.2 j) x
      + θ.1 j * deriv (deriv σ) (inner ℝ (θ.2 j) x + b j)
          * inner ℝ (u.2 j) x * inner ℝ (v.2 j) x)

/-! ### Absolute-value bound of the closed form -/

/-- **Absolute-value bound on the closed-form second derivative** by the
per-neuron pointwise sum `hessianPointwiseSum`, under the standard
bounds `|σ'| ≤ C_σ'`, `|σ''| ≤ C_σ''`, `‖x‖ ≤ C_input`, `|θ.1 j| ≤ A`.
Termwise triangle inequality + Cauchy-Schwarz. -/
theorem hessianClosedForm_abs_le
    (σ : ℝ → ℝ)
    {C_σ_prime C_σ_dprime : ℝ} (hCp : 0 ≤ C_σ_prime) (hCpp : 0 ≤ C_σ_dprime)
    (hσ' : ∀ z, |deriv σ z| ≤ C_σ_prime)
    (hσ'' : ∀ z, |deriv (deriv σ) z| ≤ C_σ_dprime)
    (b : Fin m → ℝ) (θ : Param d m)
    (x : EuclideanSpace ℝ (Fin d))
    {C_input : ℝ} (hC_input : ‖x‖ ≤ C_input) (hC_input_nn : 0 ≤ C_input)
    {A : ℝ} (hA : ∀ j, |θ.1 j| ≤ A) (hA_nn : 0 ≤ A)
    (u v : Param d m) :
    |hessianClosedForm σ b θ x u v| ≤
      hessianPointwiseSum C_σ_prime C_σ_dprime A C_input u v := by
  classical
  unfold hessianClosedForm hessianPointwiseSum
  -- √m ≥ 0
  have hsqrt_nn : 0 ≤ (1 / Real.sqrt (m : ℝ)) := by positivity
  -- Move abs inside the (1/√m) · sum
  rw [abs_mul, abs_of_nonneg hsqrt_nn]
  apply mul_le_mul_of_nonneg_left _ hsqrt_nn
  -- Now bound |Σ_j f_j| ≤ Σ_j |f_j| ≤ Σ_j g_j, termwise.
  calc |∑ j : Fin m,
          ( u.1 j * deriv σ (inner ℝ (θ.2 j) x + b j) * inner ℝ (v.2 j) x
          + v.1 j * deriv σ (inner ℝ (θ.2 j) x + b j) * inner ℝ (u.2 j) x
          + θ.1 j * deriv (deriv σ) (inner ℝ (θ.2 j) x + b j)
              * inner ℝ (u.2 j) x * inner ℝ (v.2 j) x)|
      ≤ ∑ j : Fin m,
          |( u.1 j * deriv σ (inner ℝ (θ.2 j) x + b j) * inner ℝ (v.2 j) x
          + v.1 j * deriv σ (inner ℝ (θ.2 j) x + b j) * inner ℝ (u.2 j) x
          + θ.1 j * deriv (deriv σ) (inner ℝ (θ.2 j) x + b j)
              * inner ℝ (u.2 j) x * inner ℝ (v.2 j) x)| := by
        exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin m,
          (C_σ_prime * C_input * (|u.1 j| * ‖v.2 j‖ + |v.1 j| * ‖u.2 j‖)
            + A * C_σ_dprime * C_input ^ 2 * ‖u.2 j‖ * ‖v.2 j‖) := by
        apply Finset.sum_le_sum
        intro j _
        set zj : ℝ := inner ℝ (θ.2 j) x + b j
        -- Per-neuron bound.
        -- |a + b + c| ≤ |a| + |b| + |c|
        have h_tri : |( u.1 j * deriv σ zj * inner ℝ (v.2 j) x
              + v.1 j * deriv σ zj * inner ℝ (u.2 j) x
              + θ.1 j * deriv (deriv σ) zj
                  * inner ℝ (u.2 j) x * inner ℝ (v.2 j) x)| ≤
            |u.1 j * deriv σ zj * inner ℝ (v.2 j) x| +
            |v.1 j * deriv σ zj * inner ℝ (u.2 j) x| +
            |θ.1 j * deriv (deriv σ) zj
                * inner ℝ (u.2 j) x * inner ℝ (v.2 j) x| := by
          have h1 := abs_add_le
            (u.1 j * deriv σ zj * inner ℝ (v.2 j) x +
              v.1 j * deriv σ zj * inner ℝ (u.2 j) x)
            (θ.1 j * deriv (deriv σ) zj
                * inner ℝ (u.2 j) x * inner ℝ (v.2 j) x)
          have h2 := abs_add_le
            (u.1 j * deriv σ zj * inner ℝ (v.2 j) x)
            (v.1 j * deriv σ zj * inner ℝ (u.2 j) x)
          linarith
        -- Bound each summand.
        have hu_vinner_le : |inner ℝ (v.2 j) x| ≤ ‖v.2 j‖ * C_input := by
          have h1 : |inner ℝ (v.2 j) x| ≤ ‖v.2 j‖ * ‖x‖ :=
            abs_real_inner_le_norm (v.2 j) x
          have h2 : ‖v.2 j‖ * ‖x‖ ≤ ‖v.2 j‖ * C_input :=
            mul_le_mul_of_nonneg_left hC_input (norm_nonneg _)
          exact h1.trans h2
        have hu_uinner_le : |inner ℝ (u.2 j) x| ≤ ‖u.2 j‖ * C_input := by
          have h1 : |inner ℝ (u.2 j) x| ≤ ‖u.2 j‖ * ‖x‖ :=
            abs_real_inner_le_norm (u.2 j) x
          have h2 : ‖u.2 j‖ * ‖x‖ ≤ ‖u.2 j‖ * C_input :=
            mul_le_mul_of_nonneg_left hC_input (norm_nonneg _)
          exact h1.trans h2
        have h_uvj_nn : 0 ≤ ‖v.2 j‖ := norm_nonneg _
        have h_uuj_nn : 0 ≤ ‖u.2 j‖ := norm_nonneg _
        have habs_uvj_nn : 0 ≤ |inner ℝ (v.2 j) x| := abs_nonneg _
        have habs_uuj_nn : 0 ≤ |inner ℝ (u.2 j) x| := abs_nonneg _
        -- First term: |u.1 j · σ'(z_j) · ⟨v.2 j, x⟩|
        have h_term1 :
            |u.1 j * deriv σ zj * inner ℝ (v.2 j) x| ≤
              C_σ_prime * C_input * (|u.1 j| * ‖v.2 j‖) := by
          rw [abs_mul, abs_mul]
          -- goal: |u.1 j| * |σ' z_j| * |⟨v.2 j,x⟩| ≤ C_σ' * C_input * (|u.1 j| * ‖v.2 j‖)
          have h_prod :
              |u.1 j| * |deriv σ zj| * |inner ℝ (v.2 j) x|
                ≤ |u.1 j| * C_σ_prime * (‖v.2 j‖ * C_input) := by
            have hu1_nn : 0 ≤ |u.1 j| := abs_nonneg _
            have step1 : |u.1 j| * |deriv σ zj| ≤ |u.1 j| * C_σ_prime :=
              mul_le_mul_of_nonneg_left (hσ' zj) hu1_nn
            have hu1cp_nn : 0 ≤ |u.1 j| * C_σ_prime :=
              mul_nonneg hu1_nn hCp
            calc |u.1 j| * |deriv σ zj| * |inner ℝ (v.2 j) x|
                ≤ |u.1 j| * C_σ_prime * |inner ℝ (v.2 j) x| :=
                  mul_le_mul_of_nonneg_right step1 habs_uvj_nn
              _ ≤ |u.1 j| * C_σ_prime * (‖v.2 j‖ * C_input) :=
                  mul_le_mul_of_nonneg_left hu_vinner_le hu1cp_nn
          calc |u.1 j| * |deriv σ zj| * |inner ℝ (v.2 j) x|
              ≤ |u.1 j| * C_σ_prime * (‖v.2 j‖ * C_input) := h_prod
            _ = C_σ_prime * C_input * (|u.1 j| * ‖v.2 j‖) := by ring
        -- Second term: |v.1 j · σ'(z_j) · ⟨u.2 j, x⟩|
        have h_term2 :
            |v.1 j * deriv σ zj * inner ℝ (u.2 j) x| ≤
              C_σ_prime * C_input * (|v.1 j| * ‖u.2 j‖) := by
          rw [abs_mul, abs_mul]
          have h_prod :
              |v.1 j| * |deriv σ zj| * |inner ℝ (u.2 j) x|
                ≤ |v.1 j| * C_σ_prime * (‖u.2 j‖ * C_input) := by
            have hv1_nn : 0 ≤ |v.1 j| := abs_nonneg _
            have step1 : |v.1 j| * |deriv σ zj| ≤ |v.1 j| * C_σ_prime :=
              mul_le_mul_of_nonneg_left (hσ' zj) hv1_nn
            have hv1cp_nn : 0 ≤ |v.1 j| * C_σ_prime :=
              mul_nonneg hv1_nn hCp
            calc |v.1 j| * |deriv σ zj| * |inner ℝ (u.2 j) x|
                ≤ |v.1 j| * C_σ_prime * |inner ℝ (u.2 j) x| :=
                  mul_le_mul_of_nonneg_right step1 habs_uuj_nn
              _ ≤ |v.1 j| * C_σ_prime * (‖u.2 j‖ * C_input) :=
                  mul_le_mul_of_nonneg_left hu_uinner_le hv1cp_nn
          calc |v.1 j| * |deriv σ zj| * |inner ℝ (u.2 j) x|
              ≤ |v.1 j| * C_σ_prime * (‖u.2 j‖ * C_input) := h_prod
            _ = C_σ_prime * C_input * (|v.1 j| * ‖u.2 j‖) := by ring
        -- Third term: |θ.1 j · σ''(z_j) · ⟨u.2 j, x⟩ · ⟨v.2 j, x⟩|
        have h_term3 :
            |θ.1 j * deriv (deriv σ) zj
                * inner ℝ (u.2 j) x * inner ℝ (v.2 j) x| ≤
              A * C_σ_dprime * C_input ^ 2 * ‖u.2 j‖ * ‖v.2 j‖ := by
          rw [abs_mul, abs_mul, abs_mul]
          have h_θ_j : |θ.1 j| ≤ A := hA j
          have h_ineq :
              |θ.1 j| * |deriv (deriv σ) zj| * |inner ℝ (u.2 j) x| *
                  |inner ℝ (v.2 j) x|
                ≤ A * C_σ_dprime * (‖u.2 j‖ * C_input) * (‖v.2 j‖ * C_input) := by
            have step1 : |θ.1 j| * |deriv (deriv σ) zj| ≤ A * C_σ_dprime := by
              exact mul_le_mul h_θ_j (hσ'' zj) (abs_nonneg _) hA_nn
            have hACpp_nn : 0 ≤ A * C_σ_dprime := mul_nonneg hA_nn hCpp
            have hACpp_ux_nn : 0 ≤ A * C_σ_dprime * (‖u.2 j‖ * C_input) := by
              apply mul_nonneg hACpp_nn
              exact mul_nonneg (norm_nonneg _) hC_input_nn
            calc |θ.1 j| * |deriv (deriv σ) zj| * |inner ℝ (u.2 j) x| *
                    |inner ℝ (v.2 j) x|
                ≤ A * C_σ_dprime * |inner ℝ (u.2 j) x| * |inner ℝ (v.2 j) x| := by
                  gcongr
              _ ≤ A * C_σ_dprime * (‖u.2 j‖ * C_input) * |inner ℝ (v.2 j) x| := by
                  gcongr
              _ ≤ A * C_σ_dprime * (‖u.2 j‖ * C_input) * (‖v.2 j‖ * C_input) := by
                  gcongr
          calc |θ.1 j| * |deriv (deriv σ) zj| * |inner ℝ (u.2 j) x|
                * |inner ℝ (v.2 j) x|
              ≤ A * C_σ_dprime * (‖u.2 j‖ * C_input) *
                  (‖v.2 j‖ * C_input) := h_ineq
            _ = A * C_σ_dprime * C_input ^ 2 * ‖u.2 j‖ * ‖v.2 j‖ := by ring
        -- Combine terms 1, 2, 3.
        calc |( u.1 j * deriv σ zj * inner ℝ (v.2 j) x
              + v.1 j * deriv σ zj * inner ℝ (u.2 j) x
              + θ.1 j * deriv (deriv σ) zj
                  * inner ℝ (u.2 j) x * inner ℝ (v.2 j) x)|
            ≤ |u.1 j * deriv σ zj * inner ℝ (v.2 j) x| +
                |v.1 j * deriv σ zj * inner ℝ (u.2 j) x| +
                |θ.1 j * deriv (deriv σ) zj
                    * inner ℝ (u.2 j) x * inner ℝ (v.2 j) x| := h_tri
          _ ≤ C_σ_prime * C_input * (|u.1 j| * ‖v.2 j‖) +
                C_σ_prime * C_input * (|v.1 j| * ‖u.2 j‖) +
                A * C_σ_dprime * C_input ^ 2 * ‖u.2 j‖ * ‖v.2 j‖ := by
                gcongr
          _ = C_σ_prime * C_input * (|u.1 j| * ‖v.2 j‖ + |v.1 j| * ‖u.2 j‖)
                + A * C_σ_dprime * C_input ^ 2 * ‖u.2 j‖ * ‖v.2 j‖ := by ring

/-! ### Value equality: the derivative equals the closed form -/

/-- **The Fréchet derivative of the first-order-derivative-in-a-fixed-direction
map**, evaluated on a second direction `u`, equals the closed-form second
derivative `hessianClosedForm σ b θ x u v`.

This is the load-bearing identity: it computes the value
`fderiv (fun θ' => fderiv (fun θ'' => fullNet σ b θ'' x) θ' v) θ u` in
terms of `σ`, `deriv σ`, `deriv (deriv σ)`, and the inner-product data at
`x`. Combined with `hessianClosedForm_abs_le`, this gives the absolute
value bound on the second-order directional derivative. -/
theorem fderiv_fderiv_fullNet_apply_eq
    (σ : ℝ → ℝ) (hσ : ContDiff ℝ 2 σ)
    (b : Fin m → ℝ)
    (θ : Param d m)
    (x : EuclideanSpace ℝ (Fin d))
    (u v : Param d m) :
    fderiv ℝ (fun θ' : Param d m =>
        fderiv ℝ (fun θ'' : Param d m => fullNet σ b θ'' x) θ' v) θ u =
      hessianClosedForm σ b θ x u v := by
  classical
  have hσ_diff : Differentiable ℝ σ := hσ.differentiable (by norm_num)
  have hσ'_diff : Differentiable ℝ (deriv σ) := hσ.differentiable_deriv_two
  -- Step 1: rewrite the inner function using fullNet_fderiv_eq.
  have h_rw : (fun θ' : Param d m =>
      fderiv ℝ (fun θ'' : Param d m => fullNet σ b θ'' x) θ' v)
    = fun θ' : Param d m =>
        (∑ j, (1 / Real.sqrt (m : ℝ)) *
              σ (inner ℝ (θ'.2 j) x + b j) * v.1 j) +
        (∑ j, ((1 / Real.sqrt (m : ℝ)) * θ'.1 j *
                deriv σ (inner ℝ (θ'.2 j) x + b j)) *
              inner ℝ x (v.2 j)) := by
    funext θ'
    rw [fullNet_fderiv_eq σ hσ_diff b θ' x v]
    unfold gradFullNet
    simp only
    -- LHS block 1: ∑_j ((1/√m) * σ(z_j)) * v.1 j
    -- LHS block 2: ∑_j ⟨((1/√m) * θ'.1 j * σ'(z_j)) • x, v.2 j⟩
    -- Rewrite block 2 using real_inner_smul_left; block 1 is already
    -- in the right form up to associativity.
    have h_b2 : ∀ θ'' : Param d m,
        ∑ j : Fin m, inner ℝ
            (((1 / Real.sqrt (m : ℝ)) * θ''.1 j *
                deriv σ (inner ℝ (θ''.2 j) x + b j)) • x) (v.2 j)
          = ∑ j : Fin m, ((1 / Real.sqrt (m : ℝ)) * θ''.1 j *
                deriv σ (inner ℝ (θ''.2 j) x + b j)) *
                inner ℝ x (v.2 j) := by
      intro θ''
      apply Finset.sum_congr rfl; intro j _
      rw [real_inner_smul_left]
    rw [h_b2 θ']
  rw [h_rw]
  -- Step 2: build up fderiv of the sum.
  set c : ℝ := 1 / Real.sqrt (m : ℝ) with hc_def
  -- Both sum blocks are differentiable at θ.
  have h_a_diff : ∀ j : Fin m, ∀ θ' : Param d m,
      DifferentiableAt ℝ (fun θ' : Param d m => θ'.1 j) θ' := by
    intro j θ'; fun_prop
  have h_w_diff : ∀ j : Fin m, ∀ θ' : Param d m,
      DifferentiableAt ℝ (fun θ' : Param d m => θ'.2 j) θ' := by
    intro j θ'; fun_prop
  have h_pre_diff : ∀ j : Fin m, ∀ θ' : Param d m,
      DifferentiableAt ℝ
        (fun θ' : Param d m => inner ℝ (θ'.2 j) x + b j) θ' := by
    intro j θ'
    have h_w : DifferentiableAt ℝ (fun θ' : Param d m => θ'.2 j) θ' := h_w_diff j θ'
    exact (h_w.inner ℝ (differentiableAt_const x)).add_const (b j)
  have h_sigma_at : ∀ j : Fin m, ∀ θ' : Param d m,
      DifferentiableAt ℝ
        (fun θ' : Param d m => σ (inner ℝ (θ'.2 j) x + b j)) θ' := by
    intro j θ'
    exact hσ_diff.differentiableAt.comp _ (h_pre_diff j θ')
  have h_sigma'_at : ∀ j : Fin m, ∀ θ' : Param d m,
      DifferentiableAt ℝ
        (fun θ' : Param d m => deriv σ (inner ℝ (θ'.2 j) x + b j)) θ' := by
    intro j θ'
    exact hσ'_diff.differentiableAt.comp _ (h_pre_diff j θ')
  -- Fderiv per pre-activation z_j(θ') w.r.t. θ' at u:
  --   fderiv (fun θ' => ⟨θ'.2 j, x⟩ + b j) θ u = ⟨u.2 j, x⟩
  -- This is proved in FullNetworkFrechet's h_fd_pre pattern. We reproduce
  -- it here for our own use.
  have h_fd_pre : ∀ j : Fin m,
      fderiv ℝ (fun θ' : Param d m => inner ℝ (θ'.2 j) x + b j) θ u =
        inner ℝ (u.2 j) x := by
    intro j
    -- Split as add of θ' ↦ ⟨θ'.2 j, x⟩ and constant b j.
    have h_inner_at : DifferentiableAt ℝ
        (fun θ' : Param d m => inner ℝ (θ'.2 j) x) θ := by
      have h_w : DifferentiableAt ℝ (fun θ' : Param d m => θ'.2 j) θ := h_w_diff j θ
      exact h_w.inner ℝ (differentiableAt_const x)
    rw [show (fun θ' : Param d m => inner ℝ (θ'.2 j) x + b j) =
            (fun θ' : Param d m => inner ℝ (θ'.2 j) x) +
              (fun _ : Param d m => b j) from rfl]
    rw [fderiv_add h_inner_at (differentiableAt_const (b j))]
    rw [fderiv_fun_const]
    rw [ContinuousLinearMap.add_apply]
    simp
    -- fderiv of ⟨θ'.2 j, x⟩ using fderiv_inner_apply
    rw [fderiv_inner_apply ℝ (h_w_diff j θ) (differentiableAt_const x)]
    rw [fderiv_fun_const]
    -- fderiv (θ' ↦ θ'.2 j) θ u = u.2 j
    have h_fd_w : fderiv ℝ (fun θ' : Param d m => θ'.2 j) θ u = u.2 j := by
      have h1 : HasFDerivAt (fun θ' : Param d m => θ'.2)
          (ContinuousLinearMap.snd ℝ _ (Fin m → EuclideanSpace ℝ (Fin d))) θ :=
        hasFDerivAt_snd
      have h2 : HasFDerivAt
          (fun f : Fin m → EuclideanSpace ℝ (Fin d) => f j)
          (ContinuousLinearMap.proj (R := ℝ)
            (φ := fun _ : Fin m => EuclideanSpace ℝ (Fin d)) j) θ.2 :=
        (ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : Fin m => EuclideanSpace ℝ (Fin d)) j).hasFDerivAt
      have h3 : HasFDerivAt (fun θ' : Param d m => θ'.2 j)
          ((ContinuousLinearMap.proj (R := ℝ)
              (φ := fun _ : Fin m => EuclideanSpace ℝ (Fin d)) j).comp
            (ContinuousLinearMap.snd ℝ _ (Fin m → EuclideanSpace ℝ (Fin d))))
          θ :=
        h2.comp θ h1
      rw [h3.fderiv]; rfl
    rw [h_fd_w]
    simp
  -- Fderiv of the a-projection at θ in direction u:
  --   fderiv (θ' ↦ θ'.1 j) θ u = u.1 j
  have h_fd_a : ∀ j : Fin m,
      fderiv ℝ (fun θ' : Param d m => θ'.1 j) θ u = u.1 j := by
    intro j
    have h1 : HasFDerivAt (fun θ' : Param d m => θ'.1)
        (ContinuousLinearMap.fst ℝ (Fin m → ℝ) _) θ :=
      hasFDerivAt_fst
    have h2 : HasFDerivAt (fun f : Fin m → ℝ => f j)
        (ContinuousLinearMap.proj j) θ.1 :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j).hasFDerivAt
    have h3 : HasFDerivAt (fun θ' : Param d m => θ'.1 j)
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j).comp
          (ContinuousLinearMap.fst ℝ (Fin m → ℝ) _)) θ :=
      h2.comp θ h1
    rw [h3.fderiv]; rfl
  -- Fderiv of σ(pre_j) at θ in direction u via chain rule:
  --   fderiv (θ' ↦ σ(z_j θ')) θ u = deriv σ z_j(θ) · ⟨u.2 j, x⟩
  have h_fd_sigma : ∀ j : Fin m,
      fderiv ℝ (fun θ' : Param d m => σ (inner ℝ (θ'.2 j) x + b j)) θ u =
        deriv σ (inner ℝ (θ.2 j) x + b j) * inner ℝ (u.2 j) x := by
    intro j
    have h_sigma_d : HasDerivAt σ (deriv σ (inner ℝ (θ.2 j) x + b j))
        (inner ℝ (θ.2 j) x + b j) := (hσ_diff _).hasDerivAt
    have h_pre_d : HasFDerivAt
        (fun θ' : Param d m => inner ℝ (θ'.2 j) x + b j)
        (fderiv ℝ
          (fun θ' : Param d m => inner ℝ (θ'.2 j) x + b j) θ) θ :=
      (h_pre_diff j θ).hasFDerivAt
    have h_comp := h_sigma_d.comp_hasFDerivAt (h₂ := σ) θ h_pre_d
    have h_fderiv_eq : fderiv ℝ
        (σ ∘ (fun θ' : Param d m => inner ℝ (θ'.2 j) x + b j)) θ =
        (deriv σ (inner ℝ (θ.2 j) x + b j)) •
          fderiv ℝ
            (fun θ' : Param d m => inner ℝ (θ'.2 j) x + b j) θ :=
      h_comp.fderiv
    show fderiv ℝ
        ((fun y => σ y) ∘
          (fun θ' : Param d m => inner ℝ (θ'.2 j) x + b j)) θ u = _
    rw [h_fderiv_eq]
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [h_fd_pre j]
  -- Similarly for σ'(pre_j):
  have h_fd_sigma' : ∀ j : Fin m,
      fderiv ℝ (fun θ' : Param d m => deriv σ (inner ℝ (θ'.2 j) x + b j)) θ u =
        deriv (deriv σ) (inner ℝ (θ.2 j) x + b j) * inner ℝ (u.2 j) x := by
    intro j
    have h_sigma'_d : HasDerivAt (deriv σ)
        (deriv (deriv σ) (inner ℝ (θ.2 j) x + b j))
        (inner ℝ (θ.2 j) x + b j) := (hσ'_diff _).hasDerivAt
    have h_pre_d : HasFDerivAt
        (fun θ' : Param d m => inner ℝ (θ'.2 j) x + b j)
        (fderiv ℝ
          (fun θ' : Param d m => inner ℝ (θ'.2 j) x + b j) θ) θ :=
      (h_pre_diff j θ).hasFDerivAt
    have h_comp := h_sigma'_d.comp_hasFDerivAt (h₂ := deriv σ) θ h_pre_d
    have h_fderiv_eq : fderiv ℝ
        (deriv σ ∘ (fun θ' : Param d m => inner ℝ (θ'.2 j) x + b j)) θ =
        (deriv (deriv σ) (inner ℝ (θ.2 j) x + b j)) •
          fderiv ℝ
            (fun θ' : Param d m => inner ℝ (θ'.2 j) x + b j) θ :=
      h_comp.fderiv
    show fderiv ℝ
        ((fun y => deriv σ y) ∘
          (fun θ' : Param d m => inner ℝ (θ'.2 j) x + b j)) θ u = _
    rw [h_fderiv_eq]
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [h_fd_pre j]
  -- Now compute the fderiv of the two sum blocks.
  -- BLOCK A: (Σ_j c · σ(z_j θ') · v.1 j) as a function of θ'
  set FA : Param d m → ℝ := fun θ' : Param d m =>
    ∑ j, c * σ (inner ℝ (θ'.2 j) x + b j) * v.1 j with hFA_def
  -- Per-summand differentiability
  have hFA_summand_diff : ∀ j : Fin m, ∀ θ' : Param d m,
      DifferentiableAt ℝ
        (fun θ' : Param d m => c * σ (inner ℝ (θ'.2 j) x + b j) * v.1 j) θ' := by
    intro j θ'
    have h_sigma_at := h_sigma_at j θ'
    exact (h_sigma_at.const_mul c).mul_const (v.1 j)
  have hFA_diff : DifferentiableAt ℝ FA θ :=
    DifferentiableAt.fun_sum (u := Finset.univ) (fun j _ => hFA_summand_diff j θ)
  -- Fderiv of each FA summand at θ in direction u.
  have h_fd_FA_summand : ∀ j : Fin m,
      fderiv ℝ (fun θ' : Param d m => c * σ (inner ℝ (θ'.2 j) x + b j) * v.1 j) θ u =
        c * (deriv σ (inner ℝ (θ.2 j) x + b j) * inner ℝ (u.2 j) x) * v.1 j := by
    intro j
    -- (c · σ(pre) · v.1 j) : first factor `c · σ(pre)`, second const `v.1 j`.
    have h_first : fderiv ℝ (fun θ' : Param d m =>
        c * σ (inner ℝ (θ'.2 j) x + b j)) θ u =
        c * (deriv σ (inner ℝ (θ.2 j) x + b j) * inner ℝ (u.2 j) x) := by
      rw [fderiv_const_mul (h_sigma_at j θ) c]
      rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [h_fd_sigma j]
    -- fderiv (F · v.1 j) θ u = fderiv F θ u * v.1 j since v.1 j is constant.
    have h_cconst : DifferentiableAt ℝ
        (fun θ' : Param d m => c * σ (inner ℝ (θ'.2 j) x + b j)) θ :=
      (h_sigma_at j θ).const_mul c
    rw [fderiv_fun_mul h_cconst (differentiableAt_const (v.1 j))]
    rw [ContinuousLinearMap.add_apply]
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
    rw [fderiv_fun_const]
    simp only [Pi.zero_apply, ContinuousLinearMap.zero_apply,
      mul_zero, zero_add, smul_eq_mul]
    rw [h_first]
    ring
  -- Fderiv of FA at θ in direction u.
  have h_fd_FA : fderiv ℝ FA θ u = ∑ j : Fin m,
      c * (deriv σ (inner ℝ (θ.2 j) x + b j) * inner ℝ (u.2 j) x) * v.1 j := by
    rw [fderiv_fun_sum (u := Finset.univ) (fun j _ => hFA_summand_diff j θ)]
    rw [ContinuousLinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun j _ => h_fd_FA_summand j)
  -- BLOCK B: (Σ_j (c · θ'.1 j · σ'(z_j θ')) · ⟨x, v.2 j⟩)
  set FB : Param d m → ℝ := fun θ' : Param d m =>
    ∑ j, (c * θ'.1 j * deriv σ (inner ℝ (θ'.2 j) x + b j)) * inner ℝ x (v.2 j)
    with hFB_def
  have hFB_summand_diff : ∀ j : Fin m, ∀ θ' : Param d m,
      DifferentiableAt ℝ
        (fun θ' : Param d m => (c * θ'.1 j *
              deriv σ (inner ℝ (θ'.2 j) x + b j)) * inner ℝ x (v.2 j)) θ' := by
    intro j θ'
    have h_a := h_a_diff j θ'
    have h_sigma' := h_sigma'_at j θ'
    have h_prod : DifferentiableAt ℝ
        (fun θ' : Param d m => c * θ'.1 j *
              deriv σ (inner ℝ (θ'.2 j) x + b j)) θ' :=
      (h_a.const_mul c).mul h_sigma'
    exact h_prod.mul_const (inner ℝ x (v.2 j))
  have hFB_diff : DifferentiableAt ℝ FB θ :=
    DifferentiableAt.fun_sum (u := Finset.univ) (fun j _ => hFB_summand_diff j θ)
  -- Fderiv of each FB summand at θ in direction u.
  have h_fd_FB_summand : ∀ j : Fin m,
      fderiv ℝ (fun θ' : Param d m => (c * θ'.1 j *
            deriv σ (inner ℝ (θ'.2 j) x + b j)) * inner ℝ x (v.2 j)) θ u =
        (c * u.1 j * deriv σ (inner ℝ (θ.2 j) x + b j) +
          c * θ.1 j * (deriv (deriv σ) (inner ℝ (θ.2 j) x + b j)
                        * inner ℝ (u.2 j) x)) * inner ℝ x (v.2 j) := by
    intro j
    -- Split as (c · θ'.1 j · σ'(pre)) · ⟨x, v.2 j⟩ (last factor constant).
    have h_prod : DifferentiableAt ℝ
        (fun θ' : Param d m => c * θ'.1 j *
              deriv σ (inner ℝ (θ'.2 j) x + b j)) θ :=
      ((h_a_diff j θ).const_mul c).mul (h_sigma'_at j θ)
    rw [fderiv_fun_mul h_prod (differentiableAt_const (inner ℝ x (v.2 j)))]
    rw [ContinuousLinearMap.add_apply]
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
    rw [fderiv_fun_const]
    simp only [Pi.zero_apply, ContinuousLinearMap.zero_apply,
      mul_zero, zero_add, smul_eq_mul]
    -- Now compute fderiv of (c · θ'.1 j · σ'(pre)) at θ in direction u
    -- via product rule on (c · θ'.1 j) and σ'(pre).
    have h_ca : DifferentiableAt ℝ (fun θ' : Param d m => c * θ'.1 j) θ :=
      (h_a_diff j θ).const_mul c
    have h_fd_ca : fderiv ℝ (fun θ' : Param d m => c * θ'.1 j) θ u = c * u.1 j := by
      rw [fderiv_const_mul (h_a_diff j θ) c]
      rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [h_fd_a j]
    rw [fderiv_fun_mul h_ca (h_sigma'_at j θ)]
    rw [ContinuousLinearMap.add_apply]
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
    rw [h_fd_ca, h_fd_sigma' j]
    simp only [smul_eq_mul]
    ring
  -- Fderiv of FB at θ in direction u.
  have h_fd_FB : fderiv ℝ FB θ u = ∑ j : Fin m,
      (c * u.1 j * deriv σ (inner ℝ (θ.2 j) x + b j) +
        c * θ.1 j * (deriv (deriv σ) (inner ℝ (θ.2 j) x + b j)
                      * inner ℝ (u.2 j) x)) * inner ℝ x (v.2 j) := by
    rw [fderiv_fun_sum (u := Finset.univ) (fun j _ => hFB_summand_diff j θ)]
    rw [ContinuousLinearMap.sum_apply]
    exact Finset.sum_congr rfl (fun j _ => h_fd_FB_summand j)
  -- Combine: fderiv of the sum is the sum of fderivs.
  -- The current goal is
  --   fderiv ℝ (fun θ' => (∑_j c*σ(z_j θ')*v.1 j) + (∑_j (c*θ'.1 j*σ'(z_j θ'))*⟨x,v.2 j⟩)) θ u
  --   = hessianClosedForm σ b θ x u v
  -- Use HasFDerivAt.add to build the value of the outer fderiv.
  have hFA_hd : HasFDerivAt FA (fderiv ℝ FA θ) θ := hFA_diff.hasFDerivAt
  have hFB_hd : HasFDerivAt FB (fderiv ℝ FB θ) θ := hFB_diff.hasFDerivAt
  have h_outer : HasFDerivAt (fun θ' : Param d m => FA θ' + FB θ')
      (fderiv ℝ FA θ + fderiv ℝ FB θ) θ := hFA_hd.add hFB_hd
  have h_outer_eq : (fun θ' : Param d m =>
      (∑ j, c * σ (inner ℝ (θ'.2 j) x + b j) * v.1 j) +
      (∑ j, (c * θ'.1 j * deriv σ (inner ℝ (θ'.2 j) x + b j)) *
            inner ℝ x (v.2 j))) = fun θ' : Param d m => FA θ' + FB θ' := by
    funext θ'; rfl
  rw [h_outer_eq, h_outer.fderiv]
  rw [ContinuousLinearMap.add_apply]
  rw [h_fd_FA, h_fd_FB]
  -- Merge sums; rewrite ⟨x, v.2 j⟩ = ⟨v.2 j, x⟩ per term; close by `ring`.
  unfold hessianClosedForm
  have h_symm_v : ∀ j : Fin m, inner ℝ x (v.2 j) = inner ℝ (v.2 j) x :=
    fun j => real_inner_comm (v.2 j) x
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [h_symm_v j]
  ring

/-! ### Bridge: `iteratedFDeriv 2` apply-formula via `fderiv_clm_apply` -/

/-- **Second iterated Fréchet derivative apply-formula (closed form).**

For a `ContDiff ℝ 2` activation `σ`, at any parameter `θ` and pair of
tangent vectors `u, v : Param d m`, the second iterated Fréchet
derivative of `fullNet σ b · x` at `θ` applied to `![u, v]` equals the
closed-form expression `hessianClosedForm σ b θ x u v`. -/
theorem fullNet_iteratedFDeriv_two_apply_closed_form
    (σ : ℝ → ℝ) (hσ : ContDiff ℝ 2 σ)
    (b : Fin m → ℝ)
    (θ : Param d m)
    (x : EuclideanSpace ℝ (Fin d))
    (u v : Param d m) :
    iteratedFDeriv ℝ 2 (fun θ' : Param d m => fullNet σ b θ' x) θ ![u, v] =
      hessianClosedForm σ b θ x u v := by
  classical
  have hσ_diff : Differentiable ℝ σ := hσ.differentiable (by norm_num)
  have h_c2 : ContDiff ℝ 2 (fun θ' : Param d m => fullNet σ b θ' x) :=
    fullNet_contDiff_two σ hσ b x
  -- Extract Differentiable (fderiv fullNet).
  have h_fderiv_c1 : ContDiff ℝ 1
      (fderiv ℝ (fun θ' : Param d m => fullNet σ b θ' x)) := by
    have := (contDiff_succ_iff_fderiv (𝕜 := ℝ)
      (f := fun θ' : Param d m => fullNet σ b θ' x) (n := 1)).mp
      (by simpa using h_c2)
    exact this.2.2
  have h_fderiv_diff : Differentiable ℝ
      (fderiv ℝ (fun θ' : Param d m => fullNet σ b θ' x)) :=
    h_fderiv_c1.differentiable (by norm_num)
  -- Step 1: iteratedFDeriv_two_apply.
  have h1 : iteratedFDeriv ℝ 2
        (fun θ' : Param d m => fullNet σ b θ' x) θ ![u, v] =
      fderiv ℝ (fderiv ℝ (fun θ' : Param d m => fullNet σ b θ' x)) θ u v := by
    have h := iteratedFDeriv_two_apply
      (𝕜 := ℝ) (f := fun θ' : Param d m => fullNet σ b θ' x) θ ![u, v]
    simpa using h
  -- Step 2: bridge fderiv (fderiv f) θ u v = fderiv (fun θ' => fderiv f θ' v) θ u
  -- via fderiv_clm_apply.
  have h_clm_apply :
      fderiv ℝ (fun θ' : Param d m =>
          fderiv ℝ (fun θ'' : Param d m => fullNet σ b θ'' x) θ' v) θ u =
      fderiv ℝ (fderiv ℝ (fun θ' : Param d m => fullNet σ b θ' x)) θ u v := by
    have h_c_at : DifferentiableAt ℝ
        (fderiv ℝ (fun θ' : Param d m => fullNet σ b θ' x)) θ :=
      h_fderiv_diff θ
    have h_v_at : DifferentiableAt ℝ (fun _ : Param d m => v) θ :=
      differentiableAt_const v
    rw [fderiv_clm_apply h_c_at h_v_at]
    rw [ContinuousLinearMap.add_apply]
    rw [fderiv_fun_const]
    rw [ContinuousLinearMap.comp_apply]
    simp only [Pi.zero_apply, ContinuousLinearMap.zero_apply, map_zero,
      zero_add]
    rw [ContinuousLinearMap.flip_apply]
  -- Combine.
  rw [h1, ← h_clm_apply]
  exact fderiv_fderiv_fullNet_apply_eq σ hσ b θ x u v

/-! ### Absolute-value bound: the load-bearing three-term inequality -/

/-- **Closed-form absolute-value bound on the second iterated Fréchet
derivative of `fullNet`, applied to a pair of tangent vectors.**

This is the load-bearing `hHessBilinearApply` interface unconditionally
discharged from the closed-form derivation:

`|iteratedFDeriv 2 (fun θ' => fullNet σ b θ' x) θ ![u, v]|`
  ` ≤ hessianPointwiseSum C_σ' C_σ'' A C_input u v`. -/
theorem fullNet_iteratedFDeriv_two_apply_bound
    (σ : ℝ → ℝ) (hσ : ContDiff ℝ 2 σ)
    {C_σ_prime C_σ_dprime : ℝ} (hCp : 0 ≤ C_σ_prime) (hCpp : 0 ≤ C_σ_dprime)
    (hσ' : ∀ z, |deriv σ z| ≤ C_σ_prime)
    (hσ'' : ∀ z, |iteratedDeriv 2 σ z| ≤ C_σ_dprime)
    (b : Fin m → ℝ) (θ : Param d m) (x : EuclideanSpace ℝ (Fin d))
    {C_input : ℝ} (hC_input : ‖x‖ ≤ C_input) (hC_input_nn : 0 ≤ C_input)
    {A : ℝ} (hA : ∀ j, |θ.1 j| ≤ A) (hA_nn : 0 ≤ A)
    (u v : Param d m) :
    |iteratedFDeriv ℝ 2 (fun θ' : Param d m => fullNet σ b θ' x) θ ![u, v]|
      ≤ hessianPointwiseSum C_σ_prime C_σ_dprime A C_input u v := by
  rw [fullNet_iteratedFDeriv_two_apply_closed_form σ hσ b θ x u v]
  -- σ'' in the closed form is `deriv (deriv σ) = iteratedDeriv 2 σ`.
  have hσ''_deriv : ∀ z, |deriv (deriv σ) z| ≤ C_σ_dprime := by
    intro z
    have h := hσ'' z
    rw [iteratedDeriv_two_eq σ z] at h
    exact h
  exact hessianClosedForm_abs_le σ hCp hCpp hσ' hσ''_deriv b θ x
    hC_input hC_input_nn hA hA_nn u v

/-! ### Wiring to L3-substrate: unconditional L² Hessian operator-norm bound -/

/-- **Fully unconditional L² Hessian operator-norm bound.**

Discharges the `hHessBilinearApply` hypothesis in
`fullNetL2_hessian_L2_bound_unconditional` from the closed-form second
Fréchet derivative of `fullNet` proved in this file. The final bound

`‖iteratedFDeriv 2 (fullNetL2 σ b · x) θ‖ ≤ hessianL2Const / √m`

now consumes only the bounds `|σ'| ≤ C_σ'`, `|σ''| ≤ C_σ''`,
`‖x‖ ≤ C_input`, and `|θ.1 j| ≤ A`. -/
theorem fullNetL2_hessian_L2_bound_final
    (σ : ℝ → ℝ) (hσ : ContDiff ℝ 2 σ)
    {C_σ_prime C_σ_dprime : ℝ} (hCp : 0 ≤ C_σ_prime) (hCpp : 0 ≤ C_σ_dprime)
    (hσ' : ∀ z, |deriv σ z| ≤ C_σ_prime)
    (hσ'' : ∀ z, |iteratedDeriv 2 σ z| ≤ C_σ_dprime)
    [NeZero m]
    (b : Fin m → ℝ) (θ : ParamL2 d m) (x : EuclideanSpace ℝ (Fin d))
    {C_input : ℝ} (hC_input : ‖x‖ ≤ C_input)
    {A : ℝ} (hA : ∀ j, |(ParamL2.toParam θ).1 j| ≤ A) (hA_nn : 0 ≤ A) :
    ‖iteratedFDeriv ℝ 2 (fun θ' : ParamL2 d m => fullNetL2 σ b θ' x) θ‖ ≤
      (C_σ_dprime * A * C_input ^ 2 + 2 * C_σ_prime * C_input) /
        Real.sqrt m := by
  -- Discharge hHessBilinearApply and pipe through the L3-substrate wrapper.
  apply fullNetL2_hessian_L2_bound_unconditional σ hσ C_σ_prime C_σ_dprime
    hCp hCpp hσ' hσ'' b θ x C_input hC_input A hA hA_nn
  intro u v
  exact fullNet_iteratedFDeriv_two_apply_bound σ hσ hCp hCpp hσ' hσ''
    b (ParamL2.toParam θ) x hC_input (le_trans (norm_nonneg _) hC_input)
    hA hA_nn (ParamL2.toParam u) (ParamL2.toParam v)

end ProbabilityTheory

/-! ### Downstream: fully unconditional analytical Chizat-Bach on `ParamL2` -/

namespace LTFP.MathlibExt.Probability

open BigOperators Real Set ProbabilityTheory

variable {d m : ℕ}

/-- **Fully unconditional analytical Chizat-Bach `O(1/√p)` linearization
theorem on `ParamL2` for any `ContDiff ℝ 2` activation.**

Composes `fullNetL2_hessian_L2_bound_final` (this file) with
`chizat_bach_analytical_softplus_L2` (L5) by discharging `hHess_seg`
pointwise via the closed-form Hessian bound at every `z` on the
segment. The uniform `hA_seg` output-weight bound along the segment is
the only remaining modeling hypothesis. -/
theorem chizat_bach_analytical_softplus_L2_unconditional
    (σ : ℝ → ℝ)
    (hσ_contDiff : ContDiff ℝ 2 σ)
    {C_σ_prime C_σ_dprime : ℝ} (hCp : 0 ≤ C_σ_prime) (hCpp : 0 ≤ C_σ_dprime)
    (hσ' : ∀ z, |deriv σ z| ≤ C_σ_prime)
    (hσ'' : ∀ z, |iteratedDeriv 2 σ z| ≤ C_σ_dprime)
    (b : Fin m → ℝ)
    (θ_L2 : ℝ → ParamL2 d m)
    (θ₀_L2 : ParamL2 d m) (hθ_start : θ_L2 0 = θ₀_L2)
    (hθ_diff : Differentiable ℝ θ_L2)
    (G : ℝ → ParamL2 d m)
    (hθ_ODE : ∀ t, deriv θ_L2 t = -G t)
    {Kmax : ℝ} (hKmax_pos : 0 < Kmax)
    (r_norm : ℝ → ℝ)
    (r0_norm : ℝ) (hr0_nn : 0 ≤ r0_norm)
    (hr_decay : ∀ t, r_norm t ≤ r0_norm * Real.exp (-(Kmax * t / 2)))
    (hG_bound : ∀ t, ‖G t‖ ≤ Real.sqrt Kmax * r_norm t)
    {T : ℝ} (hT : 0 ≤ T)
    (x : EuclideanSpace ℝ (Fin d))
    {C_input : ℝ} (hC_input : ‖x‖ ≤ C_input)
    {A : ℝ} (hA_nn : 0 ≤ A)
    [NeZero m]
    -- Uniform output-weight bound along the segment.
    (hA_seg : ∀ z ∈ segment ℝ θ₀_L2 (θ_L2 T),
        ∀ j, |(ParamL2.toParam z).1 j| ≤ A) :
    |fullNetL2 σ b (θ_L2 T) x - fullNetL2 σ b θ₀_L2 x
        - fderiv ℝ (fun θ' : ParamL2 d m => fullNetL2 σ b θ' x) θ₀_L2
            (θ_L2 T - θ₀_L2)|
      ≤ ((C_σ_dprime * A * C_input ^ 2 + 2 * C_σ_prime * C_input) /
            (2 * Real.sqrt (m : ℝ)))
          * (2 * r0_norm * Real.sqrt Kmax / Kmax) ^ 2 := by
  set L₀ : ℝ := C_σ_dprime * A * C_input ^ 2 + 2 * C_σ_prime * C_input
    with hL₀_def
  have hC_input_nn : 0 ≤ C_input := le_trans (norm_nonneg _) hC_input
  have hL₀_nn : 0 ≤ L₀ := by
    have h1 : 0 ≤ C_σ_dprime * A * C_input ^ 2 :=
      mul_nonneg (mul_nonneg hCpp hA_nn) (sq_nonneg _)
    have h2 : 0 ≤ 2 * C_σ_prime * C_input :=
      mul_nonneg (mul_nonneg (by norm_num) hCp) hC_input_nn
    have : L₀ = C_σ_dprime * A * C_input ^ 2 + 2 * C_σ_prime * C_input := rfl
    linarith
  -- Discharge hHess_seg via fullNetL2_hessian_L2_bound_final at every z on segment.
  have hHess_seg : ∀ z ∈ segment ℝ θ₀_L2 (θ_L2 T),
      ‖iteratedFDeriv ℝ 2 (fun θ' : ParamL2 d m => fullNetL2 σ b θ' x) z‖
        ≤ L₀ / Real.sqrt (m : ℝ) := by
    intro z hz
    exact fullNetL2_hessian_L2_bound_final σ hσ_contDiff hCp hCpp hσ' hσ''
      b z x hC_input (hA_seg z hz) hA_nn
  exact chizat_bach_analytical_softplus_L2 σ hσ_contDiff b θ_L2 θ₀_L2
    hθ_start hθ_diff G hθ_ODE hKmax_pos r_norm r0_norm hr0_nn hr_decay
    hG_bound hT hL₀_nn x hHess_seg

end LTFP.MathlibExt.Probability

#print axioms ProbabilityTheory.fullNet_iteratedFDeriv_two_apply_closed_form
#print axioms ProbabilityTheory.fullNet_iteratedFDeriv_two_apply_bound
#print axioms ProbabilityTheory.fullNetL2_hessian_L2_bound_final
#print axioms LTFP.MathlibExt.Probability.chizat_bach_analytical_softplus_L2_unconditional
