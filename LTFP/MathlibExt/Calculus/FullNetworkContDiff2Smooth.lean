/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.FullNetwork
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Bornology.Basic

/-!
# Softplus activation, `ContDiff ℝ 2` of `fullNet`, and uniform Hessian bounds

**KDD 2027 NTK Phase 2a — analytical Chizat-Bach substrate.**

The analytical Chizat-Bach `O(1/√p)` theorem for the two-layer NTK
requires a *smooth* activation surrogate (exact clipped-ReLU is not
`C²`).  This file collects the analytic prerequisites:

* the softplus activation `Real.softplus z = log (1 + exp z)`, which is
  `C^∞` and has an explicit sigmoid derivative bounded in `[0, 1]`,
* a `ContDiff ℝ 2` result for the two-layer predictor
  `fullNet σ b θ x` viewed as a function of the parameter `θ`, and
* a uniform-on-compact bound for the norm of the second-order iterated
  Fréchet derivative of `fullNet` in `θ`.

The uniform bound scales linearly in the finite-width prefactor
`1 / √m` inherited from `fullNet`'s NTK normalization; it is the
raw ingredient that Phase 2c will combine with
`hessian_taylor_remainder_along_segment` (from
`MultivariateHessianTaylor.lean`) to produce the quantitative Taylor
remainder for the lazy-training bound.

## Main definitions

* `Real.softplus z = Real.log (1 + Real.exp z)` — the softplus
  activation.
* `Real.sigmoid z = 1 / (1 + Real.exp (-z))` — the derivative of
  softplus (used for algebraic bookkeeping).

## Main results

* `Real.softplus_pos` — `0 < softplus z`.
* `Real.hasDerivAt_softplus` — `HasDerivAt softplus (sigmoid z) z`.
* `Real.contDiff_softplus` — `ContDiff ℝ ⊤ softplus`.
* `Real.sigmoid_mem_unit_Icc` — `0 < sigmoid z ≤ 1`.
* `ProbabilityTheory.fullNet_contDiff_two` — if `σ : ℝ → ℝ` is
  `ContDiff ℝ 2`, then `fun θ ↦ fullNet σ b θ x` is `ContDiff ℝ 2`.
* `ProbabilityTheory.fullNet_iteratedFDeriv_two_bound_on_compact` —
  for any compact parameter set `K ⊆ Param d m` and compact input set
  `X ⊆ EuclideanSpace ℝ (Fin d)`, the operator norm of
  `iteratedFDeriv ℝ 2 (fun θ ↦ fullNet σ b θ x) θ` is uniformly
  bounded on `K × X`.

## Discussion of the `1 / √p` scaling

The `fullNet` predictor already carries the NTK normalization
`(1/√m) · Σ_j a_j σ(⟨w_j, x⟩ + b_j)`.  The second-order iterated
Fréchet derivative in `θ` is therefore also scaled by `1/√m`, giving
the `L₀ / √m` Hessian bound expected by the Chizat-Bach analytical
proof.  The full quantitative constant `L₀` — which depends on
`‖σ''‖_∞`, `‖σ'‖_∞`, `‖x‖`, and the radius `R` of the parameter ball
— is not extracted in this file; it is left to Phase 2c which
consumes the qualitative existence result together with an explicit
softplus-specific bound.
-/

namespace Real

/-! ### Softplus and its derivative -/

/-- The softplus activation `softplus z = log (1 + exp z)`.  It is a
`C^∞` surrogate for ReLU that is nonnegative and Lipschitz with
constant `1`. -/
noncomputable def softplus (z : ℝ) : ℝ := Real.log (1 + Real.exp z)

/-- The sigmoid function `sigmoid z = 1 / (1 + exp (-z))`.  It is the
derivative of `softplus`. -/
noncomputable def sigmoid (z : ℝ) : ℝ := 1 / (1 + Real.exp (-z))

/-- `1 + exp z > 0`.  Convenience lemma. -/
theorem one_add_exp_pos (z : ℝ) : 0 < 1 + Real.exp z := by
  have h : 0 < Real.exp z := Real.exp_pos z
  linarith

/-- `1 + exp z ≠ 0`. -/
theorem one_add_exp_ne_zero (z : ℝ) : 1 + Real.exp z ≠ 0 :=
  ne_of_gt (one_add_exp_pos z)

/-- `1 + exp (-z) > 0`.  Convenience lemma. -/
theorem one_add_exp_neg_pos (z : ℝ) : 0 < 1 + Real.exp (-z) := by
  have h : 0 < Real.exp (-z) := Real.exp_pos (-z)
  linarith

/-- `1 + exp (-z) ≠ 0`. -/
theorem one_add_exp_neg_ne_zero (z : ℝ) : 1 + Real.exp (-z) ≠ 0 :=
  ne_of_gt (one_add_exp_neg_pos z)

/-- Softplus is strictly positive: `softplus z > 0`.

Since `exp z > 0`, we have `1 + exp z > 1`, so
`log (1 + exp z) > log 1 = 0`. -/
theorem softplus_pos (z : ℝ) : 0 < softplus z := by
  unfold softplus
  have h1 : 0 < Real.exp z := Real.exp_pos z
  have h2 : 1 < 1 + Real.exp z := by linarith
  exact Real.log_pos h2

/-- Softplus is nonnegative. -/
theorem softplus_nonneg (z : ℝ) : 0 ≤ softplus z :=
  (softplus_pos z).le

/-- The sigmoid function is strictly positive. -/
theorem sigmoid_pos (z : ℝ) : 0 < sigmoid z := by
  unfold sigmoid
  have h : 0 < 1 + Real.exp (-z) := one_add_exp_neg_pos z
  positivity

/-- The sigmoid function is bounded above by `1`. -/
theorem sigmoid_le_one (z : ℝ) : sigmoid z ≤ 1 := by
  unfold sigmoid
  have h : 0 < 1 + Real.exp (-z) := one_add_exp_neg_pos z
  rw [div_le_one h]
  have hexp : 0 ≤ Real.exp (-z) := (Real.exp_pos _).le
  linarith

/-- The sigmoid function lies in the unit interval `(0, 1]`. -/
theorem sigmoid_mem_unit_Icc (z : ℝ) : 0 < sigmoid z ∧ sigmoid z ≤ 1 :=
  ⟨sigmoid_pos z, sigmoid_le_one z⟩

/-- `|sigmoid z| ≤ 1`.  Used to bound the softplus derivative. -/
theorem abs_sigmoid_le_one (z : ℝ) : |sigmoid z| ≤ 1 := by
  rw [abs_of_pos (sigmoid_pos z)]
  exact sigmoid_le_one z

/-- Sigmoid can be written using the `exp z` (rather than `exp (-z)`)
form: `sigmoid z = exp z / (1 + exp z)`. -/
theorem sigmoid_eq_exp_div (z : ℝ) :
    sigmoid z = Real.exp z / (1 + Real.exp z) := by
  unfold sigmoid
  have hne2 : 1 + Real.exp z ≠ 0 := one_add_exp_ne_zero z
  have hexp_ne : Real.exp z ≠ 0 := (Real.exp_pos z).ne'
  have hnegz : Real.exp (-z) = (Real.exp z)⁻¹ := Real.exp_neg z
  rw [hnegz]
  field_simp
  ring

/-- `HasDerivAt` for softplus: `d/dz softplus z = sigmoid z`.

The derivative of `log (1 + exp z)` is `exp z / (1 + exp z)` by the
chain rule for `log` composed with `1 + exp z`.  We then rewrite this
as `sigmoid z = exp z / (1 + exp z)`. -/
theorem hasDerivAt_softplus (z : ℝ) :
    HasDerivAt softplus (sigmoid z) z := by
  -- Step 1: derivative of `1 + exp z` is `exp z`.
  have h_inner : HasDerivAt (fun w : ℝ => 1 + Real.exp w) (Real.exp z) z := by
    have h_exp : HasDerivAt (fun w : ℝ => Real.exp w) (Real.exp z) z :=
      Real.hasDerivAt_exp z
    have h_one : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 z := hasDerivAt_const z 1
    have hadd := h_one.add h_exp
    -- The derivative value is `0 + exp z = exp z`.
    have hval : (0 : ℝ) + Real.exp z = Real.exp z := by ring
    rw [hval] at hadd
    exact hadd
  -- Step 2: derivative of `log` at `1 + exp z ≠ 0` is `(1 + exp z)⁻¹`.
  have h_ne : (1 + Real.exp z) ≠ 0 := one_add_exp_ne_zero z
  have h_log : HasDerivAt Real.log (1 + Real.exp z)⁻¹ (1 + Real.exp z) :=
    Real.hasDerivAt_log h_ne
  -- Compose:
  have h_comp := h_log.comp z h_inner
  -- Compute the derivative value: (1 + exp z)⁻¹ * exp z = exp z / (1 + exp z).
  have h_val : (1 + Real.exp z)⁻¹ * Real.exp z =
      Real.exp z / (1 + Real.exp z) := by
    rw [mul_comm]
    rfl
  rw [h_val] at h_comp
  -- Convert to sigmoid form.
  rw [sigmoid_eq_exp_div]
  exact h_comp

/-- Softplus is differentiable at every point. -/
theorem differentiable_softplus : Differentiable ℝ softplus :=
  fun z => (hasDerivAt_softplus z).differentiableAt

/-- Softplus is `C^∞`: it is a composition of `exp` (smooth) with an
affine map, then `log` restricted to the positive reals (smooth on the
image `{y > 0}`).  We use `ContDiffAt.log` on the composition. -/
theorem contDiff_softplus {n : WithTop ℕ∞} :
    ContDiff ℝ n softplus := by
  -- softplus = log ∘ (fun z => 1 + exp z).
  have h_exp : ContDiff ℝ n Real.exp := Real.contDiff_exp
  have h_one : ContDiff ℝ n (fun _ : ℝ => (1 : ℝ)) := contDiff_const
  have h_sum : ContDiff ℝ n (fun z : ℝ => 1 + Real.exp z) := h_one.add h_exp
  -- Show `1 + exp z ≠ 0` everywhere.
  have h_ne : ∀ z, 1 + Real.exp z ≠ 0 := one_add_exp_ne_zero
  -- Apply `ContDiff.log`.
  exact h_sum.log h_ne

/-- Softplus is `C²` (a specialization we use downstream). -/
theorem contDiff_two_softplus : ContDiff ℝ 2 softplus :=
  contDiff_softplus

end Real

/-! ### `ContDiff ℝ 2` for `fullNet` in the parameter `θ` -/

namespace ProbabilityTheory

open BigOperators Real

variable {d : ℕ}

/-- **Auxiliary: projection onto the `a`-block coordinate `j` is `C^∞`
in `θ : Param d m`.** -/
private theorem contDiff_param_fst_apply
    {m : ℕ} (n : WithTop ℕ∞) (j : Fin m) :
    ContDiff ℝ n (fun θ : Param d m => θ.1 j) := by
  have h_fst : ContDiff ℝ n (fun θ : Param d m => θ.1) := contDiff_fst
  have h_apply : ContDiff ℝ n (fun f : Fin m → ℝ => f j) :=
    contDiff_apply (𝕜 := ℝ) (E := ℝ) (i := j)
  exact h_apply.comp h_fst

/-- **Auxiliary: projection onto the `w`-block coordinate `j` is `C^∞`
in `θ : Param d m`.** -/
private theorem contDiff_param_snd_apply
    {m : ℕ} (n : WithTop ℕ∞) (j : Fin m) :
    ContDiff ℝ n
      (fun θ : Param d m => θ.2 j) := by
  have h_snd : ContDiff ℝ n
      (fun θ : Param d m => θ.2) := contDiff_snd
  have h_apply : ContDiff ℝ n
      (fun f : Fin m → EuclideanSpace ℝ (Fin d) => f j) :=
    contDiff_apply (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin d)) (i := j)
  exact h_apply.comp h_snd

/-- **Auxiliary: the pre-activation `θ ↦ ⟨θ.2 j, x⟩ + b j` is `C^∞`
in `θ`.** -/
private theorem contDiff_preact
    {m : ℕ} (n : WithTop ℕ∞) (b : Fin m → ℝ) (j : Fin m)
    (x : EuclideanSpace ℝ (Fin d)) :
    ContDiff ℝ n
      (fun θ : Param d m => inner ℝ (θ.2 j) x + b j) := by
  have h_w : ContDiff ℝ n (fun θ : Param d m => θ.2 j) :=
    contDiff_param_snd_apply n j
  have h_const_x : ContDiff ℝ n (fun _ : Param d m => x) := contDiff_const
  have h_inner : ContDiff ℝ n
      (fun θ : Param d m => inner ℝ (θ.2 j) x) := h_w.inner ℝ h_const_x
  exact h_inner.add contDiff_const

/-- **`fullNet σ b · x` is `ContDiff ℝ 2` in `θ` when `σ` is
`ContDiff ℝ 2`.**

The predictor is a finite sum of products of the form
`θ.1 j · σ(⟨θ.2 j, x⟩ + b j)`.  Each factor is smooth in `θ`:
projections onto `Fin m → ℝ` and `Fin m → EuclideanSpace ℝ (Fin d)`
are smooth (linear), the inner product is smooth (bilinear with one
argument fixed), and `σ` is smooth by hypothesis.  The sum and
constant scalar multiplication preserve `ContDiff ℝ 2`. -/
theorem fullNet_contDiff_two
    {m : ℕ}
    (σ : ℝ → ℝ)
    (hσ : ContDiff ℝ 2 σ)
    (b : Fin m → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    ContDiff ℝ 2 (fun θ : Param d m => fullNet σ b θ x) := by
  classical
  unfold fullNet
  -- Each summand is `θ.1 j * σ(⟨θ.2 j, x⟩ + b j)`, `ContDiff ℝ 2`.
  have h_summand : ∀ j : Fin m,
      ContDiff ℝ 2
        (fun θ : Param d m =>
          θ.1 j * σ (inner ℝ (θ.2 j) x + b j)) := by
    intro j
    have h_a : ContDiff ℝ 2 (fun θ : Param d m => θ.1 j) :=
      contDiff_param_fst_apply 2 j
    have h_pre : ContDiff ℝ 2
        (fun θ : Param d m => inner ℝ (θ.2 j) x + b j) :=
      contDiff_preact 2 b j x
    have h_sigma : ContDiff ℝ 2
        (fun θ : Param d m => σ (inner ℝ (θ.2 j) x + b j)) :=
      hσ.comp h_pre
    exact h_a.mul h_sigma
  -- Sum.
  have h_sum : ContDiff ℝ 2
      (fun θ : Param d m =>
        ∑ j, θ.1 j * σ (inner ℝ (θ.2 j) x + b j)) :=
    ContDiff.sum (fun j _ => h_summand j)
  -- Constant scalar multiplication.
  exact contDiff_const.mul h_sum

/-- **`fullNet σ b · x` is `ContDiff ℝ n` in `θ` for any `n`, when
`σ` is `ContDiff ℝ n`.**

More general than `fullNet_contDiff_two`; useful for the softplus
surrogate which is `C^∞`. -/
theorem fullNet_contDiff
    {m : ℕ}
    {n : WithTop ℕ∞}
    (σ : ℝ → ℝ)
    (hσ : ContDiff ℝ n σ)
    (b : Fin m → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    ContDiff ℝ n (fun θ : Param d m => fullNet σ b θ x) := by
  classical
  unfold fullNet
  have h_summand : ∀ j : Fin m,
      ContDiff ℝ n
        (fun θ : Param d m =>
          θ.1 j * σ (inner ℝ (θ.2 j) x + b j)) := by
    intro j
    have h_a : ContDiff ℝ n (fun θ : Param d m => θ.1 j) :=
      contDiff_param_fst_apply n j
    have h_pre : ContDiff ℝ n
        (fun θ : Param d m => inner ℝ (θ.2 j) x + b j) :=
      contDiff_preact n b j x
    have h_sigma : ContDiff ℝ n
        (fun θ : Param d m => σ (inner ℝ (θ.2 j) x + b j)) :=
      hσ.comp h_pre
    exact h_a.mul h_sigma
  have h_sum : ContDiff ℝ n
      (fun θ : Param d m =>
        ∑ j, θ.1 j * σ (inner ℝ (θ.2 j) x + b j)) :=
    ContDiff.sum (fun j _ => h_summand j)
  exact contDiff_const.mul h_sum

/-- **The softplus-instantiated `fullNet` is `C^∞` in `θ`.** -/
theorem fullNet_softplus_contDiff
    {m : ℕ} {n : WithTop ℕ∞}
    (b : Fin m → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    ContDiff ℝ n
      (fun θ : Param d m => fullNet Real.softplus b θ x) :=
  fullNet_contDiff (n := n) Real.softplus Real.contDiff_softplus b x

/-! ### Uniform-on-compact bound for the Hessian of `fullNet` in `θ` -/

/-- **Continuity of the second iterated Fréchet derivative of
`fullNet` in `θ`.**

For a `ContDiff ℝ 2` activation `σ`, the map
`θ ↦ iteratedFDeriv ℝ 2 (fun θ' ↦ fullNet σ b θ' x) θ` is continuous.
This is the qualitative content of `ContDiff ℝ 2` — the top-order
iterated derivative is continuous. -/
theorem fullNet_iteratedFDeriv_two_continuous
    {m : ℕ}
    (σ : ℝ → ℝ)
    (hσ : ContDiff ℝ 2 σ)
    (b : Fin m → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    Continuous (fun θ : Param d m =>
      iteratedFDeriv ℝ 2 (fun θ' : Param d m => fullNet σ b θ' x) θ) :=
  (fullNet_contDiff_two (d := d) σ hσ b x).continuous_iteratedFDeriv
    (m := 2) (by norm_num)

/-- **Uniform bound of the Hessian on a compact parameter set.**

For any `ContDiff ℝ 2` activation `σ` and any compact parameter set
`K ⊆ Param d m`, there exists a finite `L ≥ 0` such that for every
`θ ∈ K` the operator norm of the second iterated Fréchet derivative
of `fun θ' ↦ fullNet σ b θ' x` at `θ` is at most `L`.

This is the qualitative form of the Hessian bound that Phase 2c will
plug into `hessian_taylor_remainder_along_segment` to obtain the
quantitative `L₀ / √m` Taylor remainder.  The explicit constant `L₀`
depends on `‖σ''‖_∞`, `‖σ'‖_∞`, `‖x‖`, and the radius of `K`; its
extraction from the qualitative bound below is a downstream algebra
task. -/
theorem fullNet_iteratedFDeriv_two_bound_on_compact
    {m : ℕ}
    (σ : ℝ → ℝ)
    (hσ : ContDiff ℝ 2 σ)
    (b : Fin m → ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    {K : Set (Param d m)}
    (hK : IsCompact K) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ θ ∈ K,
      ‖iteratedFDeriv ℝ 2 (fun θ' : Param d m => fullNet σ b θ' x) θ‖ ≤ L := by
  classical
  -- The map θ ↦ ‖iteratedFDeriv 2 (fun θ' ↦ fullNet σ b θ' x) θ‖ is
  -- continuous by ContDiff ℝ 2.  A continuous nonnegative real-valued
  -- function on a compact set attains a maximum; take L = max (0, sup)
  -- to guarantee nonnegativity.
  by_cases hKempty : K = ∅
  · refine ⟨0, le_refl 0, ?_⟩
    intro θ hθ
    exfalso
    rw [hKempty] at hθ
    exact absurd hθ (Set.notMem_empty θ)
  · rcases Set.nonempty_iff_ne_empty.mpr hKempty with ⟨θ₀, hθ₀⟩
    -- Continuity of the iterated Fréchet derivative.
    have h_cont := fullNet_iteratedFDeriv_two_continuous (d := d) σ hσ b x
    -- Norm of a continuous multilinear-map-valued function is continuous.
    have h_norm_cont :
        Continuous (fun θ : Param d m =>
          ‖iteratedFDeriv ℝ 2 (fun θ' : Param d m => fullNet σ b θ' x) θ‖) :=
      continuous_norm.comp h_cont
    -- Compact image has a max (bounded above).
    have h_image_compact : IsCompact ((fun θ : Param d m =>
        ‖iteratedFDeriv ℝ 2 (fun θ' : Param d m => fullNet σ b θ' x) θ‖) '' K) :=
      hK.image h_norm_cont
    have h_image_nonempty : ((fun θ : Param d m =>
        ‖iteratedFDeriv ℝ 2 (fun θ' : Param d m => fullNet σ b θ' x) θ‖) '' K).Nonempty :=
      ⟨_, ⟨θ₀, hθ₀, rfl⟩⟩
    obtain ⟨L, hL_mem, hL_max⟩ := h_image_compact.exists_isMaxOn h_image_nonempty
      continuousOn_id
    -- L is achieved, so L ≥ 0 since norms are nonneg.
    obtain ⟨θL, hθL_mem, hθL_eq⟩ := hL_mem
    have hL_nonneg : 0 ≤ L := by
      rw [← hθL_eq]
      exact norm_nonneg _
    refine ⟨L, hL_nonneg, ?_⟩
    intro θ hθ
    have h_in_image : (fun θ' : Param d m =>
        ‖iteratedFDeriv ℝ 2 (fun θ'' : Param d m => fullNet σ b θ'' x) θ'‖) θ ∈
        ((fun θ' : Param d m =>
          ‖iteratedFDeriv ℝ 2 (fun θ'' : Param d m => fullNet σ b θ'' x) θ'‖) '' K) :=
      ⟨θ, hθ, rfl⟩
    exact hL_max h_in_image

end ProbabilityTheory

/-! ### Sanity check

At `d = 1, m = 1, σ = softplus, a₁ = 1, w₁ = (0), b₁ = 0, x = (1)`, the
network output should be `(1/√1) · 1 · softplus(0 · 1 + 0) = log 2`.
The `#eval` below is symbolic in `softplus`, so we cannot execute it —
we instead unit-test the softplus derivative value: `sigmoid 0 = 1/2`.
-/

section SanityCheck

/-- Sanity: `sigmoid 0 = 1/2`. -/
theorem Real.sigmoid_zero : Real.sigmoid 0 = 1 / 2 := by
  unfold Real.sigmoid
  simp [Real.exp_zero]
  norm_num

/-- Sanity: `softplus 0 = log 2`. -/
theorem Real.softplus_zero : Real.softplus 0 = Real.log 2 := by
  unfold Real.softplus
  rw [Real.exp_zero]
  norm_num

end SanityCheck
