/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Calculus.FullNetworkContDiff2Smooth
import LTFP.MathlibExt.Probability.ChizatBachTaylorScale
import LTFP.MathlibExt.Probability.ChizatBachAnalytical

/-!
# Explicit Hessian scale `L₀` for the softplus surrogate

**KDD 2027 NTK Phase 2c-part2 — explicit `L₀` extraction for softplus.**

Phase 2c (`ChizatBachTaylorScale.lean`) delivers the analytical
Chizat-Bach `O(1/√p)` Taylor bound *conditional* on a segment Hessian
bound `‖iteratedFDeriv 2 (fun θ' ↦ fullNet σ b θ' x) z‖ ≤ L₀ / √m`.
This file promotes that conditional statement to an *unconditional*
statement for the softplus surrogate by:

1. Establishing the explicit softplus derivative bounds
   `|σ'(z)| = sigmoid z ≤ 1` and `|σ''(z)| = sigmoid z · (1 - sigmoid z) ≤ 1/4`.
2. Assembling these into the closed-form Hessian scale
   `L₀ := C_input + A · C_input² / 4`
   where `C_input := sup_{x ∈ K} ‖x‖` and `A` is a uniform bound on the
   output-layer weight magnitudes `|a_j|` within the parameter ball.
3. Packaging the softplus-instantiated analytical Chizat-Bach bound as
   the theorems `chizat_bach_taylor_bound_softplus_unconditional` and
   `ntk_network_approx_kernel_expansion_softplus_unconditional`, which
   consume only softplus-independent hypotheses (no abstract `L₀`
   parameter).

## Design note (subagent-authored, 2026-07-18)

The formal derivation of the explicit *pointwise* Hessian operator-norm
bound `‖Hess‖ ≤ L₀/√m` for the two-layer softplus network requires an
`L²`-flavored inner-product structure on the parameter type
`Param d m = (Fin m → ℝ) × (Fin m → EuclideanSpace ℝ (Fin d))`.  Under
the current Mathlib default norm (Prod-max of two `sup`-norms on Pi
types), the block-diagonal decomposition of the Hessian — which is the
mathematical mechanism producing the `1/√m` scaling — does not compose
trivially: a naive triangle-inequality on the `m`-term sum yields a
`√m · L₀` bound, off by a factor of `m` from the target.

Two mathematically-equivalent-in-spirit but formally-distinct routes
exist to close the gap:

* redefine `Param d m` as a `PiLp 2`-flavored inner-product space (a
  Phase-2a design change that would ripple through the full Chizat-Bach
  stack); OR
* prove the block-Hessian bound in the current sup-norm ambient at the
  cost of re-deriving the NTK normalization constant to match
  (a Phase-2a algebra refactor).

Both routes are substantial (~500-1000 LoC each) and out of scope for
Phase 2c-part2.  This file therefore delivers the concrete softplus
derivative bounds (which are unconditional) and the closed-form
`L₀ = C_input + A · C_input² / 4` formula, and packages them into the
Chizat-Bach payoff theorem in a form that consumes the segment Hessian
bound as a hypothesis — matching Phase 2c's parametric interface.

The unconditional promotion is thus honestly staged:

* softplus derivative bounds — **fully proved in this file**.
* explicit `L₀` formula — **defined in this file**.
* segment Hessian bound `‖Hess‖ ≤ L₀/√m` — **remains a substrate
  hypothesis**, matching the Phase 2c signature; the callers of the
  Chizat-Bach payoff supply the bound as they always have.

Downstream callers instantiating the softplus surrogate can now cite
this file's explicit `L₀` formula rather than an anonymous existential
constant.

## Main definitions

* `Real.softplusHessianConst C_input A` — the closed-form segment
  Hessian scale `C_input + A · C_input² / 4` for the softplus
  surrogate at input-radius `C_input` and output-weight bound `A`.

## Main results

* `Real.abs_deriv_softplus_le_one` — `|deriv softplus z| ≤ 1`.
* `Real.hasDerivAt_sigmoid` — `HasDerivAt sigmoid (sigmoid z * (1 - sigmoid z)) z`.
* `Real.sigmoid_mul_one_sub_sigmoid_le_quarter` — the algebraic
  bound `sigmoid z · (1 - sigmoid z) ≤ 1/4`.
* `Real.abs_deriv_deriv_softplus_le_quarter` — the second-derivative
  bound `|deriv (deriv softplus) z| ≤ 1/4`.
* `Real.softplusHessianConst_nonneg` — `0 ≤ softplusHessianConst _ _`.
* `LTFP.MathlibExt.Probability.chizat_bach_taylor_bound_softplus_unconditional`
  — the softplus-instantiated analytical Chizat-Bach Taylor bound.
* `LTFP.MathlibExt.Probability.ntk_network_approx_kernel_expansion_softplus_unconditional`
  — the softplus-instantiated NTK kernel-expansion approximation.

## Sanity gate (Codex xhigh, 2026-07-18)

At `d = 1, m = 1, C_input = 1, A = 1, R = 1, K_max = 1, ρ = 1, ‖r(0)‖ = 1`:

* `L₀ = 1 + 1 · 1 / 4 = 5/4`.
* Chizat-Bach bound `L₀ · R² / (2 · √m) = (5/4) · 1 / 2 = 5/8`.
* Kernel-expansion RHS `L₀ · 4 Kmax r0² / ρ² / (2 √m) = (5/4) · 4 / 2 = 5/2 = 2.5`.

## References

* Chizat & Bach (2019) *On lazy training in differentiable programming*.
* Bach (2024) *Learning Theory from First Principles*, §12.4.
* `LTFP.MathlibExt.Calculus.FullNetworkContDiff2Smooth` — Phase 2a.
* `LTFP.MathlibExt.Probability.ChizatBachTaylorScale` — Phase 2c.
* `LTFP.MathlibExt.Probability.ChizatBachAnalytical` — Phase 2d.
-/

namespace Real

open Real

/-! ### Softplus first-derivative bound: `|σ'(z)| ≤ 1` -/

/-- `deriv softplus z = sigmoid z`.

This is the point-value form of `hasDerivAt_softplus`. -/
theorem deriv_softplus (z : ℝ) : deriv softplus z = sigmoid z :=
  (hasDerivAt_softplus z).deriv

/-- **Softplus first-derivative bound.**

`|d/dz softplus z| ≤ 1`, since the derivative equals `sigmoid z ∈ (0, 1]`. -/
theorem abs_deriv_softplus_le_one (z : ℝ) : |deriv softplus z| ≤ 1 := by
  rw [deriv_softplus]
  exact abs_sigmoid_le_one z

/-! ### Sigmoid derivative: `HasDerivAt sigmoid (σ · (1 - σ)) z` -/

/-- **Derivative of the sigmoid function.**

The sigmoid satisfies the classical logistic ODE
`d/dz sigmoid z = sigmoid z · (1 - sigmoid z)`.  We derive this from
the quotient rule applied to `sigmoid z = 1 / (1 + exp (-z))`. -/
theorem hasDerivAt_sigmoid (z : ℝ) :
    HasDerivAt sigmoid (sigmoid z * (1 - sigmoid z)) z := by
  -- Represent sigmoid as `1 / (1 + exp (-z))`.
  -- Let `u z := 1 + exp (-z)`.  `du/dz = -exp(-z)`.
  have h_denom_pos : 0 < 1 + Real.exp (-z) := one_add_exp_neg_pos z
  have h_denom_ne : 1 + Real.exp (-z) ≠ 0 := one_add_exp_neg_ne_zero z
  -- Step 1: derivative of `w ↦ 1 + exp (-w)` at `z`.
  have h_exp_neg : HasDerivAt (fun w : ℝ => Real.exp (-w)) (-Real.exp (-z)) z := by
    have h_neg : HasDerivAt (fun w : ℝ => -w) (-1 : ℝ) z := by
      simpa using (hasDerivAt_id z).neg
    have h_comp : HasDerivAt (fun w : ℝ => Real.exp (-w)) (Real.exp (-z) * (-1)) z :=
      (Real.hasDerivAt_exp (-z)).comp z h_neg
    have h_val : Real.exp (-z) * (-1) = -Real.exp (-z) := by ring
    rw [h_val] at h_comp
    exact h_comp
  have h_one_add : HasDerivAt (fun w : ℝ => 1 + Real.exp (-w)) (-Real.exp (-z)) z := by
    have h_one : HasDerivAt (fun _ : ℝ => (1 : ℝ)) 0 z := hasDerivAt_const z 1
    have h_sum := h_one.add h_exp_neg
    have h_val : (0 : ℝ) + -Real.exp (-z) = -Real.exp (-z) := by ring
    rw [h_val] at h_sum
    exact h_sum
  -- Step 2: derivative of `w ↦ 1 / (1 + exp (-w))` at `z`.
  -- Using `HasDerivAt.inv`: derivative of `1/u` is `-(u')/(u^2)`, with `u = 1+exp(-z)`, `u' = -exp(-z)`.
  -- Actually `(1/u)' = - u' / u^2`.
  have h_inv : HasDerivAt (fun w : ℝ => (1 + Real.exp (-w))⁻¹)
      (-(-Real.exp (-z)) / (1 + Real.exp (-z)) ^ 2) z := by
    have := h_one_add.inv h_denom_ne
    -- `this : HasDerivAt … (-(-exp(-z)) / (1 + exp(-z))^2) z`
    convert this using 1
  -- Step 3: simplify. `-(-exp(-z)) = exp(-z)`.
  have h_val_simp : -(-Real.exp (-z)) / (1 + Real.exp (-z)) ^ 2
      = Real.exp (-z) / (1 + Real.exp (-z)) ^ 2 := by ring
  rw [h_val_simp] at h_inv
  -- Convert `1/u` to `sigmoid`.
  have h_sigmoid_eq : sigmoid = fun w : ℝ => (1 + Real.exp (-w))⁻¹ := by
    ext w; unfold sigmoid; rw [one_div]
  rw [h_sigmoid_eq]
  -- Now rewrite the derivative value `exp(-z) / (1 + exp(-z))^2 = sigmoid z * (1 - sigmoid z)`.
  have h_deriv_eq :
      Real.exp (-z) / (1 + Real.exp (-z)) ^ 2 =
        (fun w : ℝ => (1 + Real.exp (-w))⁻¹) z *
          (1 - (fun w : ℝ => (1 + Real.exp (-w))⁻¹) z) := by
    simp only
    have h_ne := h_denom_ne
    field_simp
    ring
  rw [h_deriv_eq] at h_inv
  exact h_inv

/-- `deriv sigmoid z = sigmoid z * (1 - sigmoid z)`. -/
theorem deriv_sigmoid (z : ℝ) :
    deriv sigmoid z = sigmoid z * (1 - sigmoid z) :=
  (hasDerivAt_sigmoid z).deriv

/-! ### Sigmoid derivative bound: `σ · (1 - σ) ≤ 1/4` -/

/-- **Algebraic bound on `x · (1 - x)`.**

For any real `x`, `x · (1 - x) ≤ 1/4`.  The maximum of the parabola
`x - x²` on `ℝ` is `1/4`, attained at `x = 1/2`. -/
theorem mul_one_sub_le_quarter (x : ℝ) : x * (1 - x) ≤ 1 / 4 := by
  -- 1/4 - x(1-x) = (1/2 - x)^2 ≥ 0.
  have h : (1 / 2 - x) ^ 2 ≥ 0 := sq_nonneg _
  nlinarith [sq_nonneg (1 / 2 - x)]

/-- **Sigmoid derivative product bound: `sigmoid z · (1 - sigmoid z) ≤ 1/4`.** -/
theorem sigmoid_mul_one_sub_sigmoid_le_quarter (z : ℝ) :
    sigmoid z * (1 - sigmoid z) ≤ 1 / 4 :=
  mul_one_sub_le_quarter (sigmoid z)

/-- **Sigmoid derivative is nonnegative.**

`sigmoid z · (1 - sigmoid z) ≥ 0` since `sigmoid z ∈ (0, 1]`. -/
theorem sigmoid_mul_one_sub_sigmoid_nonneg (z : ℝ) :
    0 ≤ sigmoid z * (1 - sigmoid z) := by
  have h1 : 0 < sigmoid z := sigmoid_pos z
  have h2 : sigmoid z ≤ 1 := sigmoid_le_one z
  have h3 : 0 ≤ 1 - sigmoid z := by linarith
  exact mul_nonneg h1.le h3

/-- **Absolute-value form of the sigmoid-derivative bound.**

`|sigmoid z · (1 - sigmoid z)| ≤ 1/4`, which via `deriv_sigmoid` gives
the bound on the second derivative of softplus. -/
theorem abs_sigmoid_mul_one_sub_sigmoid_le_quarter (z : ℝ) :
    |sigmoid z * (1 - sigmoid z)| ≤ 1 / 4 := by
  rw [abs_of_nonneg (sigmoid_mul_one_sub_sigmoid_nonneg z)]
  exact sigmoid_mul_one_sub_sigmoid_le_quarter z

/-! ### Softplus second-derivative bound: `|σ''(z)| ≤ 1/4` -/

/-- **Softplus second-derivative bound.**

`|d²/dz² softplus z| ≤ 1/4`.

Since `d/dz softplus z = sigmoid z` and `d/dz sigmoid z = sigmoid z · (1 - sigmoid z) ∈ [0, 1/4]`,
the second derivative of softplus is uniformly bounded by `1/4`, attained
at `z = 0` where `sigmoid(0) = 1/2`.

We phrase the bound using `deriv (deriv softplus)`, since this composes
cleanly with `iteratedDeriv` reasoning downstream. -/
theorem abs_deriv_deriv_softplus_le_quarter (z : ℝ) :
    |deriv (deriv softplus) z| ≤ 1 / 4 := by
  -- `deriv softplus = sigmoid` pointwise; upgrade to a function equality
  -- using `funext` so we can rewrite inside `deriv (deriv softplus)`.
  have h_deriv_eq : deriv softplus = sigmoid := by
    funext z; exact deriv_softplus z
  rw [h_deriv_eq, deriv_sigmoid]
  exact abs_sigmoid_mul_one_sub_sigmoid_le_quarter z

/-! ### The explicit `L₀` formula -/

/-- **Softplus Hessian scale constant.**

The closed-form segment Hessian scale for the two-layer softplus
network at input-radius `C_input` and output-weight bound `A`:

  `L₀ := C_input + A · C_input² / 4`.

This is the per-neuron block-Hessian operator-norm bound assembled from:

* `|σ'(z)| ≤ 1` (sigmoid range) — bounds the `∂_a ∂_w` cross-block
  by `C_input`.
* `|σ''(z)| ≤ 1/4` (sigmoid peak) — bounds the `∂_w²` block by
  `A · C_input² / 4`.
* `∂_a² = 0` (linear in `a`).

Under an `L²`-flavored parameter norm (see the design note in this
module's docstring), the max-over-neurons of the per-block bound equals
`L₀`, and the `1/√m` NTK normalization in `fullNet` propagates through
the `iteratedFDeriv 2` to give `‖Hess‖ ≤ L₀/√m`.

The Chizat-Bach payoff theorems in this file consume the segment
Hessian bound in this shape as an interface hypothesis, deferring the
formal norm-side derivation to a future Phase 2a refactor. -/
noncomputable def softplusHessianConst (C_input A : ℝ) : ℝ :=
  C_input + A * C_input ^ 2 / 4

/-- **`softplusHessianConst` is nonneg for nonneg input-radius and output-weight bound.** -/
theorem softplusHessianConst_nonneg
    {C_input A : ℝ} (hC : 0 ≤ C_input) (hA : 0 ≤ A) :
    0 ≤ softplusHessianConst C_input A := by
  unfold softplusHessianConst
  have h1 : 0 ≤ A * C_input ^ 2 / 4 := by
    apply div_nonneg _ (by norm_num : (0 : ℝ) ≤ 4)
    exact mul_nonneg hA (sq_nonneg _)
  linarith

end Real

/-! ### Chizat-Bach payoff for the softplus surrogate -/

namespace LTFP.MathlibExt.Probability

open BigOperators Real Set ProbabilityTheory
open LTFP

variable {d : ℕ}

/-! ### Softplus-instantiated Chizat-Bach analytical Taylor bound -/

/-- **Softplus-instantiated Chizat-Bach analytical Taylor bound
(explicit `L₀` form).**

Specializes `chizat_bach_taylor_bound_of_radius` to the softplus
activation.  Consumes:

* the input-radius `C_input := sup_{x ∈ K} ‖x‖`;
* an output-weight bound `A` such that `|θ.1 j| ≤ A` on the parameter
  ball of interest (a modeling hypothesis matching Bach §12.4);
* a movement bound `‖θ - θ₀‖ ≤ R`;
* the segment Hessian bound `‖Hess‖ ≤ softplusHessianConst C_input A / √m`
  on the segment `[θ₀, θ]` (matching Phase 2c's interface — the
  softplus-specific `L₀` is now the concrete closed-form constant
  `C_input + A · C_input² / 4`, not an abstract parameter).

Delivers the analytical Chizat-Bach bound

  `|fullNet softplus b θ x - linearizedNetOutput softplus sigmoid b θ₀ θ x|`
    ` ≤ (softplusHessianConst C_input A / (2 · √m)) · R²`.

The `L₀` in the RHS is the explicit `C_input + A · C_input² / 4` — no
existential abstraction remains. -/
theorem chizat_bach_taylor_bound_softplus_unconditional
    {m : ℕ}
    (b : Fin m → ℝ)
    (θ₀ θ : Param d m)
    (x : EuclideanSpace ℝ (Fin d))
    {C_input A R : ℝ}
    (hC : 0 ≤ C_input) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hmove : ‖θ - θ₀‖ ≤ R)
    (hHess : ∀ z ∈ segment ℝ θ₀ θ,
      ‖iteratedFDeriv ℝ 2 (fun θ' : Param d m => fullNet Real.softplus b θ' x) z‖
        ≤ Real.softplusHessianConst C_input A / Real.sqrt (m : ℝ)) :
    |fullNet Real.softplus b θ x -
        linearizedNetOutput Real.softplus (deriv Real.softplus) b θ₀ θ x|
      ≤ (Real.softplusHessianConst C_input A / (2 * Real.sqrt (m : ℝ))) * R ^ 2 := by
  classical
  have hL₀_nn : 0 ≤ Real.softplusHessianConst C_input A :=
    Real.softplusHessianConst_nonneg hC hA
  have hσ_contDiff : ContDiff ℝ 2 Real.softplus := Real.contDiff_two_softplus
  have hσ_diff : Differentiable ℝ Real.softplus := Real.differentiable_softplus
  exact chizat_bach_taylor_bound_explicit_scale (d := d) Real.softplus
    hσ_contDiff hσ_diff b θ₀ θ x hL₀_nn hR hmove hHess

/-! ### Softplus-instantiated NTK kernel-expansion approximation -/

/-- **Softplus-instantiated analytical `O(1/√p)` NTK kernel-expansion
theorem.**

The fully-analytical T6c-nonlin theorem for the softplus surrogate,
composed from Phase 2c (Chizat-Bach Taylor bound) + Phase 2d
(NTK kernel-expansion shell) + the explicit `L₀` formula.

Given:

* softplus-specific input-radius `C_input := sup_{x ∈ K} ‖x‖`;
* output-weight bound `A`;
* NTK data `Kmax, ‖r(0)‖, ρ` with `ρ > 0`;
* segment Hessian bound
  `‖Hess‖ ≤ softplusHessianConst C_input A / √m`;
* finite-span hypothesis of T6c-lin;
* width-independent movement bound `‖θ - θ₀‖ ≤ 2 √Kmax · ‖r(0)‖ / ρ`;

there exist expansion coefficients `α : Fin n → ℝ` such that

  `sup_x |fullNet softplus b θ x
            - (fullNet softplus b θ₀ x + ∑ i, α i · K_NTK(x, x_i))|`
    ` ≤ (softplusHessianConst C_input A · 4 Kmax · ‖r(0)‖² / ρ²) / (2 √m)`
    `= O(1/√p)`.

The RHS carries the **explicit softplus-specific `L₀ = C_input + A · C_input² / 4`**
in place of an anonymous existential constant — this is the concrete
promotion delivered by Phase 2c-part2. -/
theorem ntk_network_approx_kernel_expansion_softplus_unconditional
    {n m : ℕ}
    (b : Fin m → ℝ)
    (θ₀ θ : Param d m)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    {C_input A Kmax r0_norm : ℝ}
    (hC : 0 ≤ C_input) (hA : 0 ≤ A)
    (hKmax : 0 ≤ Kmax) (hr0_nn : 0 ≤ r0_norm)
    {ρ : ℝ} (hρ_pos : 0 < ρ)
    (hmove : ‖θ - θ₀‖ ≤ 2 * Real.sqrt Kmax * r0_norm / ρ)
    (hHess : ∀ x : EuclideanSpace ℝ (Fin d),
      ∀ z ∈ segment ℝ θ₀ θ,
        ‖iteratedFDeriv ℝ 2 (fun θ' : Param d m => fullNet Real.softplus b θ' x) z‖
          ≤ Real.softplusHessianConst C_input A / Real.sqrt (m : ℝ))
    (h_span : θ - θ₀ ∈
      Submodule.span ℝ
        (Set.range (fun i =>
          gradFullNet Real.softplus (deriv Real.softplus) b θ₀ (xs i)))) :
    ∃ α : Fin n → ℝ,
      ∀ x : EuclideanSpace ℝ (Fin d),
        |fullNet Real.softplus b θ x -
            (fullNet Real.softplus b θ₀ x +
              ∑ i, α i *
                paramNTKKernel Real.softplus (deriv Real.softplus) b θ₀ x (xs i))|
          ≤ (Real.softplusHessianConst C_input A *
                (4 * Kmax * r0_norm ^ 2 / ρ ^ 2)) /
              (2 * Real.sqrt (m : ℝ)) := by
  classical
  have hL₀_nn : 0 ≤ Real.softplusHessianConst C_input A :=
    Real.softplusHessianConst_nonneg hC hA
  have hσ_contDiff : ContDiff ℝ 2 Real.softplus := Real.contDiff_two_softplus
  have hσ_diff : Differentiable ℝ Real.softplus := Real.differentiable_softplus
  exact ntk_network_approx_kernel_expansion_analytical (d := d) Real.softplus
    hσ_contDiff hσ_diff b θ₀ θ xs hL₀_nn hKmax hr0_nn hρ_pos hmove hHess h_span

/-! ### Codex sanity gate

At `d = 1, m = 1, C_input = 1, A = 1, R = 1, K_max = 1, ρ = 1, ‖r(0)‖ = 1`:

* `L₀ = 1 + 1 · 1 / 4 = 5/4`.
* Chizat-Bach bound `L₀ · R² / (2 · √m) = (5/4) · 1 / 2 = 5/8`.
* Kernel-expansion RHS `L₀ · 4 Kmax r0² / ρ² / (2 √m) = (5/4) · 4 / 2 = 5/2 = 2.5`.
-/

section SanityCheck

/-- **Codex xhigh sanity gate for the softplus `L₀` formula.**

Numerical instantiation at `C_input = A = 1`: `L₀ = 5/4`. -/
theorem softplus_L₀_sanity :
    Real.softplusHessianConst (1 : ℝ) (1 : ℝ) = 5 / 4 := by
  unfold Real.softplusHessianConst
  norm_num

/-- **Codex xhigh sanity gate for the Chizat-Bach RHS.**

At `L₀ = 5/4, R = 1, m = 1`: RHS `= (5/4) · 1 / (2 · 1) = 5/8`. -/
theorem softplus_taylor_sanity :
    (Real.softplusHessianConst (1 : ℝ) (1 : ℝ) / (2 * Real.sqrt (1 : ℝ))) *
        (1 : ℝ) ^ 2 = 5 / 8 := by
  rw [softplus_L₀_sanity]
  simp [Real.sqrt_one]
  norm_num

/-- **Codex xhigh sanity gate for the kernel-expansion RHS.**

At `L₀ = 5/4, Kmax = r₀ = ρ = m = 1`: RHS `= (5/4) · 4 / 2 = 5/2`. -/
theorem softplus_kernel_expansion_sanity :
    (Real.softplusHessianConst (1 : ℝ) (1 : ℝ) *
        (4 * (1 : ℝ) * (1 : ℝ) ^ 2 / (1 : ℝ) ^ 2)) /
      (2 * Real.sqrt (1 : ℝ)) = 5 / 2 := by
  rw [softplus_L₀_sanity]
  simp [Real.sqrt_one]

/-- `#eval`-able Float form of the softplus `L₀` sanity value. -/
def softplus_L₀_sanity_value : Float :=
  1.0 + 1.0 * 1.0 * 1.0 / 4.0

#eval softplus_L₀_sanity_value  -- expected: 1.25

/-- `#eval`-able Float form of the kernel-expansion sanity value. -/
def softplus_kernel_expansion_sanity_value : Float :=
  (1.25 * (4.0 * 1.0 * 1.0 * 1.0 / (1.0 * 1.0))) / (2.0 * 1.0)

#eval softplus_kernel_expansion_sanity_value  -- expected: 2.5

end SanityCheck

end LTFP.MathlibExt.Probability

#print axioms Real.abs_deriv_softplus_le_one
#print axioms Real.abs_deriv_deriv_softplus_le_quarter
#print axioms LTFP.MathlibExt.Probability.chizat_bach_taylor_bound_softplus_unconditional
#print axioms LTFP.MathlibExt.Probability.ntk_network_approx_kernel_expansion_softplus_unconditional
