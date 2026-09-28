/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.NTKLazyTrainingEndToEnd

/-!
# NTK lazy-training training-set-restricted residual bound

**T6b — training-set-restricted pointwise residual bound.**

The parametric end-to-end carrier
`ntk_lazy_training_carrier_parametric` establishes the Euclidean-norm
decay

  `‖r(T)‖² ≤ ‖r(0)‖² · exp(-(ρ T))`

of the residual `r(t) = f_{θ(t)}(x_i) - y_i` for `t = T ≥ 0`.  This
module records the immediate coordinate-projection corollary: for
each training index `i`,

  `|r(T) i| ≤ ‖r(0)‖ · exp(-(ρ T) / 2)`.

The proof is a two-step composition: the pointwise-≤-Euclidean-norm
inequality (from `EuclideanSpace.norm_sq_eq`) turns the squared bound
into `|r(T) i|² ≤ ‖r(0)‖² · exp(-(ρ T))`, and taking square roots
(using `Real.sqrt_sq`, `Real.sqrt_mul`, and `Real.exp_half`) yields
the pointwise conclusion.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator
open Matrix ProbabilityTheory

namespace LTFP

open Real

/-- **Training-set-restricted pointwise residual bound.**

Under the same hypotheses as `ntk_lazy_training_carrier_parametric`
(initial coercivity `ρ • 1 ≤ K(0)`, uniform drift `‖K(t) - K(0)‖ ≤ ρ/2`,
and the linear residual ODE `r'(t) = -(K(t) · r(t))`), for every
training index `i` and every `T ≥ 0` the pointwise residual decays at
half the exponential rate of the Euclidean-norm bound:

  `|r(T) i| ≤ ‖r(0)‖ · exp(-(ρ T) / 2)`.

This is an immediate coordinate projection: `|r(T) i|² ≤ ‖r(T)‖²` by
`EuclideanSpace.norm_sq_eq`, whence the norm-squared decay yields
`|r(T) i|² ≤ ‖r(0)‖² · exp(-(ρ T))`, and taking square roots gives the
claim via `Real.exp_half`. -/
theorem ntk_training_residual_pointwise_bound
    {d n m : ℕ}
    [Nonempty (Fin n)]
    (σ σ' : ℝ → ℝ)
    (b : Fin m → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (θ : ℝ → Param d m)
    (hK_herm : ∀ t,
      (fullTrainingKernel σ σ' b (θ t) xs).IsHermitian)
    {ρ : ℝ} (hρ_pos : 0 < ρ)
    (hK_init_coercive :
      (ρ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤
        fullTrainingKernel σ σ' b (θ 0) xs)
    (hK_drift_small : ∀ t : ℝ,
      ‖fullTrainingKernel σ σ' b (θ t) xs -
       fullTrainingKernel σ σ' b (θ 0) xs‖ ≤ ρ / 2)
    (r : ℝ → EuclideanSpace ℝ (Fin n))
    (hr_diff : Differentiable ℝ r)
    (hr_ODE : ∀ t,
      deriv r t = -(WithLp.toLp 2
        ((fullTrainingKernel σ σ' b (θ t) xs) *ᵥ WithLp.ofLp (r t))))
    (i : Fin n) (T : ℝ) (hT : 0 ≤ T) :
    |r T i| ≤ ‖r 0‖ * Real.exp (-(ρ * T) / 2) := by
  -- Step 1: Euclidean-norm-squared decay from the parametric carrier.
  have h_sq : ‖r T‖ ^ 2 ≤ ‖r 0‖ ^ 2 * Real.exp (-(ρ * T)) :=
    ntk_lazy_training_carrier_parametric σ σ' b xs θ hK_herm hρ_pos
      hK_init_coercive hK_drift_small r hr_diff hr_ODE T hT
  -- Step 2: coordinate projection — |r T i|² ≤ ‖r T‖².
  have h_coord_sq : |r T i| ^ 2 ≤ ‖r T‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have h_mem : i ∈ (Finset.univ : Finset (Fin n)) := Finset.mem_univ i
    have h_nn : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ ‖r T j‖ ^ 2 :=
      fun j _ => sq_nonneg _
    have h_le := Finset.single_le_sum (f := fun j => ‖r T j‖ ^ 2) h_nn h_mem
    -- `‖r T i‖ = |r T i|` for a real coordinate.
    simpa [Real.norm_eq_abs, sq_abs] using h_le
  -- Step 3: chain the two bounds.
  have h_chain : |r T i| ^ 2 ≤ ‖r 0‖ ^ 2 * Real.exp (-(ρ * T)) :=
    le_trans h_coord_sq h_sq
  -- Step 4: take square roots on both sides.  Both sides are non-negative.
  have h_abs_nn : 0 ≤ |r T i| := abs_nonneg _
  have h_norm_nn : 0 ≤ ‖r 0‖ := norm_nonneg _
  have h_exp_nn : 0 ≤ Real.exp (-(ρ * T)) := (Real.exp_pos _).le
  have h_rhs_nn : 0 ≤ ‖r 0‖ ^ 2 * Real.exp (-(ρ * T)) :=
    mul_nonneg (sq_nonneg _) h_exp_nn
  -- Apply `Real.sqrt` monotonicity.
  have h_sqrt : Real.sqrt (|r T i| ^ 2) ≤
      Real.sqrt (‖r 0‖ ^ 2 * Real.exp (-(ρ * T))) :=
    Real.sqrt_le_sqrt h_chain
  -- Simplify the two sides.
  have h_lhs_eq : Real.sqrt (|r T i| ^ 2) = |r T i| :=
    Real.sqrt_sq h_abs_nn
  have h_rhs_eq :
      Real.sqrt (‖r 0‖ ^ 2 * Real.exp (-(ρ * T))) =
        ‖r 0‖ * Real.exp (-(ρ * T) / 2) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq h_norm_nn]
    congr 1
    -- `sqrt (exp x) = exp (x / 2)` from `Real.exp_half`.
    have := Real.exp_half (-(ρ * T))
    linarith [this]
  rw [h_lhs_eq, h_rhs_eq] at h_sqrt
  exact h_sqrt

#print axioms ntk_training_residual_pointwise_bound

end LTFP
