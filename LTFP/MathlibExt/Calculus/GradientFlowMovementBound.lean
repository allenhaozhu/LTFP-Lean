/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Calculus.ParameterMovementBoundedDeriv

/-!
# Gradient-flow movement bound from a globally bounded gradient

A curve `α : ℝ → E` in a normed space that satisfies the gradient-flow
ODE `α'(t) = -(∇L)(α(t))` and whose gradient field `∇L` is globally
bounded by `K` in norm enjoys the same straight-line movement bound as
any curve with a bounded trajectory derivative:

`‖α t - α t₀‖ ≤ K · |t - t₀|`.

This packages the composition of the gradient-flow ODE with the
parameter-movement bound `parameter_movement_of_bounded_deriv_norm_form`
and is the natural carrier for the parameter-movement step of B8 N5
(lazy training / wide-network analysis), where the relevant quantity is
the supremum of `‖∇L(x)‖` along the trajectory.

The hypothesis `hbound` is stated globally on `E` rather than along the
trajectory because in the lazy-training setting the natural bound is a
global Lipschitz bound on `L` (equivalently, a global supremum bound on
`∇L`); restricting to the trajectory is a strict weakening and can be
recovered as a corollary.
-/

namespace LTFP.MathlibExt.Calculus

/-- **Gradient-flow movement bound (global gradient-norm form).**
If `α : ℝ → E` is differentiable and satisfies the gradient-flow ODE
`α'(t) = -(gradL)(α(t))` for some gradient field `gradL : E → E` with
`‖gradL x‖₊ ≤ K` for every `x : E`, then the trajectory moves at most
`K` units of distance per unit of time:

`‖α t - α t₀‖ ≤ K · |t - t₀|`.

This is the natural continuous-time analogue of the discrete fact that
each gradient-descent step moves the iterate by at most `η · K` when
`‖∇L‖ ≤ K`, and is the step used in lazy-training analyses to control
the deviation of the iterate from its initialization. -/
theorem gradientFlow_movement_of_bounded_gradient
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : ℝ → E) (gradL : E → E) (K : NNReal)
    (hα : Differentiable ℝ α)
    (hODE : ∀ t : ℝ, deriv α t = -(gradL (α t)))
    (hbound : ∀ x : E, ‖gradL x‖₊ ≤ K)
    (t t₀ : ℝ) :
    ‖α t - α t₀‖ ≤ (K : ℝ) * |t - t₀| := by
  refine parameter_movement_of_bounded_deriv_norm_form α K hα ?_ t t₀
  intro s
  have h := hODE s
  have hneg : ‖-(gradL (α s))‖₊ = ‖gradL (α s)‖₊ := nnnorm_neg _
  calc ‖deriv α s‖₊
      = ‖-(gradL (α s))‖₊ := by rw [h]
    _ = ‖gradL (α s)‖₊ := hneg
    _ ≤ K := hbound (α s)

end LTFP.MathlibExt.Calculus
