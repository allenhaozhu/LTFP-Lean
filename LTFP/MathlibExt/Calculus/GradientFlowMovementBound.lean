/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Calculus.ParameterMovementBoundedDeriv
import LTFP.MathlibExt.Calculus.FunctionMovementAlongCurve

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

/-- **Function-movement bound along a gradient flow with bounded gradient.**
For a gradient flow `α` of `L` with `‖gradL‖ ≤ K` and an `L'`-Lipschitz
function `f`, we have `|f (α t) - f (α t₀)| ≤ L' · K · |t - t₀|`.

This is the natural composition of
`gradientFlow_movement_of_bounded_gradient` with
`function_movement_of_lipschitz_along_bounded_curve`, and is the
bridge step used in B8 N5 (lazy-training loss-tracking): the loss
value cannot change faster than `L' · K` per unit time along a
gradient flow whose gradient is globally bounded in norm by `K`. -/
theorem gradientFlow_function_movement_of_bounded_gradient
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : ℝ → E) (L : E → ℝ) (gradL : E → E)
    (K : NNReal)
    (hα : Differentiable ℝ α)
    (hODE : ∀ t : ℝ, deriv α t = -(gradL (α t)))
    (hbound : ∀ x : E, ‖gradL x‖₊ ≤ K)
    (f : E → ℝ) (L' : NNReal) (hf : LipschitzWith L' f)
    (t t₀ : ℝ) :
    |f (α t) - f (α t₀)| ≤ (L' : ℝ) * (K : ℝ) * |t - t₀| := by
  apply function_movement_of_lipschitz_along_bounded_curve α K hα ?_ f L' hf t t₀
  intro s
  have h := hODE s
  have hneg : ‖-(gradL (α s))‖₊ = ‖gradL (α s)‖₊ := nnnorm_neg _
  calc ‖deriv α s‖₊
      = ‖-(gradL (α s))‖₊ := by rw [h]
    _ = ‖gradL (α s)‖₊ := hneg
    _ ≤ K := hbound (α s)

/-- **Norm-of-iterate bound along a gradient flow with bounded gradient.**
For a gradient flow `α` of `L` with `‖gradL‖ ≤ K` everywhere, the norm
of the iterate cannot change by more than `K · |t - t₀|`:

`|‖α t‖ - ‖α t₀‖| ≤ K · |t - t₀|`.

This is a direct corollary of
`gradientFlow_function_movement_of_bounded_gradient` applied to the
1-Lipschitz function `‖·‖` (cf. `lipschitzWith_one_norm`), and is the
bridge step used to bound norm-drift of the iterate in B8 N5
(lazy-training / wide-network analysis). -/
theorem gradientFlow_norm_movement_of_bounded_gradient
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : ℝ → E) (L : E → ℝ) (gradL : E → E)
    (K : NNReal)
    (hα : Differentiable ℝ α)
    (hODE : ∀ t : ℝ, deriv α t = -(gradL (α t)))
    (hbound : ∀ x : E, ‖gradL x‖₊ ≤ K)
    (t t₀ : ℝ) :
    |‖α t‖ - ‖α t₀‖| ≤ (K : ℝ) * |t - t₀| := by
  have hLip : LipschitzWith 1 (fun x : E => ‖x‖) := lipschitzWith_one_norm
  have h := gradientFlow_function_movement_of_bounded_gradient
    α L gradL K hα hODE hbound (fun x : E => ‖x‖) 1 hLip t t₀
  simpa using h

/-- **Gradient-flow constancy at identically-zero gradient.**
If a gradient flow `α` has gradient field `gradL` that vanishes
everywhere, then the trajectory is constant: `α t = α t₀` for all
`t, t₀ : ℝ`.

This is a trivial corollary of `gradientFlow_movement_of_bounded_gradient`
with `K = 0`: the movement bound `‖α t - α t₀‖ ≤ 0 · |t - t₀| = 0`
forces `α t = α t₀`. The hypothesis `gradL x = 0` for every `x : E`
captures the qualitative statement that the loss landscape has no
gradient signal anywhere, so the flow does not move. -/
theorem gradientFlow_const_of_zero_gradient
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (α : ℝ → E) (gradL : E → E)
    (hα : Differentiable ℝ α)
    (hODE : ∀ t : ℝ, deriv α t = -(gradL (α t)))
    (hzero : ∀ x : E, gradL x = 0)
    (t t₀ : ℝ) :
    α t = α t₀ := by
  have hbound : ∀ x : E, ‖gradL x‖₊ ≤ (0 : NNReal) := by
    intro x
    simp [hzero x]
  have h := gradientFlow_movement_of_bounded_gradient
    α gradL 0 hα hODE hbound t t₀
  -- `h : ‖α t - α t₀‖ ≤ (0 : ℝ) * |t - t₀|`
  rw [← sub_eq_zero, ← norm_eq_zero]
  exact le_antisymm (by simpa using h) (norm_nonneg _)

/-- **Good-event gradient-flow movement bound.**
For a parameter family `θ : Ω → ℝ → E` of gradient flows indexed by `ω : Ω`,
each with its own gradient field `gradL ω : E → E`, if on a "good event"
`Good ω` the gradient field is globally bounded by `K`, then on that event
the trajectory enjoys the per-ω movement bound

`‖θ ω t - θ ω t₀‖ ≤ K · |t - t₀|`.

This is a tiny quantifier-discharge adapter over
`gradientFlow_movement_of_bounded_gradient`: fix `ω`, then apply the
per-ω lemma. The wrapper is the natural shape consumed in B8 N5
(lazy-training / wide-network analysis), where the gradient bound holds
only on a high-probability "good event" determined by the random
initialization. Keeping `Good : Ω → Prop` plain — rather than coupling
to a measurable structure on `Ω` — keeps the adapter usable from any
probabilistic setting (Probability Mass, AE-event, finite ensemble)
without forcing measure-theoretic machinery into the analytic step. -/
theorem gradientFlow_movement_on_good_event
    {Ω : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Good : Ω → Prop)
    (θ : Ω → ℝ → E) (gradL : Ω → E → E)
    (K : NNReal)
    (hθ : ∀ ω, Differentiable ℝ (θ ω))
    (hODE : ∀ ω t, deriv (θ ω) t = -(gradL ω (θ ω t)))
    (hbound : ∀ ω, Good ω → ∀ z, ‖gradL ω z‖₊ ≤ K)
    (t t₀ : ℝ) :
    ∀ ω, Good ω → ‖θ ω t - θ ω t₀‖ ≤ (K : ℝ) * |t - t₀| := by
  intro ω hGood
  exact gradientFlow_movement_of_bounded_gradient
    (θ ω) (gradL ω) K (hθ ω) (hODE ω) (hbound ω hGood) t t₀

/-- **Width-scaled gradient-flow movement bound on a good event.**
A trivial composition adapter over `gradientFlow_movement_on_good_event`:
if, additionally, the global gradient-norm bound `K` and the time horizon
`T` jointly satisfy the *lazy radius* inequality
`K · |T| ≤ A / √m` (e.g. with `A = O(1)` and width `m`), then the
trajectory's movement is uniformly bounded by the lazy radius:

`‖θ ω T - θ ω 0‖ ≤ A / √m`.

This is the natural carrier shape consumed by the lazy-training /
NTK-concentration pipeline (B8 N5 and the wide-network linearization
arguments) when discharging the parametric `hmove` hypothesis: the
"width-scaled" form factors out the explicit `K · |T|` quantity that
needs to be bounded experiment-by-experiment, and replaces it with the
single dimensionless lazy-radius constant `A / √m` that downstream
linearization lemmas can consume directly. The width `m` is positive
by hypothesis to keep `√m` away from zero. -/
theorem gradientFlow_movement_on_good_event_le_lazy_radius
    {Ω E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Good : Ω → Prop}
    {θ : Ω → ℝ → E} {gradL : Ω → E → E}
    {K : NNReal} {m : ℕ} (_hm : 0 < m) {A : ℝ}
    (hθ : ∀ ω, Differentiable ℝ (θ ω))
    (hODE : ∀ ω t, deriv (θ ω) t = -(gradL ω (θ ω t)))
    (hbound : ∀ ω, Good ω → ∀ z, ‖gradL ω z‖₊ ≤ K)
    {T : ℝ}
    (hrad : (K : ℝ) * |T| ≤ A / Real.sqrt (m : ℝ)) :
    ∀ ω, Good ω →
      ‖θ ω T - θ ω 0‖ ≤ A / Real.sqrt (m : ℝ) := by
  intro ω hGood
  have hmove : ‖θ ω T - θ ω 0‖ ≤ (K : ℝ) * |T - 0| :=
    gradientFlow_movement_on_good_event
      Good θ gradL K hθ hODE hbound T 0 ω hGood
  have hT : |T - 0| = |T| := by rw [sub_zero]
  rw [hT] at hmove
  exact hmove.trans hrad

end LTFP.MathlibExt.Calculus
