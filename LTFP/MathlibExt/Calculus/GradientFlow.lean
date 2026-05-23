/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

-- Proposed Mathlib path: Mathlib/Analysis/Calculus/GradientFlow.lean.
-- Proposed namespace:    Analysis.Calculus.

/-!
# Gradient flow — discrete-time iteration on scalar functions

The continuous-time gradient flow `dx/dt = -∇f(x(t))` of a smooth function
`f` is the natural dynamical system whose equilibria are the critical
points of `f` and along whose trajectories `f` decreases monotonically.
In practice it is studied through its explicit Euler discretisation
`xₖ₊₁ = xₖ - η · ∇f(xₖ)`, which is the gradient descent method and which
is what is used in optimisation and learning theory.

This file formalises the **discrete-time** iteration on scalar functions
`f : ℝ → ℝ`, proves its basic fixed-point and contraction properties, and
provides a worked instance for the canonical quadratic `f y = y² / 2`.

## Status

The discrete iteration developed below acts as the formal anchor for
downstream optimisation results in LTFP-Lean. In addition, this file now
provides a **continuous-time gradient flow** layer built on top of
`Mathlib.Analysis.ODE.PicardLindelof` and `Mathlib.Analysis.ODE.Gronwall`:

* `IsGradientFlow f α` is the predicate
  `∀ t, HasDerivAt α (-(deriv f (α t))) t`, i.e. the curve `α` satisfies
  the gradient-flow ODE `α'(t) = -∇f(α(t))` everywhere.
* `exists_local_gradient_flow_of_contDiffAt_two` produces a local
  gradient-flow trajectory whenever `f : ℝ → ℝ` is `C²` at the initial
  point. This is a direct application of Mathlib's Picard–Lindelöf
  theorem to the vector field `-deriv f`.
* `gradient_flow_unique_of_lipschitz_deriv` proves global uniqueness of
  the gradient flow as soon as `deriv f` is `M`-Lipschitz (the usual
  `M`-smoothness hypothesis), via `ODE_solution_unique_univ`.
* `gradient_flow_at_critical` and `gradient_flow_constant_at_critical`
  record the elementary fact that a critical point of `f` is an
  equilibrium of the gradient flow.

The discrete-to-continuous error estimate (`gradIter` interpolant
converges to the gradient flow as the step size shrinks) and Lyapunov /
LaSalle-style convergence theorems remain pending, but the existence and
uniqueness layer is now closed.

## Main definitions

* `gradStep f η x` — one step `x ↦ x - η · f'(x)` of the discrete
  gradient-flow iteration.
* `gradIter f η n x` — the `n`-fold composition of `gradStep f η`,
  i.e. the trajectory of the discrete flow starting at `x`.

## Main results

* `gradStep_zero_step`              — a zero step size is the identity.
* `gradStep_at_critical`            — critical points (`f'(x) = 0`) are
  fixed by one step of the iteration.
* `gradIter_zero`, `gradIter_succ`  — the defining recursion of
  `gradIter`.
* `gradIter_fixed_at_critical`      — critical points are fixed by every
  iterate of the scheme.
* `gradStep_quadratic`              — on the scalar quadratic
  `f y = y² / 2`, one step is `x ↦ x - η · x`.
* `gradIter_quadratic_geometric`    — one step on the quadratic is the
  scalar contraction `x ↦ (1 - η) · x`.
* `gradIter_quadratic_geometric_n`  — the iterated geometric form
  `gradIter f η n x = (1 - η)^n · x` on the quadratic.
* `gradIter_zero_at_zero`           — `x = 0` is a fixed point of the
  iteration on any function with `f'(0) = 0` (in particular on the
  quadratic).
* `gradStep_descent_quadratic`      — on the quadratic, one step with
  `0 < η ≤ 1` does not increase the objective.
* `gradStep_strict_descent_quadratic_when_eta_small` — strict descent on
  the quadratic for `η ∈ (0, 2)` and `x ≠ 0`.

## References

* Y. Nesterov, *Lectures on Convex Optimization*, 2nd edition, Springer,
  2018, §2.1 (gradient method) and §2.2.4 (continuous-time limit).
* S. Bubeck, *Convex Optimization: Algorithms and Complexity*,
  Foundations and Trends in Machine Learning, Vol. 8, No. 3–4 (2015),
  §3.1 (gradient descent for smooth convex functions).
* F. Bach, *Learning Theory from First Principles*, MIT Press, 2024,
  §5.1 (gradient descent as the discretisation of gradient flow).

## Tags

gradient flow, gradient descent, optimization, dynamical system, Euler
discretisation, fixed point, descent lemma
-/

namespace LTFP.MathlibExt.Calculus

/-- One step of the discrete gradient-flow iteration on a scalar
function `f : ℝ → ℝ` with step size `η`:
`gradStep f η x = x - η · f'(x)`.

This is the explicit Euler discretisation of the continuous-time
gradient flow `dx/dt = -f'(x(t))`. -/
noncomputable def gradStep (f : ℝ → ℝ) (η x : ℝ) : ℝ :=
  x - η * deriv f x

/-- The `n`-fold gradient-flow iteration, defined by
`gradIter f η 0 x = x` and
`gradIter f η (n+1) x = gradStep f η (gradIter f η n x)`.

Operationally this is `(gradStep f η)^[n] x`, i.e. the trajectory of the
discrete flow starting at `x`. -/
noncomputable def gradIter (f : ℝ → ℝ) (η : ℝ) : ℕ → ℝ → ℝ
  | 0,     x => x
  | n + 1, x => gradStep f η (gradIter f η n x)

/-- With a zero step size the gradient-flow iteration is the identity:
`gradStep f 0 x = x`. -/
@[simp]
theorem gradStep_zero_step (f : ℝ → ℝ) (x : ℝ) :
    gradStep f 0 x = x := by
  unfold gradStep
  ring

/-- Critical points of `f` (where `f' = 0`) are fixed by one step of the
gradient-flow iteration: `gradStep f η x = x` whenever `deriv f x = 0`. -/
theorem gradStep_at_critical
    (f : ℝ → ℝ) (η x : ℝ) (hx : deriv f x = 0) :
    gradStep f η x = x := by
  unfold gradStep
  rw [hx]
  ring

/-- Base case of the recursion for `gradIter`: zero iterations is the
identity. -/
@[simp]
theorem gradIter_zero (f : ℝ → ℝ) (η x : ℝ) :
    gradIter f η 0 x = x := rfl

/-- Step case of the recursion for `gradIter`: `n + 1` iterations is
one `gradStep` applied to `n` iterations. -/
theorem gradIter_succ (f : ℝ → ℝ) (η : ℝ) (n : ℕ) (x : ℝ) :
    gradIter f η (n + 1) x = gradStep f η (gradIter f η n x) := rfl

/-- Critical points are fixed by every iterate of the discrete gradient
flow: if `deriv f x = 0`, then `gradIter f η n x = x` for all `n`.

This is the discrete analogue of the elementary ODE fact that critical
points are equilibria of the continuous gradient flow. -/
theorem gradIter_fixed_at_critical
    (f : ℝ → ℝ) (η x : ℝ) (hx : deriv f x = 0) :
    ∀ n : ℕ, gradIter f η n x = x := by
  intro n
  induction n with
  | zero => exact gradIter_zero f η x
  | succ k ih =>
      rw [gradIter_succ, ih]
      exact gradStep_at_critical f η x hx

/-- The derivative of the scalar quadratic `f y = y² / 2` is the
identity: `deriv (fun y => y² / 2) x = x`. -/
theorem deriv_half_sq (x : ℝ) :
    deriv (fun y : ℝ => y ^ 2 / 2) x = x := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x ^ (2 - 1)) x := by
    simpa using (hasDerivAt_pow 2 x)
  have h2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2)
      ((2 * x ^ (2 - 1)) / 2) x := h1.div_const 2
  have h3 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
    have hsimp : (2 * x ^ (2 - 1)) / 2 = x := by
      have : x ^ (2 - 1) = x := by norm_num
      rw [this]; ring
    rw [hsimp] at h2
    exact h2
  exact h3.deriv

/-- Concrete instance of `gradStep` on the scalar quadratic
`f y = y² / 2`: one step is `x ↦ x - η · x`. -/
theorem gradStep_quadratic (η x : ℝ) :
    gradStep (fun y : ℝ => y ^ 2 / 2) η x = x - η * x := by
  unfold gradStep
  rw [deriv_half_sq]

/-- One step of the gradient-flow iteration on `f y = y² / 2` is the
scalar contraction `x ↦ (1 - η) · x`. This exhibits the discrete
gradient flow on a quadratic as a geometric sequence with ratio
`1 - η`. -/
theorem gradIter_quadratic_geometric (η x : ℝ) :
    gradIter (fun y : ℝ => y ^ 2 / 2) η 1 x = (1 - η) * x := by
  rw [gradIter_succ, gradIter_zero, gradStep_quadratic]
  ring

/-- Iterated geometric form of the discrete gradient flow on the
quadratic `f y = y² / 2`: `gradIter f η n x = (1 - η)^n · x`.

This is the closed form of the linear recurrence `xₖ₊₁ = (1 - η) · xₖ`
and exhibits gradient descent on a one-dimensional quadratic as a pure
geometric sequence. In particular, for `|1 - η| < 1` (equivalently
`0 < η < 2`), the trajectory converges to the unique critical point
`x = 0` at a linear rate, which is the prototypical statement of linear
convergence of gradient descent under strong convexity. -/
theorem gradIter_quadratic_geometric_n (η x : ℝ) :
    ∀ n : ℕ, gradIter (fun y : ℝ => y ^ 2 / 2) η n x = (1 - η) ^ n * x := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
      rw [gradIter_succ, ih, gradStep_quadratic]
      ring

/-- The origin is a fixed point of every iterate of the gradient flow on
any function whose derivative vanishes at `0`. In particular this holds
for the scalar quadratic `f y = y² / 2`. -/
theorem gradIter_zero_at_zero
    (f : ℝ → ℝ) (η : ℝ) (hf : deriv f 0 = 0) :
    ∀ n : ℕ, gradIter f η n 0 = 0 :=
  gradIter_fixed_at_critical f η 0 hf

/-- Energy-decrease (descent) property of the discrete gradient flow on
the scalar quadratic `f y = y² / 2`. For step sizes `0 < η ≤ 1` we
have `f (gradStep f η x) ≤ f x`, i.e. one step of the iteration does
not increase the objective.

This is the discrete anchor of the continuous-time fact
`(d/dt) f(x(t)) = -‖∇f(x(t))‖² ≤ 0`. -/
theorem gradStep_descent_quadratic
    (η x : ℝ) (hη_pos : 0 < η) (hη_le : η ≤ 1) :
    (fun y : ℝ => y ^ 2 / 2) (gradStep (fun y : ℝ => y ^ 2 / 2) η x)
      ≤ (fun y : ℝ => y ^ 2 / 2) x := by
  -- Reduce to: `((1 - η) * x)^2 / 2 ≤ x^2 / 2`.
  rw [gradStep_quadratic]
  show (x - η * x) ^ 2 / 2 ≤ x ^ 2 / 2
  have h_factor : x - η * x = (1 - η) * x := by ring
  rw [h_factor]
  -- Key inequality: `(1 - η)^2 ≤ 1` for `0 < η ≤ 1`.
  have h1mη_nonneg : 0 ≤ 1 - η := by linarith
  have h1mη_le_one : 1 - η ≤ 1 := by linarith
  have h_sq_le : (1 - η) ^ 2 ≤ 1 := by
    have hbound : (1 - η) ^ 2 ≤ 1 ^ 2 :=
      pow_le_pow_left₀ h1mη_nonneg h1mη_le_one 2
    simpa using hbound
  have hx_sq_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
  have h_prod : (1 - η) ^ 2 * x ^ 2 ≤ 1 * x ^ 2 :=
    mul_le_mul_of_nonneg_right h_sq_le hx_sq_nonneg
  have h_expand : ((1 - η) * x) ^ 2 = (1 - η) ^ 2 * x ^ 2 := by ring
  rw [h_expand]
  have h_one : (1 : ℝ) * x ^ 2 = x ^ 2 := one_mul _
  rw [h_one] at h_prod
  linarith

/-- Strict descent of the discrete gradient flow on the scalar
quadratic `f y = y² / 2` for step sizes `η ∈ (0, 2)` and starting
points `x ≠ 0`. This is the sharpening of `gradStep_descent_quadratic`
that drives linear convergence: as long as the iterate has not reached
the minimiser, the objective strictly decreases.

The admissible range `(0, 2)` is the well-known *stability interval* of
gradient descent on a `1`-smooth, `1`-strongly-convex quadratic: outside
it the iteration diverges. -/
theorem gradStep_strict_descent_quadratic_when_eta_small
    (η x : ℝ) (hη_pos : 0 < η) (hη_lt : η < 2) (hx : x ≠ 0) :
    (fun y : ℝ => y ^ 2 / 2) (gradStep (fun y : ℝ => y ^ 2 / 2) η x)
      < (fun y : ℝ => y ^ 2 / 2) x := by
  rw [gradStep_quadratic]
  show (x - η * x) ^ 2 / 2 < x ^ 2 / 2
  have h_factor : x - η * x = (1 - η) * x := by ring
  rw [h_factor]
  -- Key inequality: `(1 - η)^2 < 1` for `η ∈ (0, 2)`.
  have h_sq_lt : (1 - η) ^ 2 < 1 := by
    have h_expand : (1 - η) ^ 2 = 1 - η * (2 - η) := by ring
    rw [h_expand]
    have h_factor_pos : 0 < η * (2 - η) := by
      have : 0 < 2 - η := by linarith
      exact mul_pos hη_pos this
    linarith
  have hx_sq_pos : 0 < x ^ 2 := by positivity
  have h_prod : (1 - η) ^ 2 * x ^ 2 < 1 * x ^ 2 := by
    have h_diff : 1 * x ^ 2 - (1 - η) ^ 2 * x ^ 2
        = (1 - (1 - η) ^ 2) * x ^ 2 := by ring
    have h_one_minus_sq_pos : 0 < 1 - (1 - η) ^ 2 := by linarith
    have h_pos : 0 < (1 - (1 - η) ^ 2) * x ^ 2 :=
      mul_pos h_one_minus_sq_pos hx_sq_pos
    linarith
  have h_expand : ((1 - η) * x) ^ 2 = (1 - η) ^ 2 * x ^ 2 := by ring
  rw [h_expand]
  linarith

/-! ## Continuous-time gradient flow

The continuous-time gradient flow `dx/dt = -∇f(x(t))` is the natural
object behind every discrete gradient-descent scheme. On the scalar
line, where `∇f = f'`, the flow is an autonomous ODE with right-hand
side `-deriv f`. The existence and uniqueness of trajectories follow
from Mathlib's Picard–Lindelöf and Grönwall infrastructure once the
right-hand side is suitably regular. -/

/-- The continuous-time gradient flow predicate. A curve `α : ℝ → ℝ`
is a *gradient flow* of `f : ℝ → ℝ` when it satisfies the ODE
`α'(t) = -f'(α(t))` everywhere on `ℝ`.

This is the natural dynamical system whose equilibria are the critical
points of `f` and along whose trajectories `f` decreases monotonically
(under mild smoothness of `f`). The discrete iteration `gradIter` above
is the explicit Euler discretisation of this flow. -/
def IsGradientFlow (f α : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, HasDerivAt α (-(deriv f) (α t)) t

/-- Critical points of `f` are equilibria of the gradient flow: if
`deriv f x = 0`, then the constant curve `α(t) = x` satisfies the
gradient-flow ODE. -/
theorem gradient_flow_constant_at_critical
    (f : ℝ → ℝ) (x : ℝ) (hx : deriv f x = 0) :
    IsGradientFlow f (fun _ : ℝ => x) := by
  intro t
  have h_deriv_const : HasDerivAt (fun _ : ℝ => x) 0 t := hasDerivAt_const t x
  -- Goal: `HasDerivAt (fun _ => x) (-(deriv f x)) t`.
  -- Since `deriv f x = 0`, the RHS is `0`, so this is `h_deriv_const`.
  have h_rhs : -(deriv f) x = 0 := by rw [hx]; ring
  rw [h_rhs]
  exact h_deriv_const

/-- Along any gradient flow, the value at a critical initial point stays
at that critical point. Combined with the global-uniqueness theorem
below, this gives the standard "critical points are fixed by the flow"
statement.

Here we only state the direct (constructive) form: the constant curve
*is* one valid gradient flow starting at a critical point. -/
theorem gradient_flow_at_critical
    (f : ℝ → ℝ) (x : ℝ) (hx : deriv f x = 0) :
    ∃ α : ℝ → ℝ, α 0 = x ∧ IsGradientFlow f α :=
  ⟨fun _ => x, rfl, gradient_flow_constant_at_critical f x hx⟩

/-- **Local existence of the gradient flow (Picard–Lindelöf).**
If `f : ℝ → ℝ` is globally `C²`, then `-deriv f` is globally `C¹`, hence
by Mathlib's Picard–Lindelöf theorem the autonomous ODE
`α'(t) = -f'(α(t))` admits a local solution with `α(t₀) = x₀` on an
open time interval `(t₀ - ε, t₀ + ε)`.

We require the global `C²` hypothesis on `f` to obtain a `C¹` field via
`ContDiff.deriv'`; the existence theorem itself only needs `C¹` of the
field at the initial point, but a global hypothesis on `f` is the
natural and clean way to package the smoothness in the gradient-flow
setting. -/
theorem exists_local_gradient_flow_of_contDiff_two
    (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (x₀ t₀ : ℝ) :
    ∃ α : ℝ → ℝ, α t₀ = x₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt α (-(deriv f) (α t)) t := by
  -- Vector field: `V x = -deriv f x`. It is `C¹` because `deriv f` is `C¹`.
  have h_deriv_C1 : ContDiff ℝ 1 (deriv f) := by
    have h2 : (2 : WithTop ℕ∞) = ((1 : ℕ) + 1 : ℕ) := by norm_num
    rw [h2] at hf
    exact hf.deriv'
  have hV_C1 : ContDiff ℝ 1 (fun x : ℝ => -(deriv f) x) :=
    h_deriv_C1.neg
  -- Localise to a `ContDiffAt`.
  have hV_at : ContDiffAt ℝ 1 (fun x : ℝ => -(deriv f) x) x₀ :=
    hV_C1.contDiffAt
  -- Apply Picard–Lindelöf for `C¹` time-independent vector fields.
  obtain ⟨α, hα0, ε, hε, hαderiv⟩ :=
    hV_at.exists_forall_mem_closedBall_exists_eq_forall_mem_Ioo_hasDerivAt₀ t₀
  exact ⟨α, hα0, ε, hε, hαderiv⟩

/-- **Global uniqueness of the gradient flow (Grönwall).**
If `deriv f` is `M`-Lipschitz on `ℝ` (the classical `M`-smoothness
hypothesis), then any two global solutions of the gradient-flow ODE
with the same initial value agree everywhere.

This is a direct application of Mathlib's `ODE_solution_unique_univ`
to the time-independent vector field `v t x = -(deriv f x)`, which
inherits the Lipschitz constant from `deriv f`. -/
theorem gradient_flow_unique_of_lipschitz_deriv
    (f : ℝ → ℝ) {M : NNReal} (hLip : LipschitzWith M (deriv f))
    {α β : ℝ → ℝ} (hα : IsGradientFlow f α) (hβ : IsGradientFlow f β)
    {t₀ : ℝ} (h_init : α t₀ = β t₀) :
    α = β := by
  -- Vector field: `v t x = -(deriv f x)`. Lipschitz in `x` with constant `M`.
  set v : ℝ → ℝ → ℝ := fun _ x => -(deriv f) x with hv_def
  have hv_lip : ∀ t : ℝ, LipschitzOnWith M (v t) Set.univ := by
    intro t
    have hneg : LipschitzWith M (fun x : ℝ => -(deriv f) x) := hLip.neg
    exact lipschitzOnWith_univ.mpr hneg
  refine ODE_solution_unique_univ (v := v) (s := fun _ => Set.univ)
    (t₀ := t₀) (K := M) hv_lip ?_ ?_ h_init
  · intro t
    refine ⟨?_, Set.mem_univ _⟩
    -- `α'(t) = -(deriv f) (α t) = v t (α t)`.
    simpa [v] using hα t
  · intro t
    refine ⟨?_, Set.mem_univ _⟩
    simpa [v] using hβ t

/-- **Energy identity along scalar gradient flow.**
If `α` solves `α' = -f' ∘ α` and `f` is differentiable at the current
state `α t`, then the objective value satisfies
`(f ∘ α)'(t) = -(f'(α t))²`.

This is the basic Lyapunov identity underlying continuous-time gradient
flow. Convexity is not needed for the identity itself; convexity enters
later when converting this dissipation identity into rates for the
optimality gap. -/
theorem gradient_flow_energy_hasDerivAt
    {f α : ℝ → ℝ} (hα : IsGradientFlow f α) {t : ℝ}
    (hf : DifferentiableAt ℝ f (α t)) :
    HasDerivAt (fun s : ℝ => f (α s)) (-(deriv f (α t)) ^ 2) t := by
  have hf' : HasDerivAt f (deriv f (α t)) (α t) := hf.hasDerivAt
  have hcomp := hf'.comp t (hα t)
  simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hcomp

/-- Smooth global version of `gradient_flow_energy_hasDerivAt`. -/
theorem gradient_flow_energy_hasDerivAt_of_differentiable
    {f α : ℝ → ℝ} (hα : IsGradientFlow f α) (hf : Differentiable ℝ f) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (α s)) (-(deriv f (α t)) ^ 2) t :=
  gradient_flow_energy_hasDerivAt hα (hf (α t))

/-- Along a scalar gradient flow, objective energy has nonpositive derivative. -/
theorem gradient_flow_energy_deriv_nonpos
    {f α : ℝ → ℝ} (hα : IsGradientFlow f α) {t : ℝ}
    (hf : DifferentiableAt ℝ f (α t)) :
    deriv (fun s : ℝ => f (α s)) t ≤ 0 := by
  have hderiv := (gradient_flow_energy_hasDerivAt hα hf).deriv
  rw [hderiv]
  exact neg_nonpos.mpr (sq_nonneg (deriv f (α t)))

/-- Smooth global version of `gradient_flow_energy_deriv_nonpos`. -/
theorem gradient_flow_energy_deriv_nonpos_of_differentiable
    {f α : ℝ → ℝ} (hα : IsGradientFlow f α) (hf : Differentiable ℝ f) (t : ℝ) :
    deriv (fun s : ℝ => f (α s)) t ≤ 0 :=
  gradient_flow_energy_deriv_nonpos hα (hf (α t))

/-- **Scalar convex first-order inequality.**
For a convex differentiable function `f : ℝ → ℝ`, the tangent line at any
point `y` lies below the graph: `f y + deriv f y · (x - y) ≤ f x`.

This is the load-bearing intermediate for the O(1/t) gradient-flow decay
theorem (the tangent-line lower bound at the current state lets us
control the optimality gap by the gradient norm). -/
theorem convex_first_order_inequality
    {f : ℝ → ℝ} (hconv : ConvexOn ℝ Set.univ f) (hf : Differentiable ℝ f)
    (x y : ℝ) :
    f y + deriv f y * (x - y) ≤ f x := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · -- Case `x < y`: slope at right endpoint `y` is bounded above by `deriv f y`.
    -- `(f y - f x) / (y - x) ≤ deriv f y` and `y - x > 0`.
    have hxy' : (0 : ℝ) < y - x := sub_pos.mpr hxy
    have hslope :=
      hconv.slope_le_deriv (Set.mem_univ x) (Set.mem_univ y) hxy (hf y)
    rw [slope_def_field] at hslope
    rw [div_le_iff₀ hxy'] at hslope
    -- `hslope : f y - f x ≤ deriv f y * (y - x)`, goal needs `(x - y)`.
    have hneg : deriv f y * (x - y) = -(deriv f y * (y - x)) := by ring
    linarith
  · -- Case `x = y`: tangent line value equals `f y`.
    subst hxy
    simp
  · -- Case `y < x`: slope at left endpoint `y` is bounded below by `deriv f y`.
    -- `deriv f y ≤ (f x - f y) / (x - y)` and `x - y > 0`.
    have hyx' : (0 : ℝ) < x - y := sub_pos.mpr hxy
    have hslope :=
      hconv.deriv_le_slope (Set.mem_univ y) (Set.mem_univ x) hxy (hf y)
    rw [slope_def_field] at hslope
    rw [le_div_iff₀ hyx'] at hslope
    -- `hslope : deriv f y * (x - y) ≤ f x - f y`.
    linarith

/-- **Lyapunov function for scalar convex gradient flow.**
`V(t) := t · (f(α t) - f(x*)) + (α t - x*)² / 2`.

This is the standard Lyapunov function whose derivative-sign analysis
yields the O(1/t) convergence rate for the continuous-time gradient
flow of a convex objective. The first summand captures the
time-weighted optimality gap; the second is the (kinetic-style)
squared distance to the optimiser. -/
noncomputable def gradientFlowLyapunov (f α : ℝ → ℝ) (xstar : ℝ) : ℝ → ℝ :=
  fun t => t * (f (α t) - f xstar) + (α t - xstar) ^ 2 / 2

/-- **Derivative of the gradient-flow Lyapunov function.**
Along any gradient flow `α'(t) = -(deriv f) (α t)` with `f`
differentiable, `V := gradientFlowLyapunov f α xstar` satisfies
`V'(t) = (f(α t) - f xstar) - t · (deriv f (α t))² - deriv f (α t) · (α t - xstar)`.

This is the load-bearing identity for the convex O(1/t) decay theorem:
plugging in the convex first-order inequality
`f(α t) - f xstar ≤ deriv f (α t) · (α t - xstar)` shows the first and
third summands cancel down to a nonpositive residual, with the middle
`-t · (deriv f)²` term contributing the negative-definite dissipation. -/
theorem gradient_flow_lyapunov_hasDerivAt
    {f α : ℝ → ℝ} (hα : IsGradientFlow f α) (hf : Differentiable ℝ f)
    (xstar t : ℝ) :
    HasDerivAt (gradientFlowLyapunov f α xstar)
      ((f (α t) - f xstar) - t * (deriv f (α t)) ^ 2
        - deriv f (α t) * (α t - xstar)) t := by
  -- Part 1: derivative of `t ↦ t · (f (α t) - f xstar)`.
  have h_energy : HasDerivAt (fun s : ℝ => f (α s)) (-(deriv f (α t)) ^ 2) t :=
    gradient_flow_energy_hasDerivAt_of_differentiable hα hf t
  have h_energy_sub : HasDerivAt (fun s : ℝ => f (α s) - f xstar)
      (-(deriv f (α t)) ^ 2) t := by
    simpa using h_energy.sub_const (f xstar)
  have h_id : HasDerivAt (fun s : ℝ => s) (1 : ℝ) t := hasDerivAt_id t
  have h_part1 :
      HasDerivAt (fun s : ℝ => s * (f (α s) - f xstar))
        (1 * (f (α t) - f xstar) + t * (-(deriv f (α t)) ^ 2)) t :=
    h_id.mul h_energy_sub
  -- Part 2: derivative of `t ↦ (α t - xstar)^2 / 2`.
  have h_α : HasDerivAt α (-(deriv f) (α t)) t := hα t
  have h_α_sub : HasDerivAt (fun s : ℝ => α s - xstar) (-(deriv f) (α t)) t := by
    simpa using h_α.sub_const xstar
  have h_sq : HasDerivAt (fun s : ℝ => (α s - xstar) ^ 2)
      ((2 : ℕ) * (α t - xstar) ^ (2 - 1) * (-(deriv f) (α t))) t :=
    h_α_sub.fun_pow 2
  have h_sq' : HasDerivAt (fun s : ℝ => (α s - xstar) ^ 2)
      (2 * (α t - xstar) * (-(deriv f) (α t))) t := by
    simpa [pow_one] using h_sq
  have h_part2 :
      HasDerivAt (fun s : ℝ => (α s - xstar) ^ 2 / 2)
        ((2 * (α t - xstar) * (-(deriv f) (α t))) / 2) t :=
    h_sq'.div_const 2
  -- Sum the two parts.
  have h_sum :
      HasDerivAt (fun s : ℝ => s * (f (α s) - f xstar) + (α s - xstar) ^ 2 / 2)
        ((1 * (f (α t) - f xstar) + t * (-(deriv f (α t)) ^ 2))
          + (2 * (α t - xstar) * (-(deriv f) (α t))) / 2) t :=
    h_part1.add h_part2
  -- Normalise to the stated derivative value.
  have h_eq :
      (1 * (f (α t) - f xstar) + t * (-(deriv f (α t)) ^ 2))
        + (2 * (α t - xstar) * (-(deriv f) (α t))) / 2
      = (f (α t) - f xstar) - t * (deriv f (α t)) ^ 2
          - deriv f (α t) * (α t - xstar) := by
    ring
  -- Unfold `gradientFlowLyapunov` to expose the underlying sum.
  have h_fun :
      (fun s : ℝ => s * (f (α s) - f xstar) + (α s - xstar) ^ 2 / 2)
        = gradientFlowLyapunov f α xstar := rfl
  rw [← h_fun, ← h_eq]
  exact h_sum

/-- **Derivative of the gradient-flow Lyapunov function is nonpositive.**
For `0 ≤ t` and `f` convex differentiable, the Lyapunov function
`V := gradientFlowLyapunov f α xstar` along any gradient flow satisfies
`V'(t) ≤ 0`.

Combining `gradient_flow_lyapunov_hasDerivAt` with the convex first-order
inequality `f(α t) - f xstar ≤ deriv f (α t) · (α t - xstar)` shows the
non-dissipative summands cancel, leaving `V'(t) ≤ -t · (deriv f (α t))² ≤ 0`. -/
theorem gradient_flow_lyapunov_deriv_nonpos
    {f α : ℝ → ℝ} (hconv : ConvexOn ℝ Set.univ f) (hf : Differentiable ℝ f)
    (hα : IsGradientFlow f α) (xstar t : ℝ) (ht : 0 ≤ t) :
    deriv (gradientFlowLyapunov f α xstar) t ≤ 0 := by
  -- Compute the derivative via `gradient_flow_lyapunov_hasDerivAt`.
  have h_hasDeriv :
      HasDerivAt (gradientFlowLyapunov f α xstar)
        ((f (α t) - f xstar) - t * (deriv f (α t)) ^ 2
          - deriv f (α t) * (α t - xstar)) t :=
    gradient_flow_lyapunov_hasDerivAt hα hf xstar t
  rw [h_hasDeriv.deriv]
  -- Convex first-order inequality at `x = xstar`, `y = α t`:
  --   `f (α t) + deriv f (α t) * (xstar - α t) ≤ f xstar`.
  have h_conv := convex_first_order_inequality hconv hf xstar (α t)
  -- Rearrange to `f (α t) - f xstar ≤ deriv f (α t) * (α t - xstar)`.
  have h_gap :
      f (α t) - f xstar ≤ deriv f (α t) * (α t - xstar) := by
    have h_rw : deriv f (α t) * (xstar - α t)
        = -(deriv f (α t) * (α t - xstar)) := by
      ring
    rw [h_rw] at h_conv
    linarith
  -- The middle term is `-t · (deriv f (α t))² ≤ 0`.
  have h_sq_nn : 0 ≤ t * (deriv f (α t)) ^ 2 :=
    mul_nonneg ht (sq_nonneg _)
  linarith

/-- **Convex O(1/t) gradient-flow decay theorem.**
Let `f : ℝ → ℝ` be convex and differentiable on all of `ℝ`, and let
`α : ℝ → ℝ` be a gradient-flow trajectory of `f` (i.e.
`α'(t) = -(deriv f)(α t)` for all `t`) with `α 0 = x₀`. Then for any
`xstar : ℝ` (interpreted as a candidate minimiser) and any `t > 0`,
the optimality gap along the trajectory decays at the rate `1 / (2t)`:
```
f (α t) - f xstar ≤ (x₀ - xstar) ^ 2 / (2 * t).
```

This is the classical scalar version of Bach's §5 result on the
continuous-time convergence rate of gradient flow on convex
functions. The proof composes the Lyapunov function
`V t := t · (f (α t) - f xstar) + (α t - xstar)² / 2` together with
the dissipation inequality `V'(t) ≤ 0`:

* By `antitoneOn_of_deriv_nonpos` on `Set.Ici 0`, `V` is antitone on
  the nonnegative reals, so `V t ≤ V 0` for `0 ≤ t`.
* At `t = 0`: `V 0 = 0 · (·) + (α 0 - xstar)² / 2 = (x₀ - xstar)² / 2`.
* For `0 < t`: dropping the nonnegative squared term yields
  `t · (f (α t) - f xstar) ≤ V t`.
* Chaining and dividing by `t > 0` gives the stated rate.

The hypothesis `α 0 = x₀` only enters at the boundary computation of
`V 0`; the upstream Lyapunov machinery is fully independent of the
initial-value normalisation. -/
theorem gradient_flow_convex_decay_one_div_t
    {f α : ℝ → ℝ} {x₀ xstar t : ℝ}
    (hconv : ConvexOn ℝ Set.univ f) (hf : Differentiable ℝ f)
    (hα : IsGradientFlow f α) (hα0 : α 0 = x₀) (ht : 0 < t) :
    f (α t) - f xstar ≤ (x₀ - xstar) ^ 2 / (2 * t) := by
  -- Abbreviate the Lyapunov function.
  set V : ℝ → ℝ := gradientFlowLyapunov f α xstar with hV_def
  -- `V` is differentiable everywhere via `gradient_flow_lyapunov_hasDerivAt`.
  have hV_diff : Differentiable ℝ V := by
    intro s
    exact (gradient_flow_lyapunov_hasDerivAt hα hf xstar s).differentiableAt
  -- Apply `antitoneOn_of_deriv_nonpos` on `Set.Ici 0`.
  have h_antitone : AntitoneOn V (Set.Ici (0 : ℝ)) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0)
      hV_diff.continuous.continuousOn hV_diff.differentiableOn ?_
    intro s hs
    -- `s ∈ interior (Set.Ici 0) = Set.Ioi 0`.
    rw [interior_Ici] at hs
    exact gradient_flow_lyapunov_deriv_nonpos hconv hf hα xstar s (le_of_lt hs)
  -- `V t ≤ V 0` since `0 ≤ t` and `V` is antitone on `Ici 0`.
  have h_Vt_le_V0 : V t ≤ V 0 :=
    h_antitone (Set.self_mem_Ici) (Set.mem_Ici.mpr ht.le) ht.le
  -- Compute `V 0 = (x₀ - xstar)^2 / 2`.
  have h_V0 : V 0 = (x₀ - xstar) ^ 2 / 2 := by
    simp [hV_def, gradientFlowLyapunov, hα0]
  -- Lower bound: `t · (f (α t) - f xstar) ≤ V t`.
  have h_sq_nn : 0 ≤ (α t - xstar) ^ 2 / 2 :=
    div_nonneg (sq_nonneg _) (by norm_num)
  have h_tgap_le_Vt : t * (f (α t) - f xstar) ≤ V t := by
    have : V t = t * (f (α t) - f xstar) + (α t - xstar) ^ 2 / 2 := by
      simp [hV_def, gradientFlowLyapunov]
    linarith
  -- Chain: `t · (f (α t) - f xstar) ≤ V t ≤ V 0 = (x₀ - xstar)^2 / 2`.
  have h_tgap_le_half : t * (f (α t) - f xstar) ≤ (x₀ - xstar) ^ 2 / 2 := by
    calc t * (f (α t) - f xstar)
        ≤ V t := h_tgap_le_Vt
      _ ≤ V 0 := h_Vt_le_V0
      _ = (x₀ - xstar) ^ 2 / 2 := h_V0
  -- Divide both sides by `t > 0`.
  have h_div : f (α t) - f xstar ≤ (x₀ - xstar) ^ 2 / 2 / t := by
    rw [le_div_iff₀ ht]
    linarith [h_tgap_le_half]
  -- Normalise `(x₀ - xstar)^2 / 2 / t = (x₀ - xstar)^2 / (2 * t)`.
  have h_norm : (x₀ - xstar) ^ 2 / 2 / t = (x₀ - xstar) ^ 2 / (2 * t) := by
    rw [div_div]
  linarith [h_div, h_norm.symm.le, h_norm.le]

/-- Three iterations of gradient descent on `f y = y² / 2` with step
size `η = 1/2` starting at `x = 1` produce `(1/2)^3 = 1/8`. -/
example : gradIter (fun y : ℝ => y ^ 2 / 2) (1 / 2) 3 1 = 1 / 8 := by
  rw [gradIter_quadratic_geometric_n]
  norm_num

/-- One step of gradient descent on `f y = y² / 2` with step size
`η = 1` is the *Newton step* for the quadratic: it sends every point
straight to the unique minimiser `x = 0`. -/
example (x : ℝ) : gradStep (fun y : ℝ => y ^ 2 / 2) 1 x = 0 := by
  rw [gradStep_quadratic]; ring

end LTFP.MathlibExt.Calculus
