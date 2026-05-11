/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
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

**Partial.** The continuous-time limit `dx/dt = -∇f(x(t))` — i.e. the
statement that, on a Lipschitz-gradient `f`, the piecewise-linear
interpolant of `gradIter f η n x₀` converges to the unique solution of
the gradient-flow ODE as `η → 0` — is *pending Mathlib ODE
infrastructure*. Concretely it depends on:

* `Mathlib.Analysis.ODE.Gronwall` (already upstream, gives Grönwall's
  inequality) — for the discrete-to-continuous error estimate;
* a Picard–Lindelöf-style existence/uniqueness theorem for ODEs with a
  globally Lipschitz right-hand side on a Banach space (the
  `Mathlib.Analysis.ODE.PicardLindelof` API is currently limited to
  local existence in finite dimension);
* Lyapunov-function theory in the sense of LaSalle, used to conclude
  convergence of trajectories to the set of critical points under
  convexity.

Until those are in place, the discrete iteration developed below acts as
the formal anchor for downstream optimisation results in LTFP-Lean.

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

/-! ### Examples

Small smoke tests of the API: a concrete numerical iteration on the
quadratic, and a one-step convergence to the critical point at the
critical step size `η = 1`. -/

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
