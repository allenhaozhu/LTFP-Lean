/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith

/-!
# `L`-smoothness and the descent quadratic

A differentiable function `f : ℝ → ℝ` is *`L`-smooth* if its derivative
is `L`-Lipschitz, i.e.
`|f'(x) - f'(y)| ≤ L * |x - y|` for every `x, y : ℝ`.
The classical descent lemma (Nesterov, *Lectures on Convex Optimization*,
Theorem 2.1.5) states that for any such `f` and any step size `η > 0`,
the gradient-descent update `x⁺ = x - η * f'(x)` satisfies
`f(x⁺) ≤ f(x) - η * (1 - L * η / 2) * |f'(x)|²`.
For the canonical choice `η = 1 / L` this reduces to
`f(x⁺) ≤ f(x) - 1 / (2 * L) * |f'(x)|²`, and the AM–GM identity
`1 / (2 L) - η * (1 - L η / 2) = (L η - 1)² / (2 L)` shows that
`η = 1 / L` is rate-optimal.

This module proves the **algebraic core** of the descent lemma together
with the scalar `IsLSmooth` predicate and a few stability lemmas. It
deliberately stops short of the analytic conclusion: the full descent
inequality requires a `fderiv`-level Cauchy mean-value step against an
`L`-Lipschitz gradient, which in turn depends on multivariate
`fderiv`/`HasFDerivAt` infrastructure that is not in scope for this MVP.

**Status: partial — multivariate `fderiv` version pending.**
The current file fixes:

* the scalar predicate `IsLSmooth` on `ℝ → ℝ`;
* the descent-quadratic optimization (nonneg, value at `1/L`,
  optimality, negativity for `η > 2/L`);
* a worked instance on `f y = y² / 2`;
* closure of `IsLSmooth` under `+ const` and positive scaling, plus
  the trivial `const` and `linear` witnesses.

What is **pending** for a follow-up Mathlib PR:

* `IsLSmooth` on a general normed space, phrased via `fderiv`:
  `‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L * ‖x - y‖`.
* The descent inequality
  `f (x - η • fderiv ℝ f x) ≤ f x - η * (1 - L * η / 2) * ‖fderiv ℝ f x‖²`
  for `0 ≤ η ≤ 1 / L`, obtained via a Cauchy mean-value argument on the
  segment `[x, x⁺]` using the `L`-Lipschitz hypothesis on `fderiv`.
* The integrated form of the fundamental theorem of calculus
  `f y - f x = ∫₀¹ ⟨fderiv ℝ f (x + t • (y - x)), y - x⟩ dt`
  which is the standard route to the previous bullet.

## Main definitions

* `LTFP.MathlibExt.Analysis.IsLSmooth` : the scalar `L`-smoothness
  predicate `∀ x y, |deriv f x - deriv f y| ≤ L * |x - y|`.

## Main results

* `descent_ratio_nonneg` — the descent quadratic `η * (1 - L η / 2)` is
  nonneg on the admissible region `0 ≤ η`, `η * L ≤ 1`.
* `descent_ratio_eq_one_over_two_L` — at `η = 1 / L` the descent
  quadratic equals `1 / (2 L)`.
* `descent_ratio_max_at_inverse_L` — the descent quadratic is bounded
  above by `1 / (2 L)`, certifying that `η = 1 / L` is rate-optimal.
* `descent_ratio_neg_of_step_too_large` — for `L > 0` and `η > 2 / L`
  the descent quadratic is strictly negative, so a single gradient step
  is no longer guaranteed to decrease the objective.
* `descent_scalar_quadratic` — concrete instance on `f y = y² / 2`:
  the gradient-descent step with `L = 1`, `η = 1` jumps directly to the
  minimizer and the descent inequality holds with equality.
* `IsLSmooth.const`, `IsLSmooth.linear` — constant and affine functions
  are `L`-smooth for every `L ≥ 0`.
* `IsLSmooth.add_const` — adding a constant preserves `L`-smoothness.
* `IsLSmooth.const_smul` — multiplying by a nonneg scalar `c` rescales
  the smoothness constant by `c`.

## Implementation notes

Proposed Mathlib path: `Mathlib/Analysis/Calculus/LSmooth.lean`.
Proposed namespace: `Analysis` (the file is currently in
`LTFP.MathlibExt.Analysis`; rename on upstreaming).

The scalar definition is intentionally framed in terms of `deriv`
rather than `HasDerivAt`. This makes the predicate point-free and the
basic stability lemmas (`add_const`, `const_smul`) one-liners; the
trade-off is that nondifferentiable functions trivially satisfy the
predicate (`deriv` falls back to `0`). Upstream, the multivariate
version will be phrased in terms of `fderiv` with the same trade-off.

## References

* Yurii Nesterov, *Lectures on Convex Optimization*, 2nd ed., Springer,
  2018, §2.1 (descent lemma, Theorem 2.1.5).
* Francis Bach, *Learning Theory from First Principles*, MIT Press,
  2024, §5.1 (gradient descent on smooth functions; the LTFP-Lean
  downstream that motivates this PR).
* Stephen Boyd and Lieven Vandenberghe, *Convex Optimization*,
  Cambridge University Press, 2004, §9.3 (gradient methods).

## Tags

L-smooth, Lipschitz gradient, gradient descent, descent lemma,
convex optimization
-/

namespace LTFP.MathlibExt.Analysis

/-- The **descent quadratic** `η ↦ η * (1 - L * η / 2)` is nonneg on the
admissible region `0 ≤ η` and `η * L ≤ 1`.

This is the elementary algebraic content of the descent lemma: on the
step-size interval `[0, 1/L]` a single gradient step is guaranteed not
to increase the objective. The hypothesis `0 ≤ L` is recorded because
it matches the usual context (a Lipschitz constant) in which this lemma
is invoked. -/
theorem descent_ratio_nonneg
    (L η : ℝ) (hL : 0 ≤ L) (hη : 0 ≤ η) (hηL : η * L ≤ 1) :
    0 ≤ η * (1 - L * η / 2) := by
  -- `L * η = η * L ≤ 1`, hence `1 - L * η / 2 ≥ 1/2 ≥ 0`; multiplying
  -- by the nonneg factor `η` preserves nonnegativity.
  have hLη_nonneg : 0 ≤ L * η := mul_nonneg hL hη
  have hLη_le_one : L * η ≤ 1 := by rw [mul_comm]; exact hηL
  have h_pos_factor : 0 ≤ 1 - L * η / 2 := by linarith
  exact mul_nonneg hη h_pos_factor

/-- At the canonical step size `η = 1 / L` the descent quadratic
`η * (1 - L * η / 2)` equals `1 / (2 * L)`. -/
theorem descent_ratio_eq_one_over_two_L
    (L : ℝ) (hL : 0 < L) :
    (1 / L) * (1 - L * (1 / L) / 2) = 1 / (2 * L) := by
  have hL_ne : L ≠ 0 := ne_of_gt hL
  field_simp
  ring

/-- The descent quadratic `η * (1 - L * η / 2)` is bounded above by
`1 / (2 * L)`, with equality at `η = 1 / L`. Hence `1 / L` is the
rate-optimal step size of gradient descent for an `L`-smooth function.

The proof is the AM–GM-type identity
`1 / (2 L) - η * (1 - L η / 2) = (L η - 1)² / (2 L) ≥ 0`. -/
theorem descent_ratio_max_at_inverse_L
    (L η : ℝ) (hL : 0 < L) (_hη : 0 ≤ η) :
    η * (1 - L * η / 2) ≤ 1 / (2 * L) := by
  have hL_ne : L ≠ 0 := ne_of_gt hL
  have h_sq : 0 ≤ (L * η - 1) ^ 2 := sq_nonneg _
  have h_two_L : 0 < 2 * L := by linarith
  rw [div_eq_mul_inv, ← sub_nonneg]
  have h_eq :
      1 / (2 * L) - η * (1 - L * η / 2)
        = (L * η - 1) ^ 2 / (2 * L) := by
    field_simp
    ring
  have h_target : 0 ≤ 1 / (2 * L) - η * (1 - L * η / 2) := by
    rw [h_eq]
    exact div_nonneg h_sq (le_of_lt h_two_L)
  simpa [div_eq_mul_inv] using h_target

/-- For `L > 0` and `η > 2 / L` the descent quadratic
`η * (1 - L * η / 2)` is *strictly negative*: a single gradient-descent
step is no longer guaranteed to decrease the objective.

This is the converse boundary of `descent_ratio_nonneg`; together they
delineate the admissible step-size window `(0, 2 / L)` of vanilla
gradient descent on an `L`-smooth function. -/
theorem descent_ratio_neg_of_step_too_large
    (L η : ℝ) (hL : 0 < L) (hη : 2 / L < η) :
    η * (1 - L * η / 2) < 0 := by
  -- `η > 2 / L > 0` and `L * η > 2`, so `1 - L * η / 2 < 0`.
  have hL_pos : 0 < L := hL
  have hTwoOverL_pos : 0 < 2 / L := by positivity
  have hη_pos : 0 < η := lt_trans hTwoOverL_pos hη
  have hLη_gt_two : 2 < L * η := by
    have h := (mul_lt_mul_of_pos_left hη hL_pos)
    -- `L * (2 / L) < L * η`, and the LHS simplifies to `2`.
    have hL_ne : L ≠ 0 := ne_of_gt hL
    have hsimp : L * (2 / L) = 2 := by field_simp
    rw [hsimp] at h
    exact h
  have h_neg_factor : 1 - L * η / 2 < 0 := by linarith
  exact mul_neg_of_pos_of_neg hη_pos h_neg_factor

/-- Concrete instance of the descent lemma on the scalar quadratic
`f y = y² / 2`: gradient descent with `L = 1` and `η = 1` jumps from
`x` to `x - x = 0` and decreases the value by exactly `x² / 2`. The
descent inequality
`f(x⁺) ≤ f(x) - η (1 - L η / 2) * (f'(x))²`
holds here with equality, witnessing tightness of the descent
quadratic at `η = 1 / L`. -/
theorem descent_scalar_quadratic (x : ℝ) :
    (fun y : ℝ => y ^ 2 / 2) (x - x)
      = (fun y : ℝ => y ^ 2 / 2) x - x ^ 2 / 2 := by
  show (x - x) ^ 2 / 2 = x ^ 2 / 2 - x ^ 2 / 2
  ring

/-- A scalar function `f : ℝ → ℝ` is **`L`-smooth** if its derivative
is `L`-Lipschitz: `|f'(x) - f'(y)| ≤ L * |x - y|` for every `x, y : ℝ`.

This is the scalar specialisation of the general (multivariate) notion
used in convex optimisation. The multivariate `fderiv`-form is the
target of the follow-up Mathlib PR; see the module docstring. -/
def IsLSmooth (L : ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ x y : ℝ, |deriv f x - deriv f y| ≤ L * |x - y|

namespace IsLSmooth

/-- Every constant function is `L`-smooth for every `L ≥ 0`: its
derivative is identically zero, so the Lipschitz bound holds
trivially. -/
theorem const (L c : ℝ) (hL : 0 ≤ L) :
    IsLSmooth L (fun _ : ℝ => c) := by
  intro x y
  have hd : deriv (fun _ : ℝ => c) = fun _ : ℝ => (0 : ℝ) := by
    funext _; simp
  rw [hd]
  simp [mul_nonneg hL (abs_nonneg _)]

/-- Every affine function `x ↦ a * x + b` is `L`-smooth for every
`L ≥ 0`: its derivative is the constant `a`, so the left-hand side of
the Lipschitz inequality is zero. -/
theorem linear (a b L : ℝ) (hL : 0 ≤ L) :
    IsLSmooth L (fun x : ℝ => a * x + b) := by
  intro x y
  have hd : deriv (fun x : ℝ => a * x + b) = fun _ : ℝ => a := by
    funext z
    have h1 : HasDerivAt (fun x : ℝ => a * x + b) a z := by
      simpa using (((hasDerivAt_id z).const_mul a).add_const b)
    exact h1.deriv
  rw [hd]
  simp [mul_nonneg hL (abs_nonneg _)]

/-- Adding a constant `c` to an `L`-smooth function preserves
`L`-smoothness: the derivative is shifted only by `0`, so the Lipschitz
bound is unchanged. -/
theorem add_const {L : ℝ} {f : ℝ → ℝ} (hf : IsLSmooth L f) (c : ℝ) :
    IsLSmooth L (fun x : ℝ => f x + c) := by
  intro x y
  have hd : deriv (fun x : ℝ => f x + c) = deriv f := by
    funext z
    simp [deriv_add_const]
  rw [hd]
  exact hf x y

/-- Multiplying an `L`-smooth function by a nonneg constant `c` yields
a `(c * L)`-smooth function: `(c • f)' = c • f'`, and the Lipschitz
constant scales linearly. -/
theorem const_smul {L : ℝ} {f : ℝ → ℝ} (hf : IsLSmooth L f)
    {c : ℝ} (hc : 0 ≤ c) :
    IsLSmooth (c * L) (fun x : ℝ => c * f x) := by
  intro x y
  have hd : deriv (fun x : ℝ => c * f x) = fun z => c * deriv f z := by
    funext z
    simp [deriv_const_mul_field]
  rw [hd]
  have h_step : |c * deriv f x - c * deriv f y| = c * |deriv f x - deriv f y| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hc]
  have h_bound : |deriv f x - deriv f y| ≤ L * |x - y| := hf x y
  calc |c * deriv f x - c * deriv f y|
      = c * |deriv f x - deriv f y| := h_step
    _ ≤ c * (L * |x - y|) := by
        exact mul_le_mul_of_nonneg_left h_bound hc
    _ = c * L * |x - y| := by ring

end IsLSmooth

/-! ### Examples -/

/-- Compute the derivative of the scalar quadratic `y ↦ y² / 2`:
it is the identity `z ↦ z`. -/
private lemma deriv_half_sq (z : ℝ) :
    deriv (fun y : ℝ => y ^ 2 / 2) z = z := by
  have h1 : HasDerivAt (fun y : ℝ => y ^ 2) ((2 : ℕ) * z ^ (2 - 1)) z :=
    hasDerivAt_pow 2 z
  have h1' : HasDerivAt (fun y : ℝ => y ^ 2) (2 * z) z := by
    have : ((2 : ℕ) : ℝ) * z ^ (2 - 1) = 2 * z := by norm_num
    simpa [this] using h1
  have h2 : HasDerivAt (fun y : ℝ => y ^ 2 / 2) ((2 * z) / 2) z :=
    h1'.div_const 2
  have h2' : HasDerivAt (fun y : ℝ => y ^ 2 / 2) z z := by
    have : (2 * z) / 2 = z := by ring
    simpa [this] using h2
  exact h2'.deriv

/-- The scalar quadratic `f y = y² / 2` is `1`-smooth: its derivative
is the identity, which is `1`-Lipschitz. -/
example : IsLSmooth 1 (fun y : ℝ => y ^ 2 / 2) := by
  intro x y
  have hderiv : deriv (fun y : ℝ => y ^ 2 / 2) = fun z => z := by
    funext z
    exact deriv_half_sq z
  rw [hderiv]
  simp [one_mul]

/-- One gradient-descent step on `f y = y² / 2` with step size `η = 1`
sends `x` to `0` — the unique minimiser. This is the worked-equality
case of `descent_scalar_quadratic`. -/
example (x : ℝ) :
    x - (1 : ℝ) * deriv (fun y : ℝ => y ^ 2 / 2) x = 0 := by
  rw [deriv_half_sq]; ring

end LTFP.MathlibExt.Analysis
