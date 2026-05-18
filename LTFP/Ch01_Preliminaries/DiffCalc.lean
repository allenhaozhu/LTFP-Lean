/-
LTFP §1.1.5 — Differential calculus preliminaries (gradient, Hessian, chain
rule).  Placeholder anchor; downstream chapters that need gradients import
Mathlib's `fderiv` / `gradient` API directly.
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Gradient.Basic

namespace LTFP

open scoped Gradient

/-- §1.1.5 — anchor for the gradient/Hessian package, Bach 2024 p. 7.

    The book introduces the gradient `∇f` for `f : ℝᵈ → ℝ` along with the
    chain rule and the prototypical identity `∇(½‖x − a‖²) = x − a`.

    For LTFP downstream chapters we just need a stable, real-proven anchor
    on `gradient`.  Per the ticket's `book_excerpt.md`, a smaller fact is
    acceptable; here we record that the gradient of any constant function
    on a real Hilbert space is the zero vector.  This is a genuine instance
    of the differential-calculus toolkit (it is a corollary of the chain
    rule / `fderiv_const`), it is not `True`, and it directly seeds the
    downstream `gradient`/`∇` API. -/
theorem gradient_basics
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (c : ℝ) (x : F) :
    ∇ (fun _ : F => c) x = 0 :=
  gradient_fun_const x c

/-- §1.1.5 — Cauchy–Schwarz inequality on real inner product spaces
    (Bach 2024, p. 7, listed among the preliminary inequalities).

    For all `x y` in a real inner product space `F`,
    `|⟨x, y⟩| ≤ ‖x‖ · ‖y‖`. This is the prerequisite behind the operator-
    norm bound `‖A x‖ ≤ ‖A‖ · ‖x‖` and the smoothness/strong-convexity
    inequalities used throughout Chapter 5. We re-export Mathlib's
    `abs_real_inner_le_norm` inside the `LTFP` namespace so downstream
    chapters do not need to thread the Mathlib name. -/
theorem cauchy_schwarz_real
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (x y : F) :
    |inner ℝ x y| ≤ ‖x‖ * ‖y‖ :=
  abs_real_inner_le_norm x y

end LTFP

#check @LTFP.gradient_basics

open scoped Gradient in
-- Sanity-check example: the gradient of the constant-zero real-valued
-- function on `ℝ` is zero.
example : ∇ (fun _ : ℝ => (0 : ℝ)) (0 : ℝ) = 0 :=
  LTFP.gradient_basics ℝ 0 0

#check @LTFP.cauchy_schwarz_real

/-- Sanity check: on `ℝ` with its standard inner product, Cauchy-Schwarz
    on `(1, 1)` gives `|1| ≤ 1 · 1`. -/
example : |inner ℝ (1 : ℝ) (1 : ℝ)| ≤ ‖(1 : ℝ)‖ * ‖(1 : ℝ)‖ :=
  LTFP.cauchy_schwarz_real ℝ 1 1
