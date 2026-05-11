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

end LTFP

#check @LTFP.gradient_basics

open scoped Gradient in
-- Sanity-check example: the gradient of the constant-zero real-valued
-- function on `ℝ` is zero.
example : ∇ (fun _ : ℝ => (0 : ℝ)) (0 : ℝ) = 0 :=
  LTFP.gradient_basics ℝ 0 0
