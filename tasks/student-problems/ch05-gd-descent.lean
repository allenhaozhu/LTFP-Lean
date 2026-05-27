/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.Ch05_Optimization.GD

/-! # Bach §5.1 — Gradient descent: canonical-step descent inequality

**Problem.** Bach (2024, §5.1, p. 142) shows that for an `L`-smooth
function `f : E → ℝ` (meaning the gradient `∇f` is `L`-Lipschitz),
one step of gradient descent with the *canonical* step size `η = 1/L`
yields a descent guarantee with the explicit prefactor `1/(2L)`:

  `f(x - (1/L) ∇f(x)) ≤ f(x) - (1/(2L)) · ‖∇f(x)‖²`.

This is the *L-smooth descent lemma at the canonical step*, the building
block for every convergence rate in Chapter 5 (convex GD, strongly
convex GD, projected GD, accelerated GD).

LTlib already provides the **general-step** version
`gd_descent_lemma_of_lipschitz_gradient_diff` at any admissible
`η ∈ [0, 2/L]`; your job is to instantiate it at the canonical step
`η = 1/L`, and check that the prefactor collapses from
`η(1 - Lη/2)` to `1/(2L)`.

**Hints**:
- LTlib lemma: `LTFP.gd_descent_lemma_of_lipschitz_gradient_diff` in
  `LTFP/Ch05_Optimization/GD.lean` (line 444).
- Instantiate the lemma at `η := 1 / (L : ℝ)`.
- After instantiation the LHS already matches; the RHS needs the algebraic
  collapse `(1/L) * (1 - L * (1/L) / 2) = 1/(2L)`. LTlib's
  `gd_descent_canonical_step` already proves this collapse if you prefer
  to chain through it, OR you can close by `field_simp` + `ring` since
  `L > 0`.
- Expected length: 3-6 lines.
- Common pitfall: `L : NNReal`, so coerce to `ℝ` consistently. The
  hypothesis `hL : 0 < (L : ℝ)` is the form needed for `field_simp` to
  discharge the `L ≠ 0` side-condition.

**How to verify**: replace `sorry` with your proof, then run
`lake build LTFP.Ch05_Optimization` from the repo root.
-/

namespace LTFP.StudentProblems.Ch05

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- §5.1 — Canonical-step descent inequality for an L-smooth function. -/
theorem student_problem_ch05_gd_canonical_descent
    (f : E → ℝ) (L : NNReal) (x : E) (hL : 0 < (L : ℝ))
    (hDiff : ∀ z : E, HasGradientAt f (gradient f z) z)
    (hLip : LipschitzWith L (gradient f)) :
    f (x - (1 / (L : ℝ)) • gradient f x)
      ≤ f x - (1 / (2 * (L : ℝ))) * ‖gradient f x‖ ^ 2 := by
  sorry

end LTFP.StudentProblems.Ch05
