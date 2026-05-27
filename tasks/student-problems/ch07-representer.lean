/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.Ch07_Kernels

/-! # Bach §7.2 — Representer theorem (minimizer form)

**Problem.** Bach (2024, §7.2, p. 217, Proposition 7.2) states the
representer theorem: for any kernel `k : 𝒳 → 𝒳 → ℝ` realised as an RKHS
(equivalently, in any real inner-product space `E` with training
"feature vectors" `e : Fin n → E`), the regularised empirical-risk
functional

  `J(g) := L((⟨g, eⱼ⟩)ⱼ) + Ω(‖g‖)`

with `Ω : ℝ → ℝ` non-decreasing on `[0, ∞)` always admits a minimizer
that lies in the *finite-dimensional* span of the training feature
vectors. Concretely: if `f : E` is a global minimizer of `J`, then there
exists a `g*` in `span ℝ {e_1, …, e_n}` with `J(g*) = J(f)`.

In RKHS terms, this means the optimal predictor can be expanded as
`f*(x) = ∑ⱼ αⱼ · k(x, xⱼ)` — a finite linear combination of kernel
evaluations at the training points.

**Hints**:
- LTlib lemma: `LTFP.representer_theorem_minimizer` in
  `LTFP/Ch07_Kernels/Representer.lean` (line 207).
- The lemma already gives exactly this conclusion; pass the hypotheses
  through.
- Expected length: 2-4 lines.
- Common pitfall: the hypothesis `[(Submodule.span ℝ (Set.range e)).HasOrthogonalProjection]`
  is required (and standard — finite-dim spans always satisfy it). Make
  sure your variable declarations expose it as a typeclass argument so
  the call to `representer_theorem_minimizer` can fire automatically.

**How to verify**: replace `sorry` with your proof, then run
`lake build LTFP.Ch07_Kernels` from the repo root.
-/

namespace LTFP.StudentProblems.Ch07

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ}

/-- §7.2 — Representer theorem (minimizer form). -/
theorem student_problem_ch07_representer_minimizer
    (e : Fin n → E)
    [(Submodule.span ℝ (Set.range e)).HasOrthogonalProjection]
    (L : (Fin n → ℝ) → ℝ) (Ω : ℝ → ℝ)
    (hΩ : ∀ ⦃a b : ℝ⦄, 0 ≤ a → a ≤ b → Ω a ≤ Ω b)
    {f : E}
    (hf : ∀ g : E,
        L (fun j => inner ℝ f (e j)) + Ω ‖f‖ ≤
          L (fun j => inner ℝ g (e j)) + Ω ‖g‖) :
    ∃ g ∈ Submodule.span ℝ (Set.range e),
      L (fun j => inner ℝ g (e j)) + Ω ‖g‖ =
        L (fun j => inner ℝ f (e j)) + Ω ‖f‖ := by
  sorry

end LTFP.StudentProblems.Ch07
