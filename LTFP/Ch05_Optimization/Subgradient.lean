/-
LTFP §5.3 — Gradient methods on nonsmooth problems.

Bach (2024) §5.3, pp. 130-134. For nondifferentiable convex `f` (e.g.
the hinge loss, the ℓ₁ penalty), the subgradient method replaces
`∇f(x)` with any element `g(x) ∈ ∂f(x)` of the subdifferential. The
subgradient inequality `f(y) ≥ f(x) + ⟨g, y − x⟩` is the workhorse
of the analysis.
-/
import Mathlib.Analysis.InnerProductSpace.Basic

namespace LTFP

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- §5.3 — A vector `g : E` is a **subgradient** of `f : E → ℝ` at `x`
    iff `f y ≥ f x + ⟨g, y − x⟩` for every `y`. -/
def IsSubgradient (f : E → ℝ) (x g : E) : Prop :=
  ∀ y, f x + inner ℝ g (y - x) ≤ f y

/-- §5.3 sanity lemma: every constant function has the zero subgradient
    at every point (the inequality reduces to `c ≤ c`). -/
theorem isSubgradient_zero_of_const (c : ℝ) (x : E) :
    IsSubgradient (fun _ : E => c) x (0 : E) := by
  intro y
  simp

/-- §5.3 — Subgradients are translation invariant: if `g` is a
    subgradient of `f` at `x`, then `g` is a subgradient of `y ↦ f y + c`
    at `x` for any constant `c`. -/
theorem IsSubgradient.add_const
    {f : E → ℝ} {x g : E} (hf : IsSubgradient f x g) (c : ℝ) :
    IsSubgradient (fun y => f y + c) x g := by
  intro y
  have := hf y
  linarith

end LTFP
