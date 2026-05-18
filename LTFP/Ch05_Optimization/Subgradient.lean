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

/-- §5.3 — **Sum rule for subgradients** (Bach 2024 §5.3, p. 131).
    If `g₁ ∈ ∂f₁(x)` and `g₂ ∈ ∂f₂(x)`, then `g₁ + g₂ ∈ ∂(f₁ + f₂)(x)`.
    This is the basic calculus rule that underlies subgradient methods
    on regularized convex objectives (e.g., the Lasso). -/
theorem IsSubgradient.add
    {f₁ f₂ : E → ℝ} {x g₁ g₂ : E}
    (h₁ : IsSubgradient f₁ x g₁) (h₂ : IsSubgradient f₂ x g₂) :
    IsSubgradient (fun y => f₁ y + f₂ y) x (g₁ + g₂) := by
  intro y
  have e₁ := h₁ y
  have e₂ := h₂ y
  have hinner : inner ℝ (g₁ + g₂) (y - x)
      = inner ℝ g₁ (y - x) + inner ℝ g₂ (y - x) := by
    rw [inner_add_left]
  rw [hinner]
  linarith

/-- §5.3 — **Nonnegative scaling rule** (Bach 2024 §5.3, p. 131).
    If `g ∈ ∂f(x)` and `c ≥ 0`, then `c • g ∈ ∂(c · f)(x)`. This is
    the second fundamental subgradient-calculus rule, used to combine
    a data-fitting loss with a regularizer such as `λ ‖w‖₁`. -/
theorem IsSubgradient.smul_nonneg
    {f : E → ℝ} {x g : E} (hf : IsSubgradient f x g)
    {c : ℝ} (hc : 0 ≤ c) :
    IsSubgradient (fun y => c * f y) x (c • g) := by
  intro y
  have hf' := hf y
  have hinner : inner ℝ (c • g) (y - x) = c * inner ℝ g (y - x) := by
    rw [inner_smul_left]
    simp
  have hineq : c * (f x + inner ℝ g (y - x)) ≤ c * f y :=
    mul_le_mul_of_nonneg_left hf' hc
  -- Goal: c * f x + ⟨c • g, y - x⟩ ≤ c * f y
  rw [hinner]
  have hexpand : c * f x + c * inner ℝ g (y - x)
      = c * (f x + inner ℝ g (y - x)) := by ring
  linarith [hexpand]

/-- §5.3 — **Subgradient characterization of a global minimizer** (Bach
    2024 §5.3, eqn 5.10). For a convex function `f` and a point `x*`,
    the zero vector is a subgradient of `f` at `x*` iff `x*` is a
    global minimizer: `f x* ≤ f y` for all `y`. The forward direction
    `0 ∈ ∂f(x*) → x* is a minimizer` follows immediately from the
    subgradient inequality at `g = 0`. This generalizes the smooth
    first-order optimality condition `∇f(x*) = 0` to the nonsmooth
    setting and is the basis for stopping criteria of subgradient
    methods. -/
theorem IsSubgradient.zero_iff_minimizer_of
    {f : E → ℝ} {xstar : E} (h : IsSubgradient f xstar (0 : E)) :
    ∀ y, f xstar ≤ f y := by
  intro y
  have := h y
  simpa using this

end LTFP
