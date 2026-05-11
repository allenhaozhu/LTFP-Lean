/-
LTFP §5.2 — Gradient descent.

Bach (2024) §5.2, pp. 111-130. Gradient descent on `f : E → ℝ` with
step size `γ` is the iteration `xₜ₊₁ = xₜ − γ · ∇f(xₜ)`. For
convex L-smooth `f`, the suboptimality `f(xₜ) − f*` decays as `O(1/t)`;
for μ-strongly-convex L-smooth `f`, geometrically as `(1 − μ/L)^t`.

We extend `LTFP.Foundations.GradientDescent`'s `gdStep` with an
explicit multi-step iterate, and prove that GD on a constant
function leaves `xₜ = x₀` for all `t`.
-/
import LTFP.Foundations.GradientDescent

namespace LTFP

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- §5.2 — `T`-step iterate of gradient descent: applies `gdStep` `T`
    times starting from `x₀`. -/
noncomputable def gdIterate (γ : ℝ) (f : E → ℝ) (x0 : E) : ℕ → E
  | 0 => x0
  | t + 1 => gdStep γ f (gdIterate γ f x0 t)

/-- §5.2 sanity lemma: GD on a constant function leaves the iterate
    unchanged at every step. -/
theorem gdIterate_const (γ : ℝ) (c : ℝ) (x0 : E) (t : ℕ) :
    gdIterate γ (fun _ : E => c) x0 t = x0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp [gdIterate, ih, gdStep_const]

/-- §5.2.1 — GD with zero step size is a no-op. -/
theorem gdIterate_zero_step (f : E → ℝ) (x0 : E) (t : ℕ) :
    gdIterate (0 : ℝ) f x0 t = x0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp [gdIterate, gdStep, ih]

/-- §5.2 — One-step closed form: x_{t+1} = x_t - γ · ∇f(x_t). -/
theorem gdIterate_succ (γ : ℝ) (f : E → ℝ) (x0 : E) (t : ℕ) :
    gdIterate γ f x0 (t + 1) =
      gdIterate γ f x0 t - γ • gradient f (gdIterate γ f x0 t) := by
  rfl

/-- §5.2 — When ∇f vanishes at x_t, the iterate stays at x_t. -/
theorem gdIterate_fixed_at_critical (γ : ℝ) (f : E → ℝ) (x0 : E) (t : ℕ)
    (h : gradient f (gdIterate γ f x0 t) = 0) :
    gdIterate γ f x0 (t + 1) = gdIterate γ f x0 t := by
  rw [gdIterate_succ, h]
  simp

/-! ### §5.1 — The L-smoothness descent lemma (Bach 2024, p. 109).

For an L-smooth `f : E → ℝ`,
`f(x − η ∇f(x)) ≤ f(x) − η (1 − L η / 2) · ‖∇f(x)‖²`,
and at the canonical step `η = 1/L`,
`f(x⁺) ≤ f(x) − 1/(2L) · ‖∇f(x)‖²`.

Mathlib gap: a fully general L-smoothness descent chain
(`LipschitzWith L (gradient f) → quadratic upper bound → descent`) is
not yet a single named lemma. We register here:

* the **algebraic core** (descent-ratio nonnegativity) on `ℝ`;
* the **canonical step corollary** (η = 1/L collapses the prefactor); and
* a **concrete instance** on `f(x) = x² / 2` with `L = 1`, `η = 1`,
  where the descent inequality holds with equality and is proved by `ring`.

When Mathlib lands the L-smoothness ⇒ quadratic upper bound chain,
the abstract version `f(x − η g) ≤ f(x) − η (1 − Lη/2) ‖g‖²` will be
re-proved against `LipschitzWith L (gradient f)` directly. -/

/-- §5.1 — Algebraic descent-ratio nonnegativity.

The per-iteration descent factor `η · (1 − L η / 2) · a²` is
nonnegative whenever `0 ≤ η`, `0 ≤ L`, and the bracket
`1 − L η / 2 ≥ 0` is nonnegative. This is the scalar core of the
L-smoothness descent inequality: the right-hand side
`f(x) − η (1 − L η / 2) ‖∇f(x)‖²` decreases monotonically. -/
theorem gd_descent_ratio_nonneg
    (a η L : ℝ) (_hL : 0 ≤ L) (hη : 0 ≤ η)
    (hbr : 0 ≤ 1 - L * η / 2) :
    0 ≤ η * (1 - L * η / 2) * a ^ 2 := by
  have hsq : 0 ≤ a ^ 2 := sq_nonneg a
  have h1 : 0 ≤ η * (1 - L * η / 2) := mul_nonneg hη hbr
  exact mul_nonneg h1 hsq

/-- §5.1 — Canonical-step collapse: at `η = 1/L` (with `L > 0`),
the bracket `1 − L η / 2` evaluates to `1/2`, and the descent
prefactor `η · (1 − L η / 2)` collapses to `1 / (2 L)`. -/
theorem gd_descent_canonical_step (L : ℝ) (hL : 0 < L) :
    (1 / L) * (1 - L * (1 / L) / 2) = 1 / (2 * L) := by
  have hLne : L ≠ 0 := ne_of_gt hL
  field_simp
  ring

/-- §5.1 — Concrete descent instance on `f(x) = x² / 2` with `L = 1`,
`η = 1`. The gradient of `f` at `x` is `x`, so the gradient-descent
update is `x⁺ = x − 1 · x = 0`. The descent inequality
`f(x⁺) ≤ f(x) − η (1 − L η / 2) · ‖∇f(x)‖²` then reads
`0 ≤ x² / 2 − (1/2) · x² = 0`, holding with equality. -/
theorem gd_descent_quadratic_unit
    (x : ℝ) :
    ((x - 1 * x) ^ 2) / 2
      ≤ (x ^ 2) / 2 - (1 : ℝ) * (1 - 1 * 1 / 2) * x ^ 2 := by
  nlinarith [sq_nonneg x]

/-- §5.1 — Sharper form of `gd_descent_quadratic_unit`: equality
holds. This pins down the descent identity on the canonical
quadratic test function, anchoring the algebraic content of the
L-smoothness descent lemma. -/
theorem gd_descent_quadratic_unit_eq
    (x : ℝ) :
    ((x - 1 * x) ^ 2) / 2
      = (x ^ 2) / 2 - (1 : ℝ) * (1 - 1 * 1 / 2) * x ^ 2 := by
  ring

/-- §5.1 — Descent inequality on the canonical quadratic with an
arbitrary admissible step `0 ≤ η ≤ 2 / L = 2`. Models the L-smoothness
descent statement
`f(x − η ∇f(x)) ≤ f(x) − η (1 − L η / 2) · ‖∇f(x)‖²`
for `f(x) = x²/2`, `L = 1`, with the sign condition `η (1 − η/2) ≥ 0`
ensuring monotone descent. -/
theorem gd_descent_quadratic
    (x η : ℝ) (_hη : 0 ≤ η) (_hbr : 0 ≤ 1 - η / 2) :
    ((x - η * x) ^ 2) / 2
      ≤ (x ^ 2) / 2 - η * (1 - 1 * η / 2) * x ^ 2 := by
  -- The two sides are in fact equal: a `ring` identity. The hypotheses
  -- `0 ≤ η` and `0 ≤ 1 − η/2` model the L-smoothness admissibility
  -- condition for `L = 1` and document the regime in which the
  -- right-hand side is monotone descent (≤ f(x)).
  nlinarith [sq_nonneg x, sq_nonneg η]

end LTFP
