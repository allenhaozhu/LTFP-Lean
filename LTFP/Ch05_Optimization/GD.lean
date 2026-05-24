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
import LTFP.Foundations.Convex
import LTFP.MathlibExt.Analysis.ClosedConvexProjection
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

open InnerProductSpace

namespace LTFP

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-! In what follows we will also need the `LipschitzWith` API on the
    gradient. We import it via `LTFP.Foundations.Convex`'s `IsLSmooth`
    alias to keep notation aligned with Bach's textbook. -/

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

/-! ### Abstract L-smoothness descent lemma (Bach 2024, p. 109, eqn 5.5).

In a real inner-product space, suppose `f : E → ℝ` satisfies the
**L-smooth quadratic upper bound** (Bach 2024 §5.1, eqn 5.4)
`f(y) ≤ f(x) + ⟨∇f(x), y − x⟩ + (L/2) ‖y − x‖²`.
This is the property implied by `LipschitzWith L (gradient f)` and is
the form Bach uses to derive the descent lemma in the textbook.

Substituting `y = x − η · ∇f(x)` and unfolding `‖−η • ∇f(x)‖² =
η² ‖∇f(x)‖²` yields
`f(x − η ∇f(x)) ≤ f(x) − η (1 − L η / 2) · ‖∇f(x)‖²`,
which is the **L-smoothness descent lemma**.

The Mathlib gap noted on the algebraic anchor above is the **first**
step of the chain (`LipschitzWith L (gradient f)` ⇒ the quadratic
upper bound), which requires a Taylor-with-Lagrange-remainder argument
not yet packaged in Mathlib. The **second** step of the chain — from
the quadratic upper bound to the descent lemma — is fully formalized
here, parametrized by the L-smooth upper bound as hypothesis. -/

/-- §5.1 — Abstract L-smoothness descent lemma (intermediate form).

If `f : E → ℝ` satisfies the L-smooth quadratic upper bound
(Bach 2024 §5.1, eqn 5.4) and the step size `η ≥ 0` is admissible
(`L η ≤ 2`, equivalently `1 − L η / 2 ≥ 0`), then the gradient step
strictly decreases `f` by at least `η (1 − L η / 2) · ‖∇f(x)‖²`:
`f(x − η ∇f(x)) ≤ f(x) − η (1 − L η / 2) · ‖∇f(x)‖²`.

The hypothesis `hQ` is the L-smooth quadratic upper bound, which
follows from `LipschitzWith L (gradient f)` via Taylor's theorem
(now discharged below in `lSmooth_quadratic_upper_bound`).

**Intermediate form.** This statement takes the quadratic upper
bound as a hypothesis rather than deriving it from Lipschitz of the
gradient. For the canonical fully-discharged statement that takes
`LipschitzWith L (gradient f)` (plus a differentiability witness)
as its only structural hypothesis, use
`gd_descent_lemma_of_lipschitz_gradient_diff`. This intermediate
form is kept because it remains a useful entry point when the
quadratic upper bound is established by other means (e.g., a
hand-written algebraic argument on a specific `f`, as in
`gd_descent_lemma_const`), and because it factors the proof of the
canonical form cleanly. -/
theorem gd_descent_lemma_of_quadratic_bound
    (f : E → ℝ) (L η : ℝ) (x : E)
    (hQ : ∀ y : E,
      f y ≤ f x + inner ℝ (gradient f x) (y - x) + (L / 2) * ‖y - x‖ ^ 2)
    (_hη : 0 ≤ η) :
    f (x - η • gradient f x)
      ≤ f x - η * (1 - L * η / 2) * ‖gradient f x‖ ^ 2 := by
  -- Specialize hypothesis to `y = x − η • ∇f(x)`.
  have h := hQ (x - η • gradient f x)
  -- Simplify `(x − η • ∇f(x)) − x = −η • ∇f(x)`.
  have hsub : (x - η • gradient f x) - x = -(η • gradient f x) := by
    abel
  -- Simplify the inner product `⟨∇f(x), −η • ∇f(x)⟩ = −η · ‖∇f(x)‖²`.
  have hinner :
      inner ℝ (gradient f x) ((x - η • gradient f x) - x)
        = -η * ‖gradient f x‖ ^ 2 := by
    rw [hsub, inner_neg_right, inner_smul_right, real_inner_self_eq_norm_sq]
    ring
  -- Simplify `‖−η • ∇f(x)‖² = η² · ‖∇f(x)‖²`.
  have hnorm :
      ‖(x - η • gradient f x) - x‖ ^ 2 = η ^ 2 * ‖gradient f x‖ ^ 2 := by
    rw [hsub, norm_neg, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  -- Rewrite the right-hand side of `h` using the two simplifications.
  rw [hinner, hnorm] at h
  -- Algebraic rearrangement: `−η ‖g‖² + (L/2) η² ‖g‖² = −η(1 − Lη/2) ‖g‖²`.
  have : f x + -η * ‖gradient f x‖ ^ 2 + L / 2 * (η ^ 2 * ‖gradient f x‖ ^ 2)
      = f x - η * (1 - L * η / 2) * ‖gradient f x‖ ^ 2 := by
    ring
  linarith [this]

/-- §5.1 — Canonical-step instance of `gd_descent_lemma_of_quadratic_bound`.
At `η = 1/L` with `L > 0`, the descent prefactor collapses to `1/(2L)`,
giving the classical statement
`f(x − (1/L) ∇f(x)) ≤ f(x) − 1/(2L) · ‖∇f(x)‖²`. -/
theorem gd_descent_lemma_canonical_step
    (f : E → ℝ) (L : ℝ) (x : E) (hL : 0 < L)
    (hQ : ∀ y : E,
      f y ≤ f x + inner ℝ (gradient f x) (y - x) + (L / 2) * ‖y - x‖ ^ 2) :
    f (x - (1 / L) • gradient f x)
      ≤ f x - (1 / (2 * L)) * ‖gradient f x‖ ^ 2 := by
  have hηnn : (0 : ℝ) ≤ 1 / L := by positivity
  have hmain :=
    gd_descent_lemma_of_quadratic_bound f L (1 / L) x hQ hηnn
  -- `(1/L) * (1 − L · (1/L) / 2) = 1/(2L)` (canonical-step collapse).
  have hcollapse : (1 / L) * (1 - L * (1 / L) / 2) = 1 / (2 * L) :=
    gd_descent_canonical_step L hL
  -- Rewrite the descent factor.
  have hrew :
      f x - (1 / L) * (1 - L * (1 / L) / 2) * ‖gradient f x‖ ^ 2
        = f x - (1 / (2 * L)) * ‖gradient f x‖ ^ 2 := by
    rw [hcollapse]
  linarith [hmain]

/-! ### §5.1 — Descent lemma from `LipschitzWith` gradient (Taylor bridge).

Bach (2024, §5.1) derives the L-smooth quadratic upper bound
`f(y) ≤ f(x) + ⟨∇f(x), y − x⟩ + (L/2) ‖y − x‖²` from
`LipschitzWith L (gradient f)` via the fundamental theorem of calculus:
defining `g(t) := f(x + t(y − x))`, one has `g'(t) = ⟨∇f(x + t(y − x)),
y − x⟩`, so
```
f(y) − f(x) − ⟨∇f(x), y − x⟩
  = g(1) − g(0) − g'(0)
  = ∫₀¹ ⟨∇f(x + t(y − x)) − ∇f(x), y − x⟩ dt
  ≤ ∫₀¹ L · t · ‖y − x‖² dt = (L/2) · ‖y − x‖².
```
This chain is **not yet packaged as a single Mathlib lemma**: it
requires `HasGradientAt`/`HasFDerivAt` differentiability witnesses, the
parametric mean-value lemma on the line segment, and the bound
`‖∇f(x + t v) − ∇f(x)‖ ≤ L · t · ‖v‖` from `LipschitzWith L (gradient f)`.

We capture the chain as a **two-hypothesis** theorem:

* `hLip : LipschitzWith L (gradient f)` — the L-smoothness witness
  (Bach 2024 §5.1, equivalent to eqn 5.3);
* `hTaylor : the quadratic upper bound` — the Taylor-remainder bridge
  (Bach 2024 §5.1, eqn 5.4), explicitly named so its dependence on the
  Mathlib gap is visible in the type signature.

When Mathlib lands the Taylor-with-Lagrange-remainder chain for
`gradient`, `hTaylor` will be discharged from `hLip` alone, collapsing
this theorem back to a single-hypothesis statement. Until then, the
two-hypothesis form is the honest interface: it makes the L-smoothness
witness load-bearing at the type level (consumers must supply it),
while parametrizing the residual gap explicitly. -/

/-- §5.1 — **L-smooth quadratic upper bound from `LipschitzWith` gradient.**

If `f : E → ℝ` is everywhere differentiable with `gradient f` as its
gradient (`hDiff`) and the gradient is `L`-Lipschitz (`hLip`), then `f`
satisfies the L-smooth quadratic upper bound (Bach 2024 §5.1, eqn 5.4):
`f(y) ≤ f(x) + ⟨∇f(x), y − x⟩ + (L/2) ‖y − x‖²`.

**Proof sketch (Bach 2024 §5.1, "auxiliary function" version).** Define
the one-variable function
`g(t) := f(x + t·v) − f(x) − t·⟨∇f(x), v⟩ − (L/2)·t²·‖v‖²`
where `v := y − x`. Then:

* `g(0) = 0`.
* `g'(t) = ⟨∇f(x + t·v), v⟩ − ⟨∇f(x), v⟩ − L·t·‖v‖²`.
* For `t ∈ [0, 1]`, by Cauchy–Schwarz and Lipschitz of the gradient,
  `⟨∇f(x + t·v) − ∇f(x), v⟩ ≤ ‖∇f(x + t·v) − ∇f(x)‖ · ‖v‖
   ≤ L · ‖t · v‖ · ‖v‖ = L · t · ‖v‖²`.
  Hence `g'(t) ≤ 0` on `[0, 1]`.
* By `antitoneOn_of_deriv_nonpos` on `Icc 0 1`, `g` is antitone there,
  so `g(1) ≤ g(0) = 0`, which is exactly the quadratic upper bound. -/
theorem lSmooth_quadratic_upper_bound
    (f : E → ℝ) (L : NNReal) (x y : E)
    (hDiff : ∀ z : E, HasGradientAt f (gradient f z) z)
    (hLip : LipschitzWith L (gradient f)) :
    f y ≤ f x + inner ℝ (gradient f x) (y - x)
            + ((L : ℝ) / 2) * ‖y - x‖ ^ 2 := by
  -- Set `v := y - x` and define the auxiliary function `g : ℝ → ℝ`.
  set v : E := y - x with hv_def
  set g : ℝ → ℝ := fun t =>
    f (x + t • v) - f x - t * inner ℝ (gradient f x) v
      - ((L : ℝ) / 2) * t ^ 2 * ‖v‖ ^ 2 with hg_def
  -- Helper: derivative of `t ↦ f(x + t • v)` is `⟨∇f(x + t • v), v⟩`.
  have hcurve_deriv : ∀ t : ℝ,
      HasDerivAt (fun s : ℝ => f (x + s • v))
        (inner ℝ (gradient f (x + t • v)) v) t := by
    intro t
    have hgrad := hDiff (x + t • v)
    have hfderiv : HasFDerivAt f (toDual ℝ E (gradient f (x + t • v)))
        (x + t • v) := hgrad.hasFDerivAt
    -- Inner curve `s ↦ x + s • v` has derivative `v` at every point.
    have hline : HasDerivAt (fun s : ℝ => x + s • v) v t := by
      have : HasDerivAt (fun s : ℝ => s • v) v t := by
        simpa using (hasDerivAt_id t).smul_const v
      simpa using this.const_add x
    have hcomp := hfderiv.comp_hasDerivAt t hline
    -- Reduce `(toDual ℝ E (gradient f (x + t • v))) v` to `⟨gradient f (...), v⟩`.
    have happ :
        (toDual ℝ E (gradient f (x + t • v))) v
          = inner ℝ (gradient f (x + t • v)) v := rfl
    simpa [happ] using hcomp
  -- Derivative of `g` at `t`: a clean closed form.
  have hg_deriv : ∀ t : ℝ,
      HasDerivAt g
        (inner ℝ (gradient f (x + t • v)) v
          - inner ℝ (gradient f x) v - (L : ℝ) * t * ‖v‖ ^ 2) t := by
    intro t
    -- Component derivatives.
    have h1 : HasDerivAt (fun s : ℝ => f (x + s • v) - f x)
        (inner ℝ (gradient f (x + t • v)) v) t := by
      have := (hcurve_deriv t).sub_const (f x)
      simpa using this
    have h2 : HasDerivAt (fun s : ℝ => s * inner ℝ (gradient f x) v)
        (inner ℝ (gradient f x) v) t := by
      simpa using (hasDerivAt_id t).mul_const (inner ℝ (gradient f x) v)
    have h3 : HasDerivAt (fun s : ℝ => ((L : ℝ) / 2) * s ^ 2 * ‖v‖ ^ 2)
        ((L : ℝ) * t * ‖v‖ ^ 2) t := by
      have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
        simpa using (hasDerivAt_pow 2 t)
      have hL2 :
          HasDerivAt (fun s : ℝ => ((L : ℝ) / 2) * s ^ 2)
            (((L : ℝ) / 2) * (2 * t)) t :=
        hsq.const_mul ((L : ℝ) / 2)
      have := hL2.mul_const (‖v‖ ^ 2)
      have hrw : ((L : ℝ) / 2) * (2 * t) * ‖v‖ ^ 2
          = (L : ℝ) * t * ‖v‖ ^ 2 := by ring
      simpa [hrw] using this
    have hcombo := ((h1.sub h2).sub h3)
    -- `hcombo` already has the right shape modulo definitional unfolding of `g`.
    simpa [g] using hcombo
  -- Cauchy–Schwarz + Lipschitz bound: for `0 ≤ t`, the derivative of `g` is ≤ 0.
  have hg_deriv_nonpos : ∀ t : ℝ, 0 ≤ t →
      inner ℝ (gradient f (x + t • v)) v
        - inner ℝ (gradient f x) v - (L : ℝ) * t * ‖v‖ ^ 2 ≤ 0 := by
    intro t ht
    -- ⟨∇f(x+t·v) − ∇f(x), v⟩ ≤ ‖∇f(x+t·v) − ∇f(x)‖ · ‖v‖.
    have hCS : inner ℝ (gradient f (x + t • v) - gradient f x) v
        ≤ ‖gradient f (x + t • v) - gradient f x‖ * ‖v‖ :=
      real_inner_le_norm _ _
    -- Lipschitz: ‖∇f(x+t·v) − ∇f(x)‖ ≤ L · ‖t · v‖ = L · t · ‖v‖ (since t ≥ 0).
    have hLip_bound :
        ‖gradient f (x + t • v) - gradient f x‖ ≤ (L : ℝ) * (t * ‖v‖) := by
      have h := hLip.norm_sub_le (x + t • v) x
      have hxsub : (x + t • v) - x = t • v := by abel
      rw [hxsub, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at h
      linarith [h]
    have hvnn : 0 ≤ ‖v‖ := norm_nonneg _
    -- Combine: ⟨…, v⟩ ≤ L · t · ‖v‖²
    have hbound :
        inner ℝ (gradient f (x + t • v) - gradient f x) v
          ≤ (L : ℝ) * t * ‖v‖ ^ 2 := by
      calc inner ℝ (gradient f (x + t • v) - gradient f x) v
          ≤ ‖gradient f (x + t • v) - gradient f x‖ * ‖v‖ := hCS
        _ ≤ ((L : ℝ) * (t * ‖v‖)) * ‖v‖ := by
            exact mul_le_mul_of_nonneg_right hLip_bound hvnn
        _ = (L : ℝ) * t * ‖v‖ ^ 2 := by ring
    -- Rewrite the LHS using linearity of inner product.
    have hsplit :
        inner ℝ (gradient f (x + t • v) - gradient f x) v
          = inner ℝ (gradient f (x + t • v)) v - inner ℝ (gradient f x) v := by
      rw [inner_sub_left]
    linarith [hbound, hsplit ▸ hbound]
  -- Antitone on `Icc 0 1`: g(1) ≤ g(0) = 0.
  have hg_antitone : AntitoneOn g (Set.Icc (0 : ℝ) 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (D := Set.Icc (0 : ℝ) 1)
      (convex_Icc 0 1) (f := g)
    · -- ContinuousOn g (Icc 0 1)
      exact fun t _ => (hg_deriv t).continuousAt.continuousWithinAt
    · -- HasDerivWithinAt on the interior
      intro t ht
      exact (hg_deriv t).hasDerivWithinAt
    · -- Derivative non-positive on the interior `Ioo 0 1`.
      intro t ht
      have htmem : t ∈ Set.Ioo (0 : ℝ) 1 := by
        rwa [interior_Icc] at ht
      exact hg_deriv_nonpos t (le_of_lt htmem.1)
  -- Conclude: g(1) ≤ g(0) = 0.
  have hg_1_le_0 : g 1 ≤ g 0 :=
    hg_antitone (by norm_num : (0 : ℝ) ∈ Set.Icc 0 1)
      (by norm_num : (1 : ℝ) ∈ Set.Icc 0 1) (by norm_num : (0 : ℝ) ≤ 1)
  -- Compute g(0) = 0 and unpack g(1).
  have hg_0 : g 0 = 0 := by simp [g]
  have hg_1 : g 1 = f y - f x - inner ℝ (gradient f x) v - ((L : ℝ) / 2) * ‖v‖ ^ 2 := by
    simp [g, hv_def]
  rw [hg_0] at hg_1_le_0
  -- Final algebraic rearrangement: g(1) ≤ 0 unpacks to the quadratic upper bound.
  have hgoal : f y - f x - inner ℝ (gradient f x) v - ((L : ℝ) / 2) * ‖v‖ ^ 2 ≤ 0 := by
    rw [← hg_1]; exact hg_1_le_0
  -- Recall v = y - x; rearrange `f y - … ≤ 0` to `f y ≤ … + …`.
  linarith [hgoal]

/-- §5.1 — L-smoothness descent lemma from `LipschitzWith` gradient.

If `f : E → ℝ` is everywhere differentiable (`hDiff`) and has an
`L`-Lipschitz gradient (`hLip`), then for any admissible step size
`η ≥ 0` the gradient step decreases `f` by at least
`η (1 − L η / 2) · ‖∇f(x)‖²`:
`f(x − η ∇f(x)) ≤ f(x) − η (1 − L η / 2) · ‖∇f(x)‖²`.

This is the **one-hypothesis** form of Bach (2024) §5.1's descent
lemma: the Taylor-bridge `hTaylor` of `gd_descent_lemma_of_lipschitz_gradient`
is now discharged automatically via `lSmooth_quadratic_upper_bound`. -/
theorem gd_descent_lemma_of_lipschitz_gradient_diff
    (f : E → ℝ) (L : NNReal) (η : ℝ) (x : E)
    (hDiff : ∀ z : E, HasGradientAt f (gradient f z) z)
    (hLip : LipschitzWith L (gradient f))
    (hη : 0 ≤ η) :
    f (x - η • gradient f x)
      ≤ f x - η * (1 - (L : ℝ) * η / 2) * ‖gradient f x‖ ^ 2 := by
  have hTaylor : ∀ y : E,
      f y ≤ f x + inner ℝ (gradient f x) (y - x)
              + ((L : ℝ) / 2) * ‖y - x‖ ^ 2 := fun y =>
    lSmooth_quadratic_upper_bound f L x y hDiff hLip
  exact gd_descent_lemma_of_quadratic_bound f (L : ℝ) η x hTaylor hη

/-- §5.1 — L-smoothness descent lemma from `LipschitzWith` gradient
(two-hypothesis form, preserved for backwards compatibility).

If `f : E → ℝ` has an `L`-Lipschitz gradient (`hLip`) and satisfies the
L-smooth quadratic upper bound (`hTaylor`), then the gradient step at
any admissible step size `η` decreases `f` by at least
`η (1 − L η / 2) · ‖∇f(x)‖²`. The differentiability-free version of
`gd_descent_lemma_of_lipschitz_gradient_diff`, suitable when `hTaylor`
is established by other means. -/
theorem gd_descent_lemma_of_lipschitz_gradient
    (f : E → ℝ) (L : NNReal) (η : ℝ) (x : E)
    (_hLip : LipschitzWith L (gradient f))
    (hTaylor : ∀ y : E,
      f y ≤ f x + inner ℝ (gradient f x) (y - x)
              + ((L : ℝ) / 2) * ‖y - x‖ ^ 2)
    (hη : 0 ≤ η) :
    f (x - η • gradient f x)
      ≤ f x - η * (1 - (L : ℝ) * η / 2) * ‖gradient f x‖ ^ 2 :=
  gd_descent_lemma_of_quadratic_bound f (L : ℝ) η x hTaylor hη

/-- §5.1 — Canonical-step instance of the `LipschitzWith`-form descent
lemma. At `η = 1/L` with `L > 0`, the descent prefactor collapses to
`1/(2L)`, yielding the textbook statement
`f(x − (1/L) ∇f(x)) ≤ f(x) − 1/(2L) · ‖∇f(x)‖²` (Bach 2024 §5.1).

The proof reuses `gd_descent_lemma_canonical_step` on the real-valued
Lipschitz constant `(L : ℝ)`. -/
theorem gd_descent_lemma_of_lipschitz_gradient_canonical
    (f : E → ℝ) (L : NNReal) (x : E) (hL : 0 < (L : ℝ))
    (_hLip : LipschitzWith L (gradient f))
    (hTaylor : ∀ y : E,
      f y ≤ f x + inner ℝ (gradient f x) (y - x)
              + ((L : ℝ) / 2) * ‖y - x‖ ^ 2) :
    f (x - (1 / (L : ℝ)) • gradient f x)
      ≤ f x - (1 / (2 * (L : ℝ))) * ‖gradient f x‖ ^ 2 :=
  gd_descent_lemma_canonical_step f (L : ℝ) x hL hTaylor

/-- §5.1 — `IsLSmooth`-flavored statement (LTFP alias unfolded).

For `f : E → ℝ` satisfying `IsLSmooth L f` (i.e. `LipschitzWith L (gradient f)`)
plus the Taylor-bridge quadratic upper bound, the descent inequality
holds. This is just `gd_descent_lemma_of_lipschitz_gradient` rephrased
through LTFP's `IsLSmooth` predicate. -/
theorem gd_descent_lemma_of_isLSmooth
    (f : E → ℝ) (L : NNReal) (η : ℝ) (x : E)
    (hSmooth : IsLSmooth L f)
    (hTaylor : ∀ y : E,
      f y ≤ f x + inner ℝ (gradient f x) (y - x)
              + ((L : ℝ) / 2) * ‖y - x‖ ^ 2)
    (hη : 0 ≤ η) :
    f (x - η • gradient f x)
      ≤ f x - η * (1 - (L : ℝ) * η / 2) * ‖gradient f x‖ ^ 2 :=
  gd_descent_lemma_of_lipschitz_gradient f L η x hSmooth hTaylor hη

/-- §5.1 — Constant function descent (sanity instance).

For a constant function `f ≡ c`, the gradient is zero, so the descent
update is the identity and the inequality reduces to `c ≤ c`. This
discharges both `LipschitzWith 0 (gradient f)` and the trivial
quadratic upper bound `c ≤ c + 0 + 0`, giving a self-contained
end-to-end instance of `gd_descent_lemma_of_lipschitz_gradient` with
no Mathlib gap. -/
theorem gd_descent_lemma_const
    (c : ℝ) (η : ℝ) (x : E) (hη : 0 ≤ η) :
    (fun _ : E => c) (x - η • gradient (fun _ : E => c) x)
      ≤ (fun _ : E => c) x
        - η * (1 - ((0 : NNReal) : ℝ) * η / 2)
          * ‖gradient (fun _ : E => c) x‖ ^ 2 := by
  have hgrad : gradient (fun _ : E => c) x = 0 := gradient_fun_const x c
  have hLip : LipschitzWith (0 : NNReal) (gradient (fun _ : E => c)) := by
    have : gradient (fun _ : E => c) = (fun _ : E => (0 : E)) := by
      funext y
      exact gradient_fun_const y c
    rw [this]
    exact LipschitzWith.const' 0
  have hTaylor : ∀ y : E,
      (fun _ : E => c) y ≤ (fun _ : E => c) x
        + inner ℝ (gradient (fun _ : E => c) x) (y - x)
        + (((0 : NNReal) : ℝ) / 2) * ‖y - x‖ ^ 2 := by
    intro y
    rw [hgrad]
    simp
  exact gd_descent_lemma_of_lipschitz_gradient
    (fun _ : E => c) 0 η x hLip hTaylor hη

/-! ### §5.2 — Heavy-ball / momentum descent (Bach 2024, §5.2 sidebar).

The **heavy-ball** iteration (Polyak 1964, also called Polyak's momentum
method, used in Bach 2024 §5.2 and §5.6) augments gradient descent with
a momentum term: `xₜ₊₁ = xₜ − γ · ∇f(xₜ) + β · (xₜ − xₜ₋₁)`. With
`β = 0`, this reduces to vanilla gradient descent.

We record the per-step map and the structural fact that zero momentum
collapses heavy-ball to gradient descent. The convergence rate analysis
for `β` tuned to the strongly-convex condition number (Polyak's optimal
rate) is on Bach 2024 §5.2 and requires the inertial-Lyapunov chain not
yet packaged in Mathlib. -/

/-- §5.2 — **Heavy-ball / Polyak-momentum step.** From two consecutive
iterates `(x_prev, x)`, the next iterate is
`x − γ · ∇f(x) + β · (x − x_prev)`. The pair `(x, next)` is then fed
back into the iteration. With `β = 0`, this is plain gradient descent. -/
noncomputable def heavyBallStep (γ β : ℝ) (f : E → ℝ) (x_prev x : E) : E :=
  x - γ • gradient f x + β • (x - x_prev)

/-- §5.2 — **Zero-momentum collapse.** With `β = 0`, the heavy-ball
step reduces to the vanilla gradient-descent step `gdStep γ f x`. This
is the structural sanity check that heavy-ball generalizes GD. -/
theorem heavyBallStep_zero_momentum (γ : ℝ) (f : E → ℝ) (x_prev x : E) :
    heavyBallStep γ (0 : ℝ) f x_prev x = gdStep γ f x := by
  unfold heavyBallStep gdStep
  simp

/-! ### §5.2 — Projected gradient descent (Bach 2024, §5.2, p. 124).

For a closed convex constraint set `C ⊆ E` with projection operator
`P_C : E → E`, **projected gradient descent** iterates
`xₜ₊₁ = P_C(xₜ − γ · ∇f(xₜ))`. We register the step map parametrized by
an abstract projection function `proj : E → E`, and prove that on the
identity projection it reduces to vanilla gradient descent.

Full convergence analysis of projected GD (Bach 2024 §5.2.3) requires
nonexpansivity `‖P_C(x) − P_C(y)‖ ≤ ‖x − y‖` and the optimality
condition `⟨x − P_C(x), y − P_C(x)⟩ ≤ 0` for `y ∈ C`, neither of
which we package here. -/

/-- §5.2 — **Projected gradient-descent step** with abstract projection
`proj : E → E`. The step computes a vanilla GD update, then projects
back onto the (implicit) constraint set: `proj (x − γ • ∇f(x))`. -/
noncomputable def pgdStep (γ : ℝ) (proj : E → E) (f : E → ℝ) (x : E) : E :=
  proj (gdStep γ f x)

/-- §5.2 — **Identity-projection collapse.** When the projection is
the identity (i.e., the constraint set is the whole space), projected
GD reduces to vanilla gradient descent (Bach 2024 §5.2). This is the
structural sanity check that `pgdStep` generalizes `gdStep`. -/
theorem pgdStep_id (γ : ℝ) (f : E → ℝ) (x : E) :
    pgdStep γ (fun y => y) f x = gdStep γ f x := by
  unfold pgdStep
  rfl

/-! ### §5.2 — Concrete projected gradient descent.

The abstract `pgdStep` above is parametrized by an arbitrary
projection function `proj : E → E`.  In practice the projection of
interest is the metric projection onto a nonempty closed convex
constraint set `C ⊆ E`, packaged as `closedConvexProj` in
`LTFP/MathlibExt/Analysis/ClosedConvexProjection.lean`.  Specializing
`pgdStep` to that projection gives a concrete projected GD step
together with a feasibility guarantee (the iterate lies in `C`). -/

/-- §5.2 — **Concrete projected gradient-descent step** using the
Hilbert-space metric projection `closedConvexProj` onto a nonempty
closed convex constraint set `C ⊆ E`.  Equivalent to instantiating
`pgdStep` at `proj := closedConvexProj C hne hclosed hconv`. -/
noncomputable def pgdStep_closedConvex (γ : ℝ) (f : E → ℝ)
    (C : Set E) (hne : C.Nonempty) (hclosed : IsClosed C)
    (hconv : Convex ℝ C) (x : E) : E :=
  pgdStep γ (LTFP.MathlibExt.Analysis.closedConvexProj C hne hclosed hconv) f x

/-- §5.2 — **Feasibility of the projected GD step.**  The output of
`pgdStep_closedConvex` always lies in the constraint set `C`, since
it is the image of the metric projection onto `C`. -/
theorem pgdStep_closedConvex_mem (γ : ℝ) (f : E → ℝ)
    (C : Set E) (hne : C.Nonempty) (hclosed : IsClosed C)
    (hconv : Convex ℝ C) (x : E) :
    pgdStep_closedConvex γ f C hne hclosed hconv x ∈ C := by
  unfold pgdStep_closedConvex pgdStep
  exact LTFP.MathlibExt.Analysis.closedConvexProj_mem C hne hclosed hconv _

/-- §5.2 — **PGD distance-drop comparator** at the canonical step
`η = 1/L`.  For convex (`IsMuStronglyConvex 0`) and `L`-smooth `f`
with `L > 0`, the projected gradient-descent step
`p = P_C(x - (1/L) · ∇f(x))` onto a nonempty closed convex set `C`
satisfies the canonical comparator inequality against any reference
point `xstar ∈ C`:
`f(p) − f(x*) ≤ (L/2) · (‖x − x*‖² − ‖p − x*‖²)`.

This is the workhorse one-step inequality for the projected GD
convergence analysis (Bach 2024 §5.2.3); telescoping it over
iterations yields the canonical `O(1/T)` rate on the averaged
iterate.

**Proof structure.**

1. The L-smooth quadratic upper bound (`lSmooth_quadratic_upper_bound`)
   gives `f(p) ≤ f(x) + ⟨∇f(x), p − x⟩ + (L/2)‖p − x‖²`.
2. `IsMuStronglyConvex 0` (i.e., gradient-form convexity) at `(x, xstar)`
   gives `f(x) ≤ f(xstar) + ⟨∇f(x), x − xstar⟩`.
3. The projection variational inequality
   (`closedConvexProj_variational`) applied at `xstar ∈ C` gives
   `⟨x − (1/L)·∇f(x) − p, xstar − p⟩ ≤ 0`, which after multiplying by
   `L > 0` rearranges to
   `⟨∇f(x), p − xstar⟩ ≤ L · ⟨x − p, p − xstar⟩`.
4. The polar identity for real inner products gives
   `2·⟨x − p, p − xstar⟩ + ‖p − x‖² = ‖x − xstar‖² − ‖p − xstar‖²`.

Combining (1)–(4) and rearranging yields the headline inequality. -/
theorem pgdStep_closedConvex_gap_le_distance_drop
    (f : E → ℝ) (L : NNReal) (hL : 0 < (L : ℝ))
    (hDiff : ∀ z : E, HasGradientAt f (gradient f z) z)
    (hLip : LipschitzWith L (gradient f))
    (hConv : IsMuStronglyConvex 0 f)
    (C : Set E) (hne : C.Nonempty) (hclosed : IsClosed C)
    (hCconv : Convex ℝ C) {xstar : E} (hxstar : xstar ∈ C) (x : E) :
    f (pgdStep_closedConvex (1 / (L : ℝ)) f C hne hclosed hCconv x) - f xstar
      ≤ ((L : ℝ) / 2)
          * (‖x - xstar‖ ^ 2
              - ‖pgdStep_closedConvex (1 / (L : ℝ)) f C hne hclosed hCconv x
                  - xstar‖ ^ 2) := by
  -- Local abbreviation for the projected GD iterate.
  set p : E := pgdStep_closedConvex (1 / (L : ℝ)) f C hne hclosed hCconv x
    with hp_def
  -- (1) L-smooth quadratic upper bound at the pair `(x, p)`.
  have hQ : f p ≤ f x + inner ℝ (gradient f x) (p - x)
      + ((L : ℝ) / 2) * ‖p - x‖ ^ 2 :=
    lSmooth_quadratic_upper_bound f L x p hDiff hLip
  -- (2) Gradient-form convexity (μ = 0) at `(x, xstar)`.
  have hfirst :
      f x + inner ℝ (gradient f x) (xstar - x) + (0 / 2) * ‖xstar - x‖ ^ 2
        ≤ f xstar := hConv x xstar
  have hfirst' :
      f x + inner ℝ (gradient f x) (xstar - x) ≤ f xstar := by
    have := hfirst
    simpa using this
  -- (3a) Raw projection variational inequality at `xstar ∈ C`.
  have hproj :
      inner ℝ
          ((x - (1 / (L : ℝ)) • gradient f x)
            - LTFP.MathlibExt.Analysis.closedConvexProj C hne hclosed hCconv
                (x - (1 / (L : ℝ)) • gradient f x))
          (xstar
            - LTFP.MathlibExt.Analysis.closedConvexProj C hne hclosed hCconv
                (x - (1 / (L : ℝ)) • gradient f x)) ≤ 0 :=
    LTFP.MathlibExt.Analysis.closedConvexProj_variational
      C hne hclosed hCconv
      (x - (1 / (L : ℝ)) • gradient f x) xstar hxstar
  -- Identify `p` with the projection symbol used in `hproj`.
  have hp_eq_proj :
      p = LTFP.MathlibExt.Analysis.closedConvexProj C hne hclosed hCconv
            (x - (1 / (L : ℝ)) • gradient f x) := by
    show pgdStep_closedConvex (1 / (L : ℝ)) f C hne hclosed hCconv x = _
    unfold pgdStep_closedConvex pgdStep gdStep
    rfl
  rw [← hp_eq_proj] at hproj
  -- (3b) Multiply by `L > 0` and expand the inner product.  The raw
  -- inequality is `⟨(x - (1/L) ∇f x) - p, xstar - p⟩ ≤ 0`.  Expanding
  -- with `inner_sub_left` and `inner_smul_left` yields
  -- `⟨x - p, xstar - p⟩ ≤ (1/L) ⟨∇f x, xstar - p⟩`.  Multiply by `L`
  -- and rewrite `xstar - p = -(p - xstar)`.
  have hLne : (L : ℝ) ≠ 0 := ne_of_gt hL
  have hproj_expand :
      inner ℝ (x - p) (xstar - p) - (1 / (L : ℝ))
            * inner ℝ (gradient f x) (xstar - p) ≤ 0 := by
    -- Rewrite `(x - (1/L) • ∇f x) - p = (x - p) - (1/L) • ∇f x`.
    have hrearr :
        (x - (1 / (L : ℝ)) • gradient f x) - p
          = (x - p) - (1 / (L : ℝ)) • gradient f x := by abel
    have h := hproj
    rw [hrearr, inner_sub_left, inner_smul_left] at h
    -- `inner_smul_left` over ℝ leaves a `(starRingEnd ℝ) (1/L)` which
    -- is just `1/L`; simp normalizes it.
    simpa [RCLike.conj_to_real] using h
  -- Multiply by `L > 0`: `L · ⟨x - p, xstar - p⟩ ≤ ⟨∇f x, xstar - p⟩`.
  have hproj_mul :
      (L : ℝ) * inner ℝ (x - p) (xstar - p)
        ≤ inner ℝ (gradient f x) (xstar - p) := by
    have hscale :
        (L : ℝ) * (inner ℝ (x - p) (xstar - p)
              - (1 / (L : ℝ)) * inner ℝ (gradient f x) (xstar - p))
          ≤ (L : ℝ) * 0 :=
      mul_le_mul_of_nonneg_left hproj_expand hL.le
    have hLcancel :
        (L : ℝ) * ((1 / (L : ℝ)) * inner ℝ (gradient f x) (xstar - p))
          = inner ℝ (gradient f x) (xstar - p) := by
      field_simp
    nlinarith [hscale, hLcancel]
  -- Rewrite `xstar - p = -(p - xstar)`.
  have hxstar_sub : xstar - p = -(p - xstar) := by abel
  have hproj' :
      inner ℝ (gradient f x) (p - xstar)
        ≤ (L : ℝ) * inner ℝ (x - p) (p - xstar) := by
    have h := hproj_mul
    rw [hxstar_sub, inner_neg_right, inner_neg_right] at h
    linarith
  -- (4) Polar identity: `2 ⟨x - p, p - xstar⟩ + ‖p - x‖² = ‖x - xstar‖² − ‖p - xstar‖²`.
  have hpolar :
      2 * inner ℝ (x - p) (p - xstar) + ‖p - x‖ ^ 2
        = ‖x - xstar‖ ^ 2 - ‖p - xstar‖ ^ 2 := by
    -- Expand both sides using `‖·‖² = ⟨·, ·⟩_ℝ`.
    have hxx : ‖x - xstar‖ ^ 2 = inner ℝ (x - xstar) (x - xstar) := by
      rw [real_inner_self_eq_norm_sq]
    have hpp : ‖p - xstar‖ ^ 2 = inner ℝ (p - xstar) (p - xstar) := by
      rw [real_inner_self_eq_norm_sq]
    have hpx : ‖p - x‖ ^ 2 = inner ℝ (p - x) (p - x) := by
      rw [real_inner_self_eq_norm_sq]
    -- Use the algebraic identity `(x - xstar) = (x - p) + (p - xstar)`
    -- and expand bilinearly.  The remaining cleanup is `ring`-shaped
    -- after collapsing `⟨p - x, ·⟩ = -⟨x - p, ·⟩` and using symmetry.
    have hsplit : x - xstar = (x - p) + (p - xstar) := by abel
    have hpxneg : p - x = -(x - p) := by abel
    rw [hxx, hpp, hpx, hsplit, hpxneg]
    simp only [inner_add_left, inner_add_right, inner_neg_left,
      inner_neg_right, neg_neg]
    -- Use symmetry of real inner product to fold `⟨p - xstar, x - p⟩`
    -- back into `⟨x - p, p - xstar⟩`.
    have hsymm : inner ℝ (p - xstar) (x - p) = inner ℝ (x - p) (p - xstar) := by
      rw [real_inner_comm]
    linarith [hsymm]
  -- (5) Combine.  From (1) + (2):
  --   f p ≤ f xstar + ⟨∇f x, p - xstar⟩ + (L/2) ‖p - x‖².
  have hcombo12 :
      f p ≤ f xstar + inner ℝ (gradient f x) (p - xstar)
              + ((L : ℝ) / 2) * ‖p - x‖ ^ 2 := by
    have h_pxstar :
        inner ℝ (gradient f x) (p - x)
          = inner ℝ (gradient f x) (p - xstar)
            + inner ℝ (gradient f x) (xstar - x) := by
      have hsub : p - x = (p - xstar) + (xstar - x) := by abel
      rw [hsub, inner_add_right]
    -- f p ≤ f x + ⟨∇f x, p-x⟩ + (L/2)‖p-x‖² (from hQ)
    --      ≤ f x + ⟨∇f x, p-xstar⟩ - ⟨∇f x, xstar-x⟩ + (L/2)‖p-x‖²
    -- and f x - ⟨∇f x, xstar-x⟩ ≤ f xstar (from hfirst'), so add.
    linarith [hQ, hfirst', h_pxstar]
  -- Plug (3') into (5):
  --   f p ≤ f xstar + L · ⟨x - p, p - xstar⟩ + (L/2) ‖p - x‖².
  have hcombo123 :
      f p ≤ f xstar + (L : ℝ) * inner ℝ (x - p) (p - xstar)
              + ((L : ℝ) / 2) * ‖p - x‖ ^ 2 := by
    linarith [hcombo12, hproj']
  -- Rearrange RHS using `hpolar`:
  --   L · ⟨x - p, p - xstar⟩ + (L/2) ‖p - x‖²
  -- = (L/2) · (2 ⟨x - p, p - xstar⟩ + ‖p - x‖²)
  -- = (L/2) · (‖x - xstar‖² - ‖p - xstar‖²).
  -- Combine directly via nlinarith using `hpolar` as a linear constraint
  -- relating the inner-product term and the norm-square terms.
  nlinarith [hcombo123, hpolar, sq_nonneg ((L : ℝ))]

/-! ### §5.2 — Multi-step projected gradient descent and the averaged O(1/T) rate.

The one-step comparator `pgdStep_closedConvex_gap_le_distance_drop` telescopes
to a Cesàro-style `O(1/T)` rate on the averaged suboptimality of projected
gradient descent (Bach 2024 §5.2.3).  We package the `T`-step iterate and
the averaged-gap inequality, and a constrained-minimizer corollary. -/

/-- §5.2 — **`T`-step iterate of projected gradient descent** at the canonical
step `η = 1/L` (the parameter `η` is left general).  Starting from `x₀`, the
iteration applies `pgdStep_closedConvex η f C ...` repeatedly.  This is the
PGD analogue of `gdIterate`. -/
noncomputable def pgdIterate_closedConvex
    (η : ℝ) (f : E → ℝ)
    (C : Set E) (hne : C.Nonempty) (hclosed : IsClosed C)
    (hconv : Convex ℝ C) (x0 : E) : ℕ → E
  | 0 => x0
  | t + 1 =>
      pgdStep_closedConvex η f C hne hclosed hconv
        (pgdIterate_closedConvex η f C hne hclosed hconv x0 t)

/-- §5.2 — One-step closed form for `pgdIterate_closedConvex`. -/
theorem pgdIterate_closedConvex_succ
    (η : ℝ) (f : E → ℝ)
    (C : Set E) (hne : C.Nonempty) (hclosed : IsClosed C)
    (hconv : Convex ℝ C) (x0 : E) (t : ℕ) :
    pgdIterate_closedConvex η f C hne hclosed hconv x0 (t + 1)
      = pgdStep_closedConvex η f C hne hclosed hconv
          (pgdIterate_closedConvex η f C hne hclosed hconv x0 t) := rfl

/-- §5.2 — **Averaged `O(1/T)` rate for projected gradient descent.**  At the
canonical step `η = 1/L`, the averaged suboptimality of the PGD iterates
against any reference point `x* ∈ C` is bounded by `L · ‖x₀ − x*‖² / (2T)`:

`(∑ k ∈ range T, (f(x_{k+1}) − f(x*))) / T  ≤  L · ‖x₀ − x*‖² / (2T)`.

The proof telescopes the per-step distance-drop comparator
`pgdStep_closedConvex_gap_le_distance_drop` over `k ∈ {0,…,T-1}` and drops
the (nonnegative) `‖x_T − x*‖²` term.  When `x*` minimizes `f` on `C`, each
summand `f(x_{k+1}) − f(x*)` is nonnegative, so this directly bounds the
average gap (Bach 2024 §5.2.3). -/
theorem pgdIterate_closedConvex_averaged_gap_le
    (f : E → ℝ) (L : NNReal) (hL : 0 < (L : ℝ))
    (hDiff : ∀ z : E, HasGradientAt f (gradient f z) z)
    (hLip : LipschitzWith L (gradient f))
    (hConv : IsMuStronglyConvex 0 f)
    (C : Set E) (hne : C.Nonempty) (hclosed : IsClosed C)
    (hCconv : Convex ℝ C) {xstar : E} (hxstar : xstar ∈ C) (x0 : E) (T : ℕ)
    (hT : 0 < T) :
    (∑ k ∈ Finset.range T,
        (f (pgdIterate_closedConvex (1 / (L : ℝ)) f C hne hclosed hCconv x0
              (k + 1)) - f xstar))
        / (T : ℝ)
      ≤ (L : ℝ) * ‖x0 - xstar‖ ^ 2 / (2 * (T : ℝ)) := by
  -- Abbreviate the iterate trajectory.
  set xs : ℕ → E :=
    fun k => pgdIterate_closedConvex (1 / (L : ℝ)) f C hne hclosed hCconv x0 k
    with hxs_def
  -- Step 1: per-step comparator.  For every `k`, the canonical distance-drop
  -- inequality at `(xs k, xs (k+1))` gives
  --   f (xs (k+1)) - f xstar ≤ (L/2) · (‖xs k - xstar‖² - ‖xs (k+1) - xstar‖²).
  have hstep : ∀ k : ℕ,
      f (xs (k + 1)) - f xstar
        ≤ ((L : ℝ) / 2)
            * (‖xs k - xstar‖ ^ 2 - ‖xs (k + 1) - xstar‖ ^ 2) := by
    intro k
    -- `xs (k+1) = pgdStep_closedConvex (1/L) f C ... (xs k)` by definition.
    have hxs_succ :
        xs (k + 1) = pgdStep_closedConvex (1 / (L : ℝ)) f C hne hclosed hCconv
            (xs k) := pgdIterate_closedConvex_succ _ _ _ _ _ _ _ _
    rw [hxs_succ]
    exact pgdStep_closedConvex_gap_le_distance_drop
      f L hL hDiff hLip hConv C hne hclosed hCconv hxstar (xs k)
  -- Step 2: sum the per-step inequalities over `k ∈ range T`.
  have hsum_step :
      (∑ k ∈ Finset.range T, (f (xs (k + 1)) - f xstar))
        ≤ ∑ k ∈ Finset.range T,
            ((L : ℝ) / 2)
              * (‖xs k - xstar‖ ^ 2 - ‖xs (k + 1) - xstar‖ ^ 2) :=
    Finset.sum_le_sum (fun k _ => hstep k)
  -- Step 3: pull the `(L/2)` factor out and telescope using
  -- `Finset.sum_range_sub'` (additive companion of `prod_range_div'`).
  -- Define `dsq k := ‖xs k - xstar‖^2`.
  set dsq : ℕ → ℝ := fun k => ‖xs k - xstar‖ ^ 2 with hdsq_def
  have htele :
      (∑ k ∈ Finset.range T, (dsq k - dsq (k + 1))) = dsq 0 - dsq T :=
    Finset.sum_range_sub' (fun k => dsq k) T
  have hrhs_fact :
      (∑ k ∈ Finset.range T,
          ((L : ℝ) / 2)
            * (‖xs k - xstar‖ ^ 2 - ‖xs (k + 1) - xstar‖ ^ 2))
        = ((L : ℝ) / 2) * (dsq 0 - dsq T) := by
    have : (∑ k ∈ Finset.range T,
              ((L : ℝ) / 2) * (dsq k - dsq (k + 1)))
              = ((L : ℝ) / 2) * ∑ k ∈ Finset.range T,
                  (dsq k - dsq (k + 1)) := by
      rw [← Finset.mul_sum]
    rw [show (∑ k ∈ Finset.range T,
              ((L : ℝ) / 2)
                * (‖xs k - xstar‖ ^ 2 - ‖xs (k + 1) - xstar‖ ^ 2))
            = ∑ k ∈ Finset.range T,
              ((L : ℝ) / 2) * (dsq k - dsq (k + 1)) from rfl,
        this, htele]
  -- Step 4: drop the nonnegative `dsq T` term:
  --   (L/2) · (dsq 0 - dsq T) ≤ (L/2) · dsq 0.
  have hdsq_T_nn : 0 ≤ dsq T := sq_nonneg _
  have hL2_nn : 0 ≤ (L : ℝ) / 2 := by positivity
  have hdrop :
      ((L : ℝ) / 2) * (dsq 0 - dsq T) ≤ ((L : ℝ) / 2) * dsq 0 := by
    have : (L : ℝ) / 2 * (dsq 0 - dsq T) ≤ (L : ℝ) / 2 * dsq 0 := by
      have hineq : dsq 0 - dsq T ≤ dsq 0 := by linarith
      exact mul_le_mul_of_nonneg_left hineq hL2_nn
    exact this
  -- Step 5: identify `dsq 0 = ‖x0 - xstar‖²`.
  have hdsq0 : dsq 0 = ‖x0 - xstar‖ ^ 2 := by
    show ‖xs 0 - xstar‖ ^ 2 = ‖x0 - xstar‖ ^ 2
    have : xs 0 = x0 := rfl
    rw [this]
  -- Chain: ∑_k (f(xs (k+1)) - f xstar) ≤ (L/2) · ‖x0 - xstar‖².
  have hsum_bound :
      (∑ k ∈ Finset.range T, (f (xs (k + 1)) - f xstar))
        ≤ ((L : ℝ) / 2) * ‖x0 - xstar‖ ^ 2 := by
    calc (∑ k ∈ Finset.range T, (f (xs (k + 1)) - f xstar))
        ≤ ∑ k ∈ Finset.range T,
            ((L : ℝ) / 2)
              * (‖xs k - xstar‖ ^ 2 - ‖xs (k + 1) - xstar‖ ^ 2) := hsum_step
      _ = ((L : ℝ) / 2) * (dsq 0 - dsq T) := hrhs_fact
      _ ≤ ((L : ℝ) / 2) * dsq 0 := hdrop
      _ = ((L : ℝ) / 2) * ‖x0 - xstar‖ ^ 2 := by rw [hdsq0]
  -- Step 6: divide by `T > 0`.
  have hTpos : (0 : ℝ) < (T : ℝ) := by exact_mod_cast hT
  -- Multiply `hsum_bound` by 2 to clear the `L/2` factor:
  --   ∑ k, (f (xs (k+1)) - f xstar) * 2 ≤ L · ‖x0 - xstar‖².
  have hmul2 :
      2 * (∑ k ∈ Finset.range T, (f (xs (k + 1)) - f xstar))
        ≤ (L : ℝ) * ‖x0 - xstar‖ ^ 2 := by
    have h2 : (0 : ℝ) ≤ 2 := by norm_num
    have hscale :
        2 * (∑ k ∈ Finset.range T, (f (xs (k + 1)) - f xstar))
          ≤ 2 * (((L : ℝ) / 2) * ‖x0 - xstar‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsum_bound h2
    have hLrw : 2 * (((L : ℝ) / 2) * ‖x0 - xstar‖ ^ 2)
        = (L : ℝ) * ‖x0 - xstar‖ ^ 2 := by ring
    linarith
  -- Now divide by `2T > 0`.
  have h2Tpos : (0 : ℝ) < 2 * (T : ℝ) := by positivity
  rw [div_le_div_iff₀ hTpos h2Tpos]
  -- Goal: ∑ k, (f (pgdIterate ... (k+1)) - f xstar) * (2 * T)
  --         ≤ L * ‖x0 - xstar‖² * T.
  -- Use `hmul2` and the positivity of `T`.
  have : (∑ k ∈ Finset.range T,
            (f (pgdIterate_closedConvex (1 / (L : ℝ)) f C hne hclosed hCconv x0
                  (k + 1)) - f xstar))
          = ∑ k ∈ Finset.range T, (f (xs (k + 1)) - f xstar) := rfl
  rw [this]
  nlinarith [hmul2, hTpos]

/-- §5.2 — **Constrained-minimizer corollary.**  If `x*` is a minimizer of `f`
on `C`, each summand `f(x_{k+1}) − f(x*)` is nonnegative and the averaged-gap
bound directly controls the average suboptimality of the PGD iterates. -/
theorem pgdIterate_closedConvex_constrained_minimizer_gap_le
    (f : E → ℝ) (L : NNReal) (hL : 0 < (L : ℝ))
    (hDiff : ∀ z : E, HasGradientAt f (gradient f z) z)
    (hLip : LipschitzWith L (gradient f))
    (hConv : IsMuStronglyConvex 0 f)
    (C : Set E) (hne : C.Nonempty) (hclosed : IsClosed C)
    (hCconv : Convex ℝ C) {xstar : E} (hxstar : xstar ∈ C)
    (_hmin : ∀ y ∈ C, f xstar ≤ f y) (x0 : E) (T : ℕ) (hT : 0 < T) :
    (∑ k ∈ Finset.range T,
        (f (pgdIterate_closedConvex (1 / (L : ℝ)) f C hne hclosed hCconv x0
              (k + 1)) - f xstar))
        / (T : ℝ)
      ≤ (L : ℝ) * ‖x0 - xstar‖ ^ 2 / (2 * (T : ℝ)) :=
  pgdIterate_closedConvex_averaged_gap_le
    f L hL hDiff hLip hConv C hne hclosed hCconv hxstar x0 T hT

/-! ### §5.3 — Strong-convexity geometric decay for projected gradient descent.

For `μ`-strongly-convex `L`-smooth `f` with `0 < μ ≤ L`, the canonical
PGD step `η = 1/L` contracts the squared distance to any constrained
minimizer `x* ∈ C` by a factor `(1 - μ/L) ∈ [0, 1)`.  Iterating, the
squared distance decays geometrically as `(1 - μ/L)^t · ‖x₀ - x*‖²`
(Bach 2024 §5.2.4 / 5.3.1, the discrete-time constrained analogue of
the gradient-flow PL exponential decay).

The proof refines milestone #4's comparator by retaining the
`(μ/2)‖x - x*‖²` term (dropped under `μ = 0`), yielding
`f p - f x* ≤ ((L - μ)/2)‖x - x*‖² - (L/2)‖p - x*‖²` at the per-step
level.  Combined with `0 ≤ f p - f x*` (since `x*` minimizes `f` on
`C` and `p ∈ C`), this rearranges to the per-step contraction. -/

/-- §5.3 — **Per-step squared-distance contraction for PGD under μ-strong
convexity.**  For `L`-smooth `μ`-strongly-convex `f` with `0 < L` and
`0 ≤ μ`, the canonical PGD step `η = 1/L` from `x` contracts the squared
distance to any constrained minimizer `x* ∈ C` by `(1 - μ/L)`:

`‖p − x*‖² ≤ (1 − μ/L) · ‖x − x*‖²`,

where `p = pgdStep_closedConvex (1/L) f C x`.

This is the discrete-time constrained analogue of the gradient-flow PL
contraction `(d/dt)‖x_t - x*‖² ≤ -2μ ‖x_t - x*‖²`. -/
theorem pgdStep_closedConvex_stronglyConvex_dist_sq_le
    (f : E → ℝ) (L : NNReal) (μ : ℝ)
    (hL : 0 < (L : ℝ)) (_hμ : 0 ≤ μ)
    (hDiff : ∀ z : E, HasGradientAt f (gradient f z) z)
    (hLip : LipschitzWith L (gradient f))
    (hStrong : IsMuStronglyConvex μ f)
    (C : Set E) (hne : C.Nonempty) (hclosed : IsClosed C)
    (hCconv : Convex ℝ C) {xstar : E} (hxstar : xstar ∈ C)
    (hmin : ∀ y ∈ C, f xstar ≤ f y) (x : E) :
    ‖pgdStep_closedConvex (1 / (L : ℝ)) f C hne hclosed hCconv x - xstar‖ ^ 2
      ≤ (1 - μ / (L : ℝ)) * ‖x - xstar‖ ^ 2 := by
  -- Local abbreviation for the projected GD iterate.
  set p : E := pgdStep_closedConvex (1 / (L : ℝ)) f C hne hclosed hCconv x
    with hp_def
  -- The iterate `p` lies in `C`, so the minimizer property gives `f xstar ≤ f p`.
  have hpC : p ∈ C := by
    simpa [p, hp_def] using
      pgdStep_closedConvex_mem (1 / (L : ℝ)) f C hne hclosed hCconv x
  have hgap : 0 ≤ f p - f xstar := sub_nonneg.mpr (hmin p hpC)
  -- (1) L-smooth quadratic upper bound at the pair `(x, p)`.
  have hQ : f p ≤ f x + inner ℝ (gradient f x) (p - x)
      + ((L : ℝ) / 2) * ‖p - x‖ ^ 2 :=
    lSmooth_quadratic_upper_bound f L x p hDiff hLip
  -- (2) μ-strong convexity at `(x, xstar)`:
  --     f x + ⟨∇f x, xstar - x⟩ + (μ/2) ‖xstar - x‖² ≤ f xstar.
  have hStrong_xs :
      f x + inner ℝ (gradient f x) (xstar - x) + (μ / 2) * ‖xstar - x‖ ^ 2
        ≤ f xstar := hStrong x xstar
  -- Rewrite `‖xstar - x‖² = ‖x - xstar‖²` using `norm_sub_rev`.
  have hnorm_sym : ‖xstar - x‖ = ‖x - xstar‖ := norm_sub_rev xstar x
  have hStrong_xs' :
      f x + inner ℝ (gradient f x) (xstar - x) ≤
        f xstar - (μ / 2) * ‖x - xstar‖ ^ 2 := by
    have h := hStrong_xs
    rw [hnorm_sym] at h
    linarith
  -- (3a) Raw projection variational inequality at `xstar ∈ C`.
  have hproj :
      inner ℝ
          ((x - (1 / (L : ℝ)) • gradient f x)
            - LTFP.MathlibExt.Analysis.closedConvexProj C hne hclosed hCconv
                (x - (1 / (L : ℝ)) • gradient f x))
          (xstar
            - LTFP.MathlibExt.Analysis.closedConvexProj C hne hclosed hCconv
                (x - (1 / (L : ℝ)) • gradient f x)) ≤ 0 :=
    LTFP.MathlibExt.Analysis.closedConvexProj_variational
      C hne hclosed hCconv
      (x - (1 / (L : ℝ)) • gradient f x) xstar hxstar
  -- Identify `p` with the projection symbol used in `hproj`.
  have hp_eq_proj :
      p = LTFP.MathlibExt.Analysis.closedConvexProj C hne hclosed hCconv
            (x - (1 / (L : ℝ)) • gradient f x) := by
    show pgdStep_closedConvex (1 / (L : ℝ)) f C hne hclosed hCconv x = _
    unfold pgdStep_closedConvex pgdStep gdStep
    rfl
  rw [← hp_eq_proj] at hproj
  -- (3b) Expand and rescale exactly as in `pgdStep_closedConvex_gap_le_distance_drop`.
  have hLne : (L : ℝ) ≠ 0 := ne_of_gt hL
  have hproj_expand :
      inner ℝ (x - p) (xstar - p) - (1 / (L : ℝ))
            * inner ℝ (gradient f x) (xstar - p) ≤ 0 := by
    have hrearr :
        (x - (1 / (L : ℝ)) • gradient f x) - p
          = (x - p) - (1 / (L : ℝ)) • gradient f x := by abel
    have h := hproj
    rw [hrearr, inner_sub_left, inner_smul_left] at h
    simpa [RCLike.conj_to_real] using h
  have hproj_mul :
      (L : ℝ) * inner ℝ (x - p) (xstar - p)
        ≤ inner ℝ (gradient f x) (xstar - p) := by
    have hscale :
        (L : ℝ) * (inner ℝ (x - p) (xstar - p)
              - (1 / (L : ℝ)) * inner ℝ (gradient f x) (xstar - p))
          ≤ (L : ℝ) * 0 :=
      mul_le_mul_of_nonneg_left hproj_expand hL.le
    have hLcancel :
        (L : ℝ) * ((1 / (L : ℝ)) * inner ℝ (gradient f x) (xstar - p))
          = inner ℝ (gradient f x) (xstar - p) := by
      field_simp
    nlinarith [hscale, hLcancel]
  have hxstar_sub : xstar - p = -(p - xstar) := by abel
  have hproj' :
      inner ℝ (gradient f x) (p - xstar)
        ≤ (L : ℝ) * inner ℝ (x - p) (p - xstar) := by
    have h := hproj_mul
    rw [hxstar_sub, inner_neg_right, inner_neg_right] at h
    linarith
  -- (4) Polar identity (unchanged from the μ=0 proof).
  have hpolar :
      2 * inner ℝ (x - p) (p - xstar) + ‖p - x‖ ^ 2
        = ‖x - xstar‖ ^ 2 - ‖p - xstar‖ ^ 2 := by
    have hxx : ‖x - xstar‖ ^ 2 = inner ℝ (x - xstar) (x - xstar) := by
      rw [real_inner_self_eq_norm_sq]
    have hpp : ‖p - xstar‖ ^ 2 = inner ℝ (p - xstar) (p - xstar) := by
      rw [real_inner_self_eq_norm_sq]
    have hpx : ‖p - x‖ ^ 2 = inner ℝ (p - x) (p - x) := by
      rw [real_inner_self_eq_norm_sq]
    have hsplit : x - xstar = (x - p) + (p - xstar) := by abel
    have hpxneg : p - x = -(x - p) := by abel
    rw [hxx, hpp, hpx, hsplit, hpxneg]
    simp only [inner_add_left, inner_add_right, inner_neg_left,
      inner_neg_right, neg_neg]
    have hsymm : inner ℝ (p - xstar) (x - p) = inner ℝ (x - p) (p - xstar) := by
      rw [real_inner_comm]
    linarith [hsymm]
  -- (5) Refined comparator combining (1), (2)-with-μ, (3'), (4).
  --     f p ≤ f xstar - (μ/2)‖x - xstar‖² + ⟨∇f x, p - xstar⟩ + (L/2)‖p - x‖².
  have hcombo12 :
      f p ≤ f xstar - (μ / 2) * ‖x - xstar‖ ^ 2
              + inner ℝ (gradient f x) (p - xstar)
              + ((L : ℝ) / 2) * ‖p - x‖ ^ 2 := by
    have h_pxstar :
        inner ℝ (gradient f x) (p - x)
          = inner ℝ (gradient f x) (p - xstar)
            + inner ℝ (gradient f x) (xstar - x) := by
      have hsub : p - x = (p - xstar) + (xstar - x) := by abel
      rw [hsub, inner_add_right]
    linarith [hQ, hStrong_xs', h_pxstar]
  -- Plug (3') into (5'):
  have hcombo123 :
      f p ≤ f xstar - (μ / 2) * ‖x - xstar‖ ^ 2
              + (L : ℝ) * inner ℝ (x - p) (p - xstar)
              + ((L : ℝ) / 2) * ‖p - x‖ ^ 2 := by
    linarith [hcombo12, hproj']
  -- (6) Refined comparator in closed form:
  --     f p - f xstar ≤ ((L - μ)/2)‖x - xstar‖² - (L/2)‖p - xstar‖².
  have hrefined :
      f p - f xstar ≤
        (((L : ℝ) - μ) / 2) * ‖x - xstar‖ ^ 2
          - ((L : ℝ) / 2) * ‖p - xstar‖ ^ 2 := by
    nlinarith [hcombo123, hpolar, sq_nonneg ((L : ℝ))]
  -- (7) Drop `f p - f xstar ≥ 0` to get the L-scaled contraction:
  --     L · ‖p - xstar‖² ≤ (L - μ) · ‖x - xstar‖².
  have hscaled :
      (L : ℝ) * ‖p - xstar‖ ^ 2
        ≤ ((L : ℝ) - μ) * ‖x - xstar‖ ^ 2 := by
    nlinarith [hgap, hrefined]
  -- (8) Factor out `L` on the RHS and cancel via `le_of_mul_le_mul_left`.
  have hfactor : (L : ℝ) - μ = (L : ℝ) * (1 - μ / (L : ℝ)) := by
    field_simp
  rw [hfactor, mul_assoc] at hscaled
  exact le_of_mul_le_mul_left hscaled hL

/-- §5.3 — **Geometric squared-distance decay for PGD under μ-strong
convexity.**  For `L`-smooth `μ`-strongly-convex `f` with `0 < L` and
`0 ≤ μ ≤ L`, iterating the canonical PGD step `η = 1/L` from `x₀` gives

`‖x_t − x*‖² ≤ (1 − μ/L)^t · ‖x₀ − x*‖²`

for any constrained minimizer `x* ∈ C`.  This is the discrete-time
constrained analogue of the gradient-flow PL exponential decay
(b33fb55a) and matches the textbook rate in Bach 2024 §5.2.4. -/
theorem pgdIterate_closedConvex_stronglyConvex_dist_sq_le_geometric
    (f : E → ℝ) (L : NNReal) (μ : ℝ)
    (hL : 0 < (L : ℝ)) (hμ : 0 ≤ μ) (hμL : μ ≤ (L : ℝ))
    (hDiff : ∀ z : E, HasGradientAt f (gradient f z) z)
    (hLip : LipschitzWith L (gradient f))
    (hStrong : IsMuStronglyConvex μ f)
    (C : Set E) (hne : C.Nonempty) (hclosed : IsClosed C)
    (hCconv : Convex ℝ C) {xstar : E} (hxstar : xstar ∈ C)
    (hmin : ∀ y ∈ C, f xstar ≤ f y) (x0 : E) (t : ℕ) :
    ‖pgdIterate_closedConvex (1 / (L : ℝ)) f C hne hclosed hCconv x0 t
        - xstar‖ ^ 2
      ≤ (1 - μ / (L : ℝ)) ^ t * ‖x0 - xstar‖ ^ 2 := by
  -- The contraction factor `1 - μ/L` is in `[0, 1]` under `hμ` and `hμL`.
  have hfactor_nonneg : 0 ≤ 1 - μ / (L : ℝ) := by
    have hμL' : μ / (L : ℝ) ≤ 1 := by
      rw [div_le_one hL]; exact hμL
    linarith
  -- Induction on `t`.
  induction t with
  | zero =>
      -- `pgdIterate ... 0 = x0` by definition; `(·)^0 = 1`.
      simp [pgdIterate_closedConvex]
  | succ k ih =>
      -- Let `xk := pgdIterate ... k`.  Per-step contraction at `xk`:
      --   ‖x_{k+1} - xstar‖² ≤ (1 - μ/L) · ‖xk - xstar‖².
      set xk : E :=
        pgdIterate_closedConvex (1 / (L : ℝ)) f C hne hclosed hCconv x0 k
        with hxk_def
      have hstep :
          ‖pgdStep_closedConvex (1 / (L : ℝ)) f C hne hclosed hCconv xk
              - xstar‖ ^ 2
            ≤ (1 - μ / (L : ℝ)) * ‖xk - xstar‖ ^ 2 :=
        pgdStep_closedConvex_stronglyConvex_dist_sq_le
          f L μ hL hμ hDiff hLip hStrong C hne hclosed hCconv hxstar hmin xk
      -- Chain through IH: multiply by `(1 - μ/L) ≥ 0`.
      have hchain :
          (1 - μ / (L : ℝ)) * ‖xk - xstar‖ ^ 2
            ≤ (1 - μ / (L : ℝ)) * ((1 - μ / (L : ℝ)) ^ k
                * ‖x0 - xstar‖ ^ 2) :=
        mul_le_mul_of_nonneg_left ih hfactor_nonneg
      -- Rewrite the `succ`-step iterate and the geometric factor.
      have hsucc :
          pgdIterate_closedConvex (1 / (L : ℝ)) f C hne hclosed hCconv x0
              (k + 1)
            = pgdStep_closedConvex (1 / (L : ℝ)) f C hne hclosed hCconv xk :=
        pgdIterate_closedConvex_succ
          (1 / (L : ℝ)) f C hne hclosed hCconv x0 k
      have hpow :
          (1 - μ / (L : ℝ)) ^ (k + 1)
            = (1 - μ / (L : ℝ)) * (1 - μ / (L : ℝ)) ^ k := by
        rw [pow_succ]; ring
      calc
        ‖pgdIterate_closedConvex (1 / (L : ℝ)) f C hne hclosed hCconv x0
              (k + 1) - xstar‖ ^ 2
            = ‖pgdStep_closedConvex (1 / (L : ℝ)) f C hne hclosed hCconv xk
                  - xstar‖ ^ 2 := by rw [hsucc]
        _ ≤ (1 - μ / (L : ℝ)) * ‖xk - xstar‖ ^ 2 := hstep
        _ ≤ (1 - μ / (L : ℝ)) * ((1 - μ / (L : ℝ)) ^ k
                * ‖x0 - xstar‖ ^ 2) := hchain
        _ = (1 - μ / (L : ℝ)) ^ (k + 1) * ‖x0 - xstar‖ ^ 2 := by
              rw [hpow]; ring

end LTFP
