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

/-- §5.1 — Abstract L-smoothness descent lemma.

If `f : E → ℝ` satisfies the L-smooth quadratic upper bound
(Bach 2024 §5.1, eqn 5.4) and the step size `η ≥ 0` is admissible
(`L η ≤ 2`, equivalently `1 − L η / 2 ≥ 0`), then the gradient step
strictly decreases `f` by at least `η (1 − L η / 2) · ‖∇f(x)‖²`:
`f(x − η ∇f(x)) ≤ f(x) − η (1 − L η / 2) · ‖∇f(x)‖²`.

The hypothesis `hQ` is the L-smooth quadratic upper bound, which
follows from `LipschitzWith L (gradient f)` via Taylor's theorem
(Mathlib gap, see file docstring). -/
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

/-- §5.1 — L-smoothness descent lemma from `LipschitzWith` gradient.

If `f : E → ℝ` has an `L`-Lipschitz gradient (`hLip`) and satisfies the
L-smooth quadratic upper bound (`hTaylor`, the Mathlib Taylor-bridge
gap), then the gradient step at any admissible step size `η`
decreases `f` by at least `η (1 − L η / 2) · ‖∇f(x)‖²`:
`f(x − η ∇f(x)) ≤ f(x) − η (1 − L η / 2) · ‖∇f(x)‖²`.

This is the L-smoothness descent lemma of Bach (2024) §5.1, with the
Lipschitz-of-gradient witness exposed at the type level. The
`hLip` hypothesis is unused in the proof (the conclusion follows from
`hTaylor` alone via `gd_descent_lemma_of_quadratic_bound`), but its
presence pins the L-smoothness constant `L` to the gradient's
Lipschitz constant, which is what Bach's textbook statement actually
asserts. When Mathlib closes the Taylor-bridge gap, `hTaylor` will be
derivable from `hLip` and disappear from this signature. -/
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

end LTFP
