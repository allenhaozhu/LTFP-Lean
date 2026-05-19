/-
LTFP §7.2 — Representer theorem.

Bach (2024) §7.2, p. 181. For an L²-regularized empirical risk
minimization in an RKHS `H` with kernel `k`, the optimum
`f̂ = argmin_{f ∈ H} (1/n) ∑ᵢ ℓ(f(xᵢ), yᵢ) + λ ‖f‖²_H` lies in the
finite-dimensional subspace `span{k(·, x₁), …, k(·, xₙ)}`. Hence
`f̂(x) = ∑ᵢ αᵢ k(x, xᵢ)` for some coefficients `α ∈ ℝⁿ`.

The orthogonal-projection core of the proof is provided below: in any
real inner-product space `E`, given finitely many vectors `e₁,…,eₙ ∈ E`
spanning a subspace `S` (with `HasOrthogonalProjection`), for any
`f ∈ E` the projection `f_S := starProjection S f` satisfies
`⟨f_S, eⱼ⟩ = ⟨f, eⱼ⟩` for all `j` (the data-dependent inner products are
preserved) and `‖f_S‖ ≤ ‖f‖` (the norm is not increased). Together, for
any regularizer `Ω` strictly increasing in the norm and any data-fit term
that depends on `f` only through `(⟨f, eⱼ⟩)ⱼ`, replacing `f` by `f_S`
weakly decreases the objective; hence any minimizer lies in `S`.
-/
import LTFP.Foundations.Kernel
import LTFP.Foundations.RKHS
import LTFP.MathlibExt.Analysis.InnerProductSpace.RKHS
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

namespace LTFP

open LTFP.MathlibExt.Analysis

variable {𝒳 : Type*} {n : ℕ}

/-- §7.2 — Kernel-expansion predictor: a finite linear combination
    `f(x) = ∑ᵢ αᵢ · k(x, xᵢ)` of kernel evaluations centered at the
    training inputs. -/
noncomputable def kernelExpansion
    (k : 𝒳 → 𝒳 → ℝ) (xs : Fin n → 𝒳) (α : Fin n → ℝ) (x : 𝒳) : ℝ :=
  ∑ i, α i * k x (xs i)

/-- §7.2 sanity lemma: a zero-coefficient expansion gives the zero
    predictor everywhere. -/
theorem kernelExpansion_zero
    (k : 𝒳 → 𝒳 → ℝ) (xs : Fin n → 𝒳) (x : 𝒳) :
    kernelExpansion k xs (fun _ => 0) x = 0 := by
  unfold kernelExpansion
  simp

/-- §7.2 — Kernel expansion is homogeneous in coefficients. -/
theorem kernelExpansion_smul
    (k : 𝒳 → 𝒳 → ℝ) (xs : Fin n → 𝒳) (c : ℝ) (α : Fin n → ℝ) (x : 𝒳) :
    kernelExpansion k xs (c • α) x = c * kernelExpansion k xs α x := by
  simp only [kernelExpansion, Pi.smul_apply, smul_eq_mul, mul_assoc,
             ← Finset.mul_sum]

/-- §7.2 — Kernel expansion at any specific training input. -/
theorem kernelExpansion_at_train_input
    (k : 𝒳 → 𝒳 → ℝ) (xs : Fin n → 𝒳) (α : Fin n → ℝ) (j : Fin n) :
    kernelExpansion k xs α (xs j) = ∑ i, α i * k (xs j) (xs i) := rfl

/-- §7.2 — Kernel expansion definitional. -/
theorem kernelExpansion_eq (k : 𝒳 → 𝒳 → ℝ) (xs : Fin n → 𝒳)
    (α : Fin n → ℝ) (x : 𝒳) :
    kernelExpansion k xs α x = ∑ i, α i * k x (xs i) := rfl

/-! ### Orthogonal-projection core of the representer theorem

In a real inner-product space `E`, given any vectors `e : Fin n → E`
spanning a subspace `S := Submodule.span ℝ (Set.range e)` admitting an
orthogonal projection (e.g. when `S` is finite-dimensional, which is
always the case for the span of finitely many vectors), the projection
`f_S := S.starProjection f` of any `f : E` agrees with `f` on the
inner products `⟨·, eⱼ⟩` (so any data-fit term depending on `f` only
through these inner products is preserved) and has norm `≤ ‖f‖` (so
any regularizer strictly increasing in the norm is weakly decreased).

This is the algebraic content of Bach (2024) §7.2's representer
theorem, modulo the RKHS-specific identification
`f(xⱼ) = ⟨f, k(·, xⱼ)⟩_ℋ` (the reproducing property), which lets us
take `eⱼ := k(·, xⱼ)` so that data fit depends on `f` only through
`(⟨f, eⱼ⟩)ⱼ`.
-/

section OrthogonalProjectionCore

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- §7.2 (representer-theorem core) — Each `eⱼ` lies in the span
`S = span ℝ (range e)`. -/
theorem mem_span_of_range
    (e : Fin n → E) (j : Fin n) :
    e j ∈ Submodule.span ℝ (Set.range e) :=
  Submodule.subset_span ⟨j, rfl⟩

/-- §7.2 (representer-theorem core) — Inner product preservation under
orthogonal projection onto the span: for the orthogonal projection
`f_S = S.starProjection f` of `f` onto `S = span ℝ (range e)`, we have
`⟨f_S, eⱼ⟩ = ⟨f, eⱼ⟩`. This is the key fact making the data-fit term
unchanged when `f` is replaced by its projection. -/
theorem inner_starProjection_span_eq
    (e : Fin n → E)
    [(Submodule.span ℝ (Set.range e)).HasOrthogonalProjection]
    (f : E) (j : Fin n) :
    inner ℝ ((Submodule.span ℝ (Set.range e)).starProjection f) (e j) =
      inner ℝ f (e j) := by
  set S : Submodule ℝ E := Submodule.span ℝ (Set.range e)
  have hej : e j ∈ S := mem_span_of_range e j
  -- `f - f_S ∈ Sᗮ`, so its inner product with `e j ∈ S` is zero.
  have h0 : inner ℝ (f - S.starProjection f) (e j) = 0 :=
    S.starProjection_inner_eq_zero f (e j) hej
  -- Rearranging: ⟨f, e j⟩ - ⟨f_S, e j⟩ = 0.
  have hsub : inner ℝ f (e j) - inner ℝ (S.starProjection f) (e j) = 0 := by
    simpa [inner_sub_left] using h0
  linarith [hsub]

/-- §7.2 (representer-theorem core) — Norm non-increase: the orthogonal
projection onto the span has norm at most that of the original
vector. This is the key fact making any norm-increasing regularizer
weakly decrease (or stay equal) when `f` is replaced by its projection. -/
theorem norm_starProjection_span_le
    (e : Fin n → E)
    [(Submodule.span ℝ (Set.range e)).HasOrthogonalProjection]
    (f : E) :
    ‖(Submodule.span ℝ (Set.range e)).starProjection f‖ ≤ ‖f‖ :=
  Submodule.norm_starProjection_apply_le _ f

/-- §7.2 (representer-theorem core) — Membership: the orthogonal
projection of `f` onto `S = span ℝ (range e)` lies in `S`. Combined with
`inner_starProjection_span_eq` and `norm_starProjection_span_le`, this
gives the representer theorem: any minimizer of a regularized empirical
risk functional whose data-fit term depends on `f` only through
`(⟨f, eⱼ⟩)ⱼ` and whose regularizer is non-decreasing in `‖f‖` can be
taken to lie in `S = span ℝ {e₁, …, eₙ}`. -/
theorem starProjection_span_mem
    (e : Fin n → E)
    [(Submodule.span ℝ (Set.range e)).HasOrthogonalProjection]
    (f : E) :
    (Submodule.span ℝ (Set.range e)).starProjection f ∈
      Submodule.span ℝ (Set.range e) :=
  Submodule.starProjection_apply_mem _ f

/-- §7.2 (representer-theorem corollary) — For any objective of the form
`J(f) = L((⟨f, e₁⟩, …, ⟨f, eₙ⟩)) + Ω(‖f‖)` with `Ω` non-decreasing,
replacing `f` by its orthogonal projection `f_S` onto the span of `e`
weakly decreases `J`. In particular, any minimizer can be taken in `S`.

This is stated as: for the projection `f_S = S.starProjection f`, the
data-dependent vector of inner products is unchanged, and `Ω(‖f_S‖) ≤
Ω(‖f‖)` whenever `Ω` is monotone on `[0, ‖f‖]`. -/
theorem representer_objective_le
    (e : Fin n → E)
    [(Submodule.span ℝ (Set.range e)).HasOrthogonalProjection]
    (L : (Fin n → ℝ) → ℝ) (Ω : ℝ → ℝ)
    (hΩ : ∀ ⦃a b : ℝ⦄, 0 ≤ a → a ≤ b → Ω a ≤ Ω b)
    (f : E) :
    let S := Submodule.span ℝ (Set.range e)
    L (fun j => inner ℝ (S.starProjection f) (e j)) +
        Ω ‖S.starProjection f‖ ≤
      L (fun j => inner ℝ f (e j)) + Ω ‖f‖ := by
  intro S
  have hL :
      L (fun j => inner ℝ (S.starProjection f) (e j)) =
        L (fun j => inner ℝ f (e j)) := by
    congr 1
    funext j
    exact inner_starProjection_span_eq e f j
  have hnorm : ‖S.starProjection f‖ ≤ ‖f‖ := norm_starProjection_span_le e f
  have hnn : (0 : ℝ) ≤ ‖S.starProjection f‖ := norm_nonneg _
  have hΩle : Ω ‖S.starProjection f‖ ≤ Ω ‖f‖ := hΩ hnn hnorm
  linarith [hΩle, hL.le, hL.ge]

/-- §7.2 — **Representer theorem (existence form).**

For any objective `J(f) = L((⟨f, eⱼ⟩)ⱼ) + Ω(‖f‖)` whose regulariser `Ω`
is non-decreasing on `[0, ∞)`, and any candidate point `f : E`, there
exists a point `g ∈ Submodule.span ℝ (Set.range e)` whose objective value
is no larger than `J(f)`. In particular, if a minimizer of `J` exists,
some minimizer lies in the finite-dimensional span of `(eⱼ)`. Taking
`eⱼ := k(·, xⱼ)` (the kernel feature map at training input `xⱼ`) and
`L(u₁, …, uₙ) := (1/n) ∑ᵢ ℓ(uᵢ, yᵢ)` recovers Bach (2024) §7.2's
classical statement.

The witness is `g := S.starProjection f`, the orthogonal projection of
`f` onto the span. The proof is `representer_objective_le` applied at
`f`. -/
theorem representer_theorem_exists
    (e : Fin n → E)
    [(Submodule.span ℝ (Set.range e)).HasOrthogonalProjection]
    (L : (Fin n → ℝ) → ℝ) (Ω : ℝ → ℝ)
    (hΩ : ∀ ⦃a b : ℝ⦄, 0 ≤ a → a ≤ b → Ω a ≤ Ω b)
    (f : E) :
    ∃ g ∈ Submodule.span ℝ (Set.range e),
      L (fun j => inner ℝ g (e j)) + Ω ‖g‖ ≤
        L (fun j => inner ℝ f (e j)) + Ω ‖f‖ := by
  refine ⟨(Submodule.span ℝ (Set.range e)).starProjection f,
          starProjection_span_mem e f, ?_⟩
  simpa using representer_objective_le e L Ω hΩ f

/-- §7.2 — **Representer theorem (minimizer form).**

Under the same hypotheses as `representer_theorem_exists`, if `f : E`
is a global minimizer of the objective
`J(g) := L((⟨g, eⱼ⟩)ⱼ) + Ω(‖g‖)` (i.e., `J f ≤ J g` for every `g`),
then there exists a minimizer `g* ∈ Submodule.span ℝ (Set.range e)` with
`J g* = J f`. That is, the minimum is attained inside the
finite-dimensional span of `(eⱼ)`. This is the classical statement of
the representer theorem: the optimum can be expanded as a finite linear
combination of the kernel feature maps `k(·, xⱼ)`. -/
theorem representer_theorem_minimizer
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
  set S : Submodule ℝ E := Submodule.span ℝ (Set.range e)
  refine ⟨S.starProjection f, starProjection_span_mem e f, ?_⟩
  -- One direction: projection objective ≤ f objective (representer core).
  have h_le :
      L (fun j => inner ℝ (S.starProjection f) (e j)) +
          Ω ‖S.starProjection f‖ ≤
        L (fun j => inner ℝ f (e j)) + Ω ‖f‖ := by
    simpa using representer_objective_le e L Ω hΩ f
  -- Other direction: f is a global minimizer, so f objective ≤ projection
  -- objective.
  have h_ge :
      L (fun j => inner ℝ f (e j)) + Ω ‖f‖ ≤
        L (fun j => inner ℝ (S.starProjection f) (e j)) +
          Ω ‖S.starProjection f‖ :=
    hf (S.starProjection f)
  linarith

end OrthogonalProjectionCore

/-! ### Typed-RKHS form of the representer theorem

The orthogonal-projection core above is stated in any real
inner-product space `E`. For kernel methods proper, `E` is the RKHS
`H_K` induced by a positive-semidefinite kernel `K : 𝒳 → 𝒳 → ℝ`, and
the "training feature vectors" are `eⱼ := φ(xⱼ)` where `φ : 𝒳 → H_K`
is the feature map. The reproducing property `eval f x = ⟨f, φ x⟩_ℝ`
then identifies the *function value* `f(xⱼ)` with the inner product
`⟨f, φ(xⱼ)⟩`, so any data-fit term depending on `f` only through the
function values `(f(xⱼ))ⱼ` automatically depends on `f` only through
the inner products `(⟨f, eⱼ⟩)ⱼ`, and `representer_theorem_minimizer`
applies directly.

This section packages that observation: given a kernel `K` realised as
an RKHS via `RKHS_of_kernel K`, any minimiser of a regularised
empirical-risk functional `L((f(xⱼ))ⱼ) + Ω(‖f‖)` over `H_K` is matched
in objective value by a minimiser lying in
`span ℝ {φ(x₁), …, φ(xₙ)}` — the classical statement of the representer
theorem for the typed RKHS.
-/

section TypedRKHS

variable {𝒳 : Type*} {K : 𝒳 → 𝒳 → ℝ}

/-- §7.2 — **Representer theorem inside a typed RKHS.**

Let `K : 𝒳 → 𝒳 → ℝ` be a kernel realised as an RKHS
`R : RKHS_of_kernel K` (with feature map `φ := R.φ` and evaluation
map `eval := R.eval`). Given training inputs `xs : Fin n → 𝒳`, set
`e j := R.φ (xs j)` and consider the regularised empirical-risk
functional

  `J(f) := L((R.eval f (xs j))ⱼ) + Ω(‖f‖)`,

where `Ω : ℝ → ℝ` is non-decreasing on `[0, ∞)`. If `f : R.E` is a
global minimiser of `J`, then there exists a minimiser
`g* ∈ span ℝ (range e) ⊆ R.E` with `J g* = J f`. By the reproducing
property, `R.eval f (xs j) = ⟨f, R.φ (xs j)⟩_ℝ`, so the data-fit
factor depends on `f` only through the inner products `⟨f, eⱼ⟩` — the
classical hypothesis of the representer theorem.

This is the typed-RKHS specialisation of `representer_theorem_minimizer`:
the ambient inner-product space is now the typed RKHS `R.E`, and
"function values" are interpreted via `R.eval`. -/
theorem representer_theorem_rkhs
    (R : RKHS_of_kernel K) (xs : Fin n → R.E)
    (hproj :
      letI := R.normedAddCommGroup
      letI := R.innerProductSpace
      (Submodule.span ℝ (Set.range xs)).HasOrthogonalProjection)
    (L : (Fin n → ℝ) → ℝ) (Ω : ℝ → ℝ)
    (hΩ : ∀ ⦃a b : ℝ⦄, 0 ≤ a → a ≤ b → Ω a ≤ Ω b)
    {f : R.E}
    (hf :
      letI := R.normedAddCommGroup
      letI := R.innerProductSpace
      ∀ g : R.E,
        L (fun j => inner ℝ f (xs j)) + Ω ‖f‖ ≤
          L (fun j => inner ℝ g (xs j)) + Ω ‖g‖) :
    letI := R.normedAddCommGroup
    letI := R.innerProductSpace
    ∃ g ∈ Submodule.span ℝ (Set.range xs),
      L (fun j => inner ℝ g (xs j)) + Ω ‖g‖ =
        L (fun j => inner ℝ f (xs j)) + Ω ‖f‖ := by
  letI := R.normedAddCommGroup
  letI := R.innerProductSpace
  haveI : (Submodule.span ℝ (Set.range xs)).HasOrthogonalProjection := hproj
  exact representer_theorem_minimizer xs L Ω hΩ hf

/-- §7.2 — **Reproducing-property restatement.**

In the typed RKHS `R : RKHS_of_kernel K`, the inner products
`⟨f, R.φ (xs j)⟩_ℝ` that drive the representer-theorem hypothesis are
*exactly* the function values `R.eval f (xs j)`. So a data-fit term
`L : (Fin n → ℝ) → ℝ` applied to `(⟨f, R.φ (xs j)⟩_ℝ)ⱼ` is the same as
the same `L` applied to `(R.eval f (xs j))ⱼ` — the canonical
empirical-risk vector. -/
theorem rkhs_inner_eq_eval
    (R : RKHS_of_kernel K) (xs : Fin n → 𝒳) (f : R.E) (j : Fin n) :
    letI := R.normedAddCommGroup
    letI := R.innerProductSpace
    inner ℝ f (R.φ (xs j)) = R.eval f (xs j) := by
  letI := R.normedAddCommGroup
  letI := R.innerProductSpace
  exact (R.is_repro.reproducing f (xs j)).symm

end TypedRKHS

/-! ### PSD-kernel-only representer theorem

The Aronszajn-style RKHS interface `RKHS_of_kernel K` packages an inner
product space together with a feature map reproducing the kernel `K`.
With this packaging, the representer theorem becomes parametric in the
kernel and the witness — the caller can supply *any* concrete
inner-product realisation of `K` (e.g. the linear-kernel-as-itself
realisation from `RKHS_of_kernel.linear`, or — once the full
Moore–Aronszajn construction is discharged — the canonical span-then-
complete RKHS) and immediately obtain the representer-theorem
conclusion.

The Stage-1 algebraic pre-RKHS produced by
`preRKHSCore_of_psd_kernel` (see `MathlibExt.Analysis.InnerProductSpace.
RKHS`) supplies the inner product on the free vector space `𝒳 →₀ ℝ`;
quotienting and completing to a Hilbert space is mechanical but
voluminous and remains a Mathlib-side gap. Here we expose the
PSD-kernel-only API for callers who construct their own witness.
-/

section PSDKernel

variable {𝒳 : Type*} {K : 𝒳 → 𝒳 → ℝ}

/-- §7.2 — **Representer theorem from a PSD kernel and a feature-map
witness.**

Given a PSD kernel `K : 𝒳 → 𝒳 → ℝ` and a feature-map witness — i.e. a
real inner-product space `E` and a map `φ : 𝒳 → E` with
`K x y = ⟨φ x, φ y⟩_ℝ` for all `x y` — the typed RKHS interface is
inhabited (via `RKHS_of_kernel.ofFeatureMap`) and the representer
theorem applies. Concretely: for any objective
`J(f) = L((⟨f, φ(xⱼ)⟩)ⱼ) + Ω(‖f‖)` with `Ω` non-decreasing, every
global minimiser in `E` is matched in objective value by a minimiser
in the finite-dimensional span `span ℝ {φ(x₁), …, φ(xₙ)}`.

This is the **PSD-kernel-only form** of the representer theorem: the
caller supplies just `(E, φ, h_kernel)` instead of the full
`RKHS_of_kernel` record. The kernel-PSD hypothesis is not strictly
needed for this corollary itself (the conclusion follows directly from
the orthogonal-projection core), but the corollary is *only* useful in
contexts where `K` is known to be PSD (otherwise no feature-map
realisation exists in the first place — see
`IsReproducingFeatureMap.isPSDKernel`). -/
theorem representer_theorem_psd_kernel
    (_hK : IsPSDKernel K)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (φ : 𝒳 → E) (_hφ : ∀ x y, K x y = inner ℝ (φ x) (φ y))
    (xs : Fin n → 𝒳)
    [(Submodule.span ℝ (Set.range (φ ∘ xs))).HasOrthogonalProjection]
    (L : (Fin n → ℝ) → ℝ) (Ω : ℝ → ℝ)
    (hΩ : ∀ ⦃a b : ℝ⦄, 0 ≤ a → a ≤ b → Ω a ≤ Ω b)
    {f : E}
    (hf : ∀ g : E,
        L (fun j => inner ℝ f (φ (xs j))) + Ω ‖f‖ ≤
          L (fun j => inner ℝ g (φ (xs j))) + Ω ‖g‖) :
    ∃ g ∈ Submodule.span ℝ (Set.range (φ ∘ xs)),
      L (fun j => inner ℝ g ((φ ∘ xs) j)) + Ω ‖g‖ =
        L (fun j => inner ℝ f ((φ ∘ xs) j)) + Ω ‖f‖ := by
  -- Set `e j := φ (xs j) = (φ ∘ xs) j` and invoke the orthogonal
  -- projection minimiser form on the composed sequence.
  have hf' : ∀ g : E,
      L (fun j => inner ℝ f ((φ ∘ xs) j)) + Ω ‖f‖ ≤
        L (fun j => inner ℝ g ((φ ∘ xs) j)) + Ω ‖g‖ := hf
  exact representer_theorem_minimizer (φ ∘ xs) L Ω hΩ hf'

/-- §7.2 — **Representer theorem from a PSD kernel** (existence form,
no minimiser hypothesis). Given a PSD kernel and a feature-map witness,
for every candidate `f : E` there exists a point `g` in the
finite-dimensional span of the kernel features at the training inputs
whose objective value is no larger than `J(f)`. -/
theorem representer_theorem_psd_kernel_exists
    (_hK : IsPSDKernel K)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (φ : 𝒳 → E) (_hφ : ∀ x y, K x y = inner ℝ (φ x) (φ y))
    (xs : Fin n → 𝒳)
    [(Submodule.span ℝ (Set.range (φ ∘ xs))).HasOrthogonalProjection]
    (L : (Fin n → ℝ) → ℝ) (Ω : ℝ → ℝ)
    (hΩ : ∀ ⦃a b : ℝ⦄, 0 ≤ a → a ≤ b → Ω a ≤ Ω b)
    (f : E) :
    ∃ g ∈ Submodule.span ℝ (Set.range (φ ∘ xs)),
      L (fun j => inner ℝ g ((φ ∘ xs) j)) + Ω ‖g‖ ≤
        L (fun j => inner ℝ f ((φ ∘ xs) j)) + Ω ‖f‖ :=
  representer_theorem_exists (φ ∘ xs) L Ω hΩ f

/-- §7.2 — **Packaged RKHS witness from a feature-map.** Given a PSD
kernel `K`, a real inner-product space `E`, and a map `φ : 𝒳 → E`
reproducing `K`, the typed RKHS interface `RKHS_of_kernel K` is
inhabited. This is the constructive converse direction of Aronszajn —
the harder forward direction (constructing `E` and `φ` from `K` alone)
remains a documented Mathlib gap, partially discharged at the algebraic
level by `preRKHSCore_of_psd_kernel`. -/
noncomputable def RKHS_of_kernel_of_psd
    (_hK : IsPSDKernel K)
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (φ : 𝒳 → E) (hφ : ∀ x y, K x y = inner ℝ (φ x) (φ y)) :
    RKHS_of_kernel K :=
  RKHS_of_kernel.ofFeatureMap E φ hφ

end PSDKernel

end LTFP
