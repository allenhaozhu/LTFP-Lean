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
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

namespace LTFP

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

end OrthogonalProjectionCore

end LTFP
