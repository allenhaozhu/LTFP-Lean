/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Reproducing kernel Hilbert spaces (RKHS)

A function `K : X × X → ℝ` is a positive semidefinite kernel if the Gram
matrix `K(xᵢ, xⱼ)` is PSD for every finite sample. By Moore-Aronszajn,
to every such `K` there is a unique RKHS `ℋ_K` of functions `X → ℝ`
with `K(·, x) ∈ ℋ_K` and the reproducing property `⟨f, K(·, x)⟩ = f(x)`.

The full Moore-Aronszajn construction (functional analytic completion of
the span of `{K(·, x) : x ∈ X}` under the inner product
`⟪K(·, x), K(·, y)⟫ := K(x, y)`) is a documented gap; this module
supplies the **finite-dimensional algebraic content** that downstream
theorems (e.g. the representer theorem for kernel ridge regression) need.

## Main definitions

* `IsSymmetricKernel` : a kernel function `K : X → X → ℝ` is symmetric.
* `IsPSDKernel` : a kernel function `K : X → X → ℝ` is positive
  semidefinite, in the sense that every finite Gram matrix is PSD.

## Main results

* `linear_kernel` and `linear_kernel_psd` : the standard inner product
  on `EuclideanSpace ℝ (Fin d)` is a symmetric PSD kernel.
* `sum_kernel`, `sum_kernel_psd`, `scale_kernel_psd` : pointwise sums of
  kernels are kernels, and nonneg scaling preserves the PSD property.
* `representer_projection_preserves_data` : in any real inner-product
  space, given training points `(eᵢ)`, orthogonally projecting any
  point `f` onto `span {eᵢ}` does not change the inner products
  `⟨f, eⱼ⟩`. This is the algebraic core of the representer theorem for
  kernel-based regularised least squares.
* `representer_projection_norm_le` : the orthogonal projection used in
  the representer theorem does not increase the norm, hence it strictly
  improves any rotation-invariant regulariser of the form `‖·‖²`.
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Tactic.Linarith

open scoped InnerProductSpace

namespace LTFP.MathlibExt.Analysis

/-- A kernel function `K : X → X → ℝ` is symmetric if `K x y = K y x`
for every pair of points. -/
def IsSymmetricKernel {X : Type*} (K : X → X → ℝ) : Prop :=
  ∀ x y, K x y = K y x

/-- A kernel function `K : X → X → ℝ` is positive semidefinite (PSD) if
every finite Gram matrix is PSD, i.e. for any `n`, any sample
`(xᵢ : Fin n → X)`, and any coefficient vector `(αᵢ : Fin n → ℝ)`,
the quadratic form `∑ᵢⱼ αᵢ αⱼ K(xᵢ, xⱼ)` is nonneg. -/
def IsPSDKernel {X : Type*} (K : X → X → ℝ) : Prop :=
  ∀ (n : ℕ) (x : Fin n → X) (α : Fin n → ℝ),
    0 ≤ ∑ i, ∑ j, α i * α j * K (x i) (x j)

/-- The linear (inner-product) kernel on `EuclideanSpace ℝ (Fin d)` is
symmetric: this is just the symmetry of the real inner product. -/
theorem linear_kernel (d : ℕ) :
    IsSymmetricKernel
      (fun u v : EuclideanSpace ℝ (Fin d) => ⟪u, v⟫_ℝ) := by
  intro u v
  exact real_inner_comm v u

/-- The linear (inner-product) kernel on `EuclideanSpace ℝ (Fin d)` is
positive semidefinite. The proof rewrites the Gram quadratic form as
`‖∑ᵢ αᵢ xᵢ‖²`, which is nonneg. -/
theorem linear_kernel_psd (d : ℕ) :
    IsPSDKernel
      (fun u v : EuclideanSpace ℝ (Fin d) => ⟪u, v⟫_ℝ) := by
  intro n x α
  -- Rewrite `∑ᵢⱼ αᵢ αⱼ ⟨xᵢ, xⱼ⟩` as `⟨∑ᵢ αᵢ xᵢ, ∑ⱼ αⱼ xⱼ⟩` and then
  -- as `‖∑ᵢ αᵢ xᵢ‖²`.
  set y : EuclideanSpace ℝ (Fin d) := ∑ i, α i • x i with hy
  have h_inner :
      ⟪y, y⟫_ℝ = ∑ i, ∑ j, α i * α j * ⟪x i, x j⟫_ℝ := by
    -- Expand both sums and pull out the scalars.
    have h1 : ⟪y, y⟫_ℝ = ∑ i, ⟪α i • x i, y⟫_ℝ := by
      rw [hy]; exact sum_inner (𝕜 := ℝ) Finset.univ (fun i => α i • x i) y
    have h2 : ∀ i,
        ⟪α i • x i, y⟫_ℝ
          = α i * ∑ j, α j * ⟪x i, x j⟫_ℝ := by
      intro i
      have hsmul :
          ⟪α i • x i, y⟫_ℝ = α i * ⟪x i, y⟫_ℝ := by
        simpa using (real_inner_smul_left (x i) y (α i))
      have hsum :
          ⟪x i, y⟫_ℝ = ∑ j, α j * ⟪x i, x j⟫_ℝ := by
        rw [hy, inner_sum (𝕜 := ℝ) Finset.univ (fun j => α j • x j) (x i)]
        refine Finset.sum_congr rfl ?_
        intro j _
        simpa using (real_inner_smul_right (x i) (x j) (α j))
      rw [hsmul, hsum]
    calc
      ⟪y, y⟫_ℝ
          = ∑ i, ⟪α i • x i, y⟫_ℝ := h1
      _   = ∑ i, α i * ∑ j, α j * ⟪x i, x j⟫_ℝ := by
              refine Finset.sum_congr rfl ?_
              intro i _; exact h2 i
      _   = ∑ i, ∑ j, α i * (α j * ⟪x i, x j⟫_ℝ) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              exact Finset.mul_sum _ _ _
      _   = ∑ i, ∑ j, α i * α j * ⟪x i, x j⟫_ℝ := by
              refine Finset.sum_congr rfl ?_
              intro i _
              refine Finset.sum_congr rfl ?_
              intro j _; ring
  have h_nonneg : 0 ≤ ⟪y, y⟫_ℝ := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_nonneg _
  -- Conclude by rewriting the goal as `0 ≤ ⟪y, y⟫_ℝ`.
  have h_goal :
      ∑ i, ∑ j, α i * α j * ⟪x i, x j⟫_ℝ = ⟪y, y⟫_ℝ := h_inner.symm
  rw [show
        (∑ i, ∑ j, α i * α j *
          (fun u v : EuclideanSpace ℝ (Fin d) => ⟪u, v⟫_ℝ) (x i) (x j))
          = ∑ i, ∑ j, α i * α j * ⟪x i, x j⟫_ℝ from rfl,
      h_goal]
  exact h_nonneg

/-- The pointwise sum of two symmetric kernels is symmetric. -/
theorem sum_kernel {X : Type*} (K₁ K₂ : X → X → ℝ)
    (h₁ : IsSymmetricKernel K₁) (h₂ : IsSymmetricKernel K₂) :
    IsSymmetricKernel (fun x y => K₁ x y + K₂ x y) := by
  intro x y
  show K₁ x y + K₂ x y = K₁ y x + K₂ y x
  rw [h₁ x y, h₂ x y]

/-- The pointwise sum of two PSD kernels is PSD: the Gram quadratic form
of the sum is the sum of two nonneg Gram quadratic forms. -/
theorem sum_kernel_psd {X : Type*} (K₁ K₂ : X → X → ℝ)
    (h₁ : IsPSDKernel K₁) (h₂ : IsPSDKernel K₂) :
    IsPSDKernel (fun x y => K₁ x y + K₂ x y) := by
  intro n x α
  have hsplit :
      ∑ i, ∑ j, α i * α j * (K₁ (x i) (x j) + K₂ (x i) (x j))
        = (∑ i, ∑ j, α i * α j * K₁ (x i) (x j))
            + ∑ i, ∑ j, α i * α j * K₂ (x i) (x j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro j _; ring
  rw [show
        (∑ i, ∑ j, α i * α j *
          (fun x y => K₁ x y + K₂ x y) (x i) (x j))
          = ∑ i, ∑ j, α i * α j * (K₁ (x i) (x j) + K₂ (x i) (x j)) from rfl,
      hsplit]
  exact add_nonneg (h₁ n x α) (h₂ n x α)

/-- A nonneg scaling of a PSD kernel is still PSD: the scalar simply
factors out of the Gram quadratic form. -/
theorem scale_kernel_psd {X : Type*} (K : X → X → ℝ) (c : ℝ)
    (hc : 0 ≤ c) (hK : IsPSDKernel K) :
    IsPSDKernel (fun x y => c * K x y) := by
  intro n x α
  have hfactor :
      ∑ i, ∑ j, α i * α j * (c * K (x i) (x j))
        = c * ∑ i, ∑ j, α i * α j * K (x i) (x j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _; ring
  rw [show
        (∑ i, ∑ j, α i * α j *
          (fun x y => c * K x y) (x i) (x j))
          = ∑ i, ∑ j, α i * α j * (c * K (x i) (x j)) from rfl,
      hfactor]
  exact mul_nonneg hc (hK n x α)

/-- **Representer theorem, algebraic core.**

In any real inner-product space `E`, given training points represented
as vectors `(eᵢ : Fin n → E)`, the orthogonal projection of any `f : E`
onto the finite-dimensional subspace `span ℝ {eᵢ}` does not change the
inner products with any training point. Hence any data-fit term that
only depends on the inner products `⟨f, eⱼ⟩` is invariant under
projection onto the training span — which combined with
`representer_projection_norm_le` shows that for any squared-norm
regulariser, the minimiser of `data_fit f + λ ‖f‖²` lies in the span of
the training data.

The argument is purely algebraic: `f - πf ⊥ eⱼ` since `eⱼ ∈ span e`,
hence `⟨πf, eⱼ⟩ = ⟨f, eⱼ⟩`. The `HasOrthogonalProjection` hypothesis is
used only to ensure the projection exists; it is automatic whenever the
span is complete (e.g. whenever `E` is finite-dimensional, or whenever a
`CompleteSpace ↥(Submodule.span ℝ (Set.range e))` instance is
registered via `FiniteDimensional.complete`). -/
theorem representer_projection_preserves_data
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (e : Fin n → E)
    [(Submodule.span ℝ (Set.range e)).HasOrthogonalProjection]
    (f : E) (j : Fin n) :
    ⟪(Submodule.span ℝ (Set.range e)).starProjection f, e j⟫_ℝ
      = ⟪f, e j⟫_ℝ := by
  -- `e j ∈ span ℝ (Set.range e)`.
  have hej : e j ∈ Submodule.span ℝ (Set.range e) :=
    Submodule.subset_span ⟨j, rfl⟩
  -- Push the projection across the inner product using self-adjointness
  -- and idempotence on members.
  have hsym :
      ⟪(Submodule.span ℝ (Set.range e)).starProjection f, e j⟫_ℝ
        = ⟪f, (Submodule.span ℝ (Set.range e)).starProjection (e j)⟫_ℝ :=
    Submodule.inner_starProjection_left_eq_right
      (Submodule.span ℝ (Set.range e)) f (e j)
  have hfix :
      (Submodule.span ℝ (Set.range e)).starProjection (e j) = e j :=
    (Submodule.starProjection_eq_self_iff
      (K := Submodule.span ℝ (Set.range e)) (v := e j)).mpr hej
  rw [hsym, hfix]

/-- **Representer theorem, norm-bound part.**

The orthogonal projection onto the training span is norm non-increasing:
`‖πf‖ ≤ ‖f‖`. Combined with `representer_projection_preserves_data`,
this shows that for any data-fit term depending only on
`⟨f, eⱼ⟩` and any squared-norm regulariser, replacing `f` by its
projection onto the training span weakly decreases the objective. -/
theorem representer_projection_norm_le
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (e : Fin n → E)
    [(Submodule.span ℝ (Set.range e)).HasOrthogonalProjection]
    (f : E) :
    ‖(Submodule.span ℝ (Set.range e)).starProjection f‖ ≤ ‖f‖ :=
  (Submodule.span ℝ (Set.range e)).norm_starProjection_apply_le f

/-- Convenience constructor: in any *complete* real inner-product space,
the span of finitely many points always has an orthogonal projection,
because it is finite-dimensional hence complete. This is the instance
the representer theorem expects in practice. -/
theorem hasOrthogonalProjection_span_range_of_complete
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {n : ℕ} (e : Fin n → E) :
    (Submodule.span ℝ (Set.range e)).HasOrthogonalProjection := by
  have hfin : Set.Finite (Set.range e) := Set.finite_range e
  haveI : FiniteDimensional ℝ (Submodule.span ℝ (Set.range e)) :=
    FiniteDimensional.span_of_finite ℝ hfin
  haveI : CompleteSpace (Submodule.span ℝ (Set.range e)) :=
    FiniteDimensional.complete ℝ _
  infer_instance

/-! ### Aronszajn-style typed RKHS structure

The classical Moore–Aronszajn theorem says: every positive-semidefinite
symmetric kernel `K : 𝒳 × 𝒳 → ℝ` induces a unique (up to isometric
isomorphism) real Hilbert space `H_K` of functions `𝒳 → ℝ`, equipped
with a **feature map** `φ : 𝒳 → H_K` and an **evaluation map**
`eval : H_K → 𝒳 → ℝ`, satisfying the *reproducing property*

  `eval f x = ⟨f, φ x⟩_{H_K}` for all `f ∈ H_K`, `x ∈ 𝒳`.

The construction (completion of `span ℝ {K(·, x) : x ∈ 𝒳}` under
`⟪K(·, x), K(·, y)⟫ := K(x, y)`) is functional-analytic in nature and
relies on Mathlib's `UniformSpace.Completion` machinery, which is a
documented Tier-C gap for this project.

To make the existing representer theorem (in `Ch07_Kernels.Representer`)
land against a *typed* RKHS — rather than an arbitrary ambient
inner-product space — we expose the following lightweight structures:

* `IsReproducingFeatureMap K E φ eval` : a Prop-valued predicate saying
  that `φ : 𝒳 → E` and `eval : E → 𝒳 → ℝ` jointly witness the
  reproducing property `eval f x = ⟨f, φ x⟩_ℝ`, and that the induced
  kernel equals `K`.

* `RKHS_of_kernel K` : a packaged record bundling an inner-product space
  `E`, a feature map `φ`, an evaluation map `eval`, and an
  `IsReproducingFeatureMap` proof.

Stage-1 deliverable: we register the predicate, prove the symmetric and
PSD-of-kernel corollaries that always follow from the reproducing
property (so the predicate is *non-vacuous*: any kernel admitting such a
realisation is automatically symmetric and PSD), and expose the typed
representer-friendly form. We do not prove the converse (Aronszajn's
existence/uniqueness theorem) here; that is Stage-3 territory.
-/

/-- **Reproducing-feature-map predicate.**

Given a kernel `K : 𝒳 → 𝒳 → ℝ`, a real inner-product space `E`, a
feature map `φ : 𝒳 → E`, and an evaluation map `eval : E → 𝒳 → ℝ`, we
say the data `(E, φ, eval)` is a reproducing realisation of `K` if
`eval` is linear in `f`, and the reproducing property holds:

  `eval f x = ⟨f, φ x⟩_ℝ` and `K x y = ⟨φ x, φ y⟩_ℝ`.

This is the *non-trivial content* of being an RKHS: a Hilbert space
together with feature and evaluation maps witnessing the reproducing
identity. -/
structure IsReproducingFeatureMap
    {𝒳 E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : 𝒳 → 𝒳 → ℝ) (φ : 𝒳 → E) (eval : E → 𝒳 → ℝ) : Prop where
  /-- Evaluation is the inner product with the feature image. -/
  reproducing : ∀ (f : E) (x : 𝒳), eval f x = ⟪f, φ x⟫_ℝ
  /-- The kernel is recovered from the feature map. -/
  kernel_eq : ∀ x y : 𝒳, K x y = ⟪φ x, φ y⟫_ℝ

/-- **Aronszajn-style RKHS record.**

A bundled witness that a kernel `K : 𝒳 → 𝒳 → ℝ` is realised as a
reproducing kernel inside some real inner-product space `E`. The record
exposes the underlying space `E`, the feature map `φ`, the evaluation
map `eval`, and the reproducing-property witness. Downstream theorems
(e.g. the representer theorem) accept an `RKHS_of_kernel K` and only
ever interact with `E` through inner products and projections.

This is the typed RKHS *interface* that the representer theorem
consumes; concrete instances (e.g. the linear kernel realised inside
`EuclideanSpace ℝ (Fin d)` itself) are constructed elsewhere. The full
Aronszajn theorem — that *every* PSD symmetric kernel admits such an
instance — is a documented Mathlib gap. -/
structure RKHS_of_kernel {𝒳 : Type*} (K : 𝒳 → 𝒳 → ℝ) where
  /-- The ambient inner-product space (= `H_K` in textbook notation). -/
  E : Type*
  /-- Additive-group structure on `E`. -/
  [normedAddCommGroup : NormedAddCommGroup E]
  /-- Inner-product structure on `E` over `ℝ`. -/
  [innerProductSpace : InnerProductSpace ℝ E]
  /-- The feature map `𝒳 → E`. -/
  φ : 𝒳 → E
  /-- The evaluation map: each `f : E` is realised as a function
  `eval f : 𝒳 → ℝ`. -/
  eval : E → 𝒳 → ℝ
  /-- Witness that `(E, φ, eval)` reproduces `K`. -/
  is_repro : IsReproducingFeatureMap K φ eval

namespace IsReproducingFeatureMap

variable {𝒳 E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {K : 𝒳 → 𝒳 → ℝ} {φ : 𝒳 → E} {eval : E → 𝒳 → ℝ}

/-- **Symmetry from reproducing property.** Any kernel realised as
`⟨φ x, φ y⟩_ℝ` is automatically symmetric in its arguments. -/
theorem isSymmetricKernel
    (h : IsReproducingFeatureMap K φ eval) : IsSymmetricKernel K := by
  intro x y
  rw [h.kernel_eq x y, h.kernel_eq y x, real_inner_comm]

/-- **PSD from reproducing property.** Any kernel realised as
`⟨φ x, φ y⟩_ℝ` is automatically positive semidefinite: the Gram
quadratic form equals `‖∑ᵢ αᵢ φ(xᵢ)‖² ≥ 0`. -/
theorem isPSDKernel
    (h : IsReproducingFeatureMap K φ eval) : IsPSDKernel K := by
  intro n x α
  -- Rewrite the Gram quadratic form using `K x y = ⟨φ x, φ y⟩`.
  have hrewrite :
      ∑ i, ∑ j, α i * α j * K (x i) (x j)
        = ∑ i, ∑ j, α i * α j * ⟪φ (x i), φ (x j)⟫_ℝ := by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [h.kernel_eq]
  -- The latter is `‖∑ αᵢ φ(xᵢ)‖² ≥ 0` by `linear_kernel_psd`'s argument.
  set y : E := ∑ i, α i • φ (x i) with hy
  have h_inner :
      ⟪y, y⟫_ℝ = ∑ i, ∑ j, α i * α j * ⟪φ (x i), φ (x j)⟫_ℝ := by
    have h1 : ⟪y, y⟫_ℝ = ∑ i, ⟪α i • φ (x i), y⟫_ℝ := by
      rw [hy]; exact sum_inner (𝕜 := ℝ) Finset.univ (fun i => α i • φ (x i)) y
    have h2 : ∀ i,
        ⟪α i • φ (x i), y⟫_ℝ
          = α i * ∑ j, α j * ⟪φ (x i), φ (x j)⟫_ℝ := by
      intro i
      have hsmul :
          ⟪α i • φ (x i), y⟫_ℝ = α i * ⟪φ (x i), y⟫_ℝ := by
        simpa using (real_inner_smul_left (φ (x i)) y (α i))
      have hsum :
          ⟪φ (x i), y⟫_ℝ = ∑ j, α j * ⟪φ (x i), φ (x j)⟫_ℝ := by
        rw [hy, inner_sum (𝕜 := ℝ) Finset.univ (fun j => α j • φ (x j)) (φ (x i))]
        refine Finset.sum_congr rfl ?_
        intro j _
        simpa using (real_inner_smul_right (φ (x i)) (φ (x j)) (α j))
      rw [hsmul, hsum]
    calc
      ⟪y, y⟫_ℝ
          = ∑ i, ⟪α i • φ (x i), y⟫_ℝ := h1
      _   = ∑ i, α i * ∑ j, α j * ⟪φ (x i), φ (x j)⟫_ℝ := by
              refine Finset.sum_congr rfl ?_
              intro i _; exact h2 i
      _   = ∑ i, ∑ j, α i * (α j * ⟪φ (x i), φ (x j)⟫_ℝ) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              exact Finset.mul_sum _ _ _
      _   = ∑ i, ∑ j, α i * α j * ⟪φ (x i), φ (x j)⟫_ℝ := by
              refine Finset.sum_congr rfl ?_
              intro i _
              refine Finset.sum_congr rfl ?_
              intro j _; ring
  have h_nonneg : 0 ≤ ⟪y, y⟫_ℝ := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_nonneg _
  rw [hrewrite, ← h_inner]
  exact h_nonneg

/-- **Evaluation at a feature point recovers the kernel.** For any
reproducing realisation of `K`, evaluating `φ y` at `x` gives `K y x`.
This is the "the feature `φ y` *is* the function `K(·, y)`" identity
when `eval (φ y) ·` is interpreted as a function `𝒳 → ℝ`. -/
theorem eval_feature_eq_kernel
    (h : IsReproducingFeatureMap K φ eval) (x y : 𝒳) :
    eval (φ y) x = K y x := by
  rw [h.reproducing, h.kernel_eq y x]

end IsReproducingFeatureMap

/-- **Canonical reproducing realisation of the linear kernel.**

The linear kernel `K u v := ⟨u, v⟩` on `EuclideanSpace ℝ (Fin d)` is
canonically realised inside `EuclideanSpace ℝ (Fin d)` itself, with
feature map `φ := id` and evaluation map `eval f x := ⟨f, x⟩`. This is
the simplest non-trivial Aronszajn-style witness and shows the
`RKHS_of_kernel` structure is inhabited for at least one concrete
kernel. -/
noncomputable def RKHS_of_kernel.linear (d : ℕ) :
    RKHS_of_kernel
      (fun u v : EuclideanSpace ℝ (Fin d) => ⟪u, v⟫_ℝ) where
  E := EuclideanSpace ℝ (Fin d)
  φ := id
  eval f x := ⟪f, x⟫_ℝ
  is_repro :=
    { reproducing := by intro f x; rfl
      kernel_eq := by intro x y; rfl }

/-! ### Aronszajn pre-RKHS construction (algebraic core)

The Moore–Aronszajn theorem produces, from any symmetric positive
semidefinite kernel `K : 𝒳 → 𝒳 → ℝ`, a Hilbert space of functions on
`𝒳` with a reproducing feature map. The construction proceeds in three
stages:

  1. **Algebraic pre-RKHS** — equip the free real vector space on `𝒳`,
     namely `𝒳 →₀ ℝ` (finitely-supported functions), with the bilinear
     form `⟪c, c'⟫_K := ∑_{x, y} c x * c' y * K x y`. The PSD condition
     on `K` is exactly the statement that this bilinear form is positive
     semidefinite, and the symmetry of `K` is exactly its symmetry. This
     yields a `PreInnerProductSpace.Core ℝ (𝒳 →₀ ℝ)` instance.

  2. **Quotient to inner-product space** — pass to the
     `SeparationQuotient` of the resulting seminormed space, getting an
     honest `InnerProductSpace ℝ`.

  3. **Completion to Hilbert space** — apply `UniformSpace.Completion`
     to obtain the full RKHS `H_K`.

Stage 1 (the algebraic core) is **discharged below**. Stages 2 and 3 are
mechanical applications of Mathlib's `SeparationQuotient` and
`UniformSpace.Completion` instances for inner-product spaces, but
threading the feature map and reproducing property through the quotient
and completion is a substantial bookkeeping exercise that we mark as a
known Mathlib-side gap (see `NEEDS_HELP` block in the module summary).

The downstream payoff of Stage 1 alone is significant: the
`PreInnerProductSpace.Core` produced here gives the seminorm
`‖∑ᵢ cᵢ K(·, xᵢ)‖_K = √(∑ᵢⱼ cᵢ cⱼ K xᵢ xⱼ)` that the representer
theorem and kernel-method analysis depend on at the algebraic level.
-/

open scoped BigOperators

/-- **Kernel Gram bilinear form on `𝒳 →₀ ℝ`.**

Given a kernel `K : 𝒳 → 𝒳 → ℝ`, the *kernel Gram form* of two
finitely-supported coefficient vectors `c c' : 𝒳 →₀ ℝ` is

  `⟪c, c'⟫_K := ∑_{x ∈ c.support} ∑_{y ∈ c'.support} c x * c' y * K x y`.

Viewing `c = ∑ᵢ cᵢ δ_{xᵢ}` as a formal linear combination of "kernel
sections" `K(·, xᵢ)`, this is exactly the candidate inner product
`⟪∑ᵢ cᵢ K(·, xᵢ), ∑ⱼ cⱼ' K(·, xⱼ)⟫ = ∑ᵢⱼ cᵢ cⱼ' K(xᵢ, xⱼ)` driving the
Aronszajn construction. -/
noncomputable def kernelGramForm {𝒳 : Type*} (K : 𝒳 → 𝒳 → ℝ)
    (c c' : 𝒳 →₀ ℝ) : ℝ :=
  ∑ x ∈ c.support, ∑ y ∈ c'.support, c x * c' y * K x y

namespace kernelGramForm

variable {𝒳 : Type*} (K : 𝒳 → 𝒳 → ℝ)

/-- The kernel Gram form vanishes when either argument is zero. -/
@[simp] theorem zero_left (c : 𝒳 →₀ ℝ) :
    kernelGramForm K 0 c = 0 := by
  unfold kernelGramForm
  simp

@[simp] theorem zero_right (c : 𝒳 →₀ ℝ) :
    kernelGramForm K c 0 = 0 := by
  unfold kernelGramForm
  simp

/-- The kernel Gram form can be re-summed over any larger finite set
than `c.support` and `c'.support` — outside the supports the
coefficients are zero. -/
theorem eq_sum_of_subset {𝒳 : Type*} (K : 𝒳 → 𝒳 → ℝ)
    (c c' : 𝒳 →₀ ℝ) {s t : Finset 𝒳}
    (hs : c.support ⊆ s) (ht : c'.support ⊆ t) :
    kernelGramForm K c c' =
      ∑ x ∈ s, ∑ y ∈ t, c x * c' y * K x y := by
  unfold kernelGramForm
  rw [Finset.sum_subset hs (by
        intro x hx hx'
        have : c x = 0 := Finsupp.notMem_support_iff.mp hx'
        simp [this])]
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [Finset.sum_subset ht (by
        intro y hy hy'
        have : c' y = 0 := Finsupp.notMem_support_iff.mp hy'
        simp [this])]

/-- **Symmetry of the Gram form** from symmetry of `K`. -/
theorem symm {𝒳 : Type*} {K : 𝒳 → 𝒳 → ℝ} (hK : IsSymmetricKernel K)
    (c c' : 𝒳 →₀ ℝ) :
    kernelGramForm K c c' = kernelGramForm K c' c := by
  -- Switch the order of summation and use `K x y = K y x` plus
  -- commutativity of multiplication.
  unfold kernelGramForm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro y _
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [hK x y]; ring

/-- **Additivity (left).** The kernel Gram form is additive in its first
argument. -/
theorem add_left {𝒳 : Type*} (K : 𝒳 → 𝒳 → ℝ) (c₁ c₂ d : 𝒳 →₀ ℝ) :
    kernelGramForm K (c₁ + c₂) d =
      kernelGramForm K c₁ d + kernelGramForm K c₂ d := by
  classical
  -- Sum over a common finite set containing all three supports, then split.
  let s : Finset 𝒳 := (c₁ + c₂).support ∪ c₁.support ∪ c₂.support
  have hs_sum : (c₁ + c₂).support ⊆ s := by
    intro x hx
    exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have hs1 : c₁.support ⊆ s := by
    intro x hx
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have hs2 : c₂.support ⊆ s := by
    intro x hx
    exact Finset.mem_union_right _ hx
  rw [eq_sum_of_subset K (c₁ + c₂) d hs_sum (Finset.Subset.refl _),
      eq_sum_of_subset K c₁ d hs1 (Finset.Subset.refl _),
      eq_sum_of_subset K c₂ d hs2 (Finset.Subset.refl _)]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [Finsupp.add_apply]; ring

/-- **Additivity (right).** -/
theorem add_right {𝒳 : Type*} {K : 𝒳 → 𝒳 → ℝ}
    (hK : IsSymmetricKernel K) (c d₁ d₂ : 𝒳 →₀ ℝ) :
    kernelGramForm K c (d₁ + d₂) =
      kernelGramForm K c d₁ + kernelGramForm K c d₂ := by
  rw [symm hK c (d₁ + d₂), add_left K d₁ d₂ c,
      symm hK d₁ c, symm hK d₂ c]

/-- **Scalar homogeneity (left).** -/
theorem smul_left {𝒳 : Type*} (K : 𝒳 → 𝒳 → ℝ) (r : ℝ) (c d : 𝒳 →₀ ℝ) :
    kernelGramForm K (r • c) d = r * kernelGramForm K c d := by
  -- Sum over `c.support`; `(r • c).support ⊆ c.support`.
  have hsub : (r • c).support ⊆ c.support := Finsupp.support_smul
  rw [eq_sum_of_subset K (r • c) d hsub (Finset.Subset.refl _)]
  unfold kernelGramForm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro x _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [Finsupp.smul_apply, smul_eq_mul]; ring

/-- **Scalar homogeneity (right).** -/
theorem smul_right {𝒳 : Type*} {K : 𝒳 → 𝒳 → ℝ}
    (hK : IsSymmetricKernel K) (r : ℝ) (c d : 𝒳 →₀ ℝ) :
    kernelGramForm K c (r • d) = r * kernelGramForm K c d := by
  rw [symm hK c (r • d), smul_left K r d c, symm hK d c]

/-- **Reproducing identity on the basis.** The kernel Gram form of two
single-spike Finsupps `δ_x = single x 1` and `δ_y = single y 1` is
exactly `K x y`. This is the algebraic Aronszajn reproducing identity
on the canonical generators of the pre-RKHS. -/
theorem single_one_single_one {𝒳 : Type*} [DecidableEq 𝒳]
    (K : 𝒳 → 𝒳 → ℝ) (x y : 𝒳) :
    kernelGramForm K (Finsupp.single x (1 : ℝ)) (Finsupp.single y 1)
      = K x y := by
  -- Re-sum over the singleton sets `{x}` and `{y}` containing the supports.
  have hx : (Finsupp.single x (1 : ℝ)).support ⊆ ({x} : Finset 𝒳) :=
    Finsupp.support_single_subset
  have hy : (Finsupp.single y (1 : ℝ)).support ⊆ ({y} : Finset 𝒳) :=
    Finsupp.support_single_subset
  rw [eq_sum_of_subset K _ _ hx hy]
  -- Now the double sum is over `{x} × {y}`; reduce.
  rw [Finset.sum_singleton, Finset.sum_singleton]
  rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
  ring

/-- **Positive semidefiniteness of the Gram form** from PSD of `K`. -/
theorem nonneg_of_psd {𝒳 : Type*} {K : 𝒳 → 𝒳 → ℝ}
    (hK : IsPSDKernel K) (c : 𝒳 →₀ ℝ) :
    0 ≤ kernelGramForm K c c := by
  -- Enumerate `c.support` as a `Fin n → 𝒳` via `Finset.equivFin`, then
  -- apply `IsPSDKernel`.
  let s := c.support
  let n := s.card
  let e : s ≃ Fin n := s.equivFin
  let x : Fin n → 𝒳 := fun i => (e.symm i).val
  let α : Fin n → ℝ := fun i => c (x i)
  have hpsd := hK n x α
  -- Convert RHS `∑ i, ∑ j, α i * α j * K (x i) (x j)`
  --       = `∑ p : s, ∑ q : s, c p * c q * K p q` via `Equiv.sum_comp`
  --       = `∑ p ∈ s.attach, ∑ q ∈ s.attach, c p.val * ... ` (definition)
  --       = `∑ p ∈ s, ∑ q ∈ s, c p * c q * K p q` via `Finset.sum_attach`
  --       = `kernelGramForm K c c`.
  have h1 :
      ∑ i, ∑ j, α i * α j * K (x i) (x j)
        = ∑ p : s, ∑ q : s,
            c p.val * c q.val * K p.val q.val := by
    rw [← Equiv.sum_comp e.symm
          (fun p : s => ∑ q : s, c p.val * c q.val * K p.val q.val)]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [← Equiv.sum_comp e.symm
          (fun q : s => c (e.symm i).val * c q.val *
                        K (e.symm i).val q.val)]
  have h2 :
      ∑ p : s, ∑ q : s, c p.val * c q.val * K p.val q.val
        = ∑ p ∈ s, ∑ q ∈ s, c p * c q * K p q := by
    rw [← Finset.sum_attach s
          (fun p => ∑ q ∈ s, c p * c q * K p q),
        show (Finset.univ : Finset s) = s.attach
          from Finset.univ_eq_attach s]
    refine Finset.sum_congr rfl ?_
    intro p _
    rw [← Finset.sum_attach s
          (fun q => c p.val * c q * K p.val q)]
  rw [show kernelGramForm K c c
        = ∑ p ∈ s, ∑ q ∈ s, c p * c q * K p q from rfl,
      ← h2, ← h1]
  exact hpsd

end kernelGramForm

/-- **Pre-RKHS algebraic core.**

Given a symmetric PSD kernel `K : 𝒳 → 𝒳 → ℝ`, the free real vector
space `𝒳 →₀ ℝ` carries a positive semidefinite symmetric bilinear form
— the *kernel Gram form* — and hence satisfies Mathlib's
`PreInnerProductSpace.Core ℝ (𝒳 →₀ ℝ)` structure. This is **stage 1 of
the Moore–Aronszajn construction**: the algebraic pre-RKHS.

The remaining stages (quotient by the seminorm kernel to get a true
inner-product space, then completion to a Hilbert space) are mechanical
applications of `SeparationQuotient` and `UniformSpace.Completion` from
Mathlib's inner-product-space library; threading the feature map and
the reproducing identity through them is a known Mathlib-side gap
recorded in `PROGRESS.md` (Tier C, "Aronszajn RKHS uniqueness up to
isometry"). -/
noncomputable def preRKHSCore_of_psd_kernel
    {𝒳 : Type*} {K : 𝒳 → 𝒳 → ℝ}
    (hsym : IsSymmetricKernel K) (hpsd : IsPSDKernel K) :
    PreInnerProductSpace.Core ℝ (𝒳 →₀ ℝ) where
  inner := fun c c' => kernelGramForm K c c'
  conj_inner_symm := by
    intro c c'
    -- Real-valued symmetry; `conj` on ℝ is identity.
    show (kernelGramForm K c' c : ℝ) = kernelGramForm K c c'
    exact (kernelGramForm.symm hsym c c').symm
  re_inner_nonneg := by
    intro c
    show 0 ≤ kernelGramForm K c c
    exact kernelGramForm.nonneg_of_psd hpsd c
  add_left := by
    intro c₁ c₂ d
    show kernelGramForm K (c₁ + c₂) d
          = kernelGramForm K c₁ d + kernelGramForm K c₂ d
    exact kernelGramForm.add_left K c₁ c₂ d
  smul_left := by
    intro c d r
    -- The goal is `inner (r • c) d = conj r * inner c d` with `𝕜 = ℝ`;
    -- since `conj` is the identity on `ℝ`, this reduces to the
    -- bilinearity lemma `smul_left`.
    show kernelGramForm K (r • c) d
          = (starRingEnd ℝ) r * kernelGramForm K c d
    rw [kernelGramForm.smul_left K r c d]
    rfl

/-- **Pre-RKHS feature map.** For a kernel `K : 𝒳 → 𝒳 → ℝ`, the
canonical feature map sending `x` to the formal generator
`δ_x ∈ 𝒳 →₀ ℝ` is `fun x => Finsupp.single x 1`. -/
noncomputable def preRKHSFeature {𝒳 : Type*} [DecidableEq 𝒳]
    (x : 𝒳) : 𝒳 →₀ ℝ :=
  Finsupp.single x 1

/-- **Reproducing identity on basis features.** The pre-RKHS Gram form
of two basis feature vectors `δ_x` and `δ_y` recovers `K x y`. This is
the algebraic Aronszajn reproducing identity at the level of the
pre-RKHS — once the quotient and completion stages are performed, this
identity propagates to the full Hilbert RKHS. -/
theorem kernelGramForm_feature_eq_kernel
    {𝒳 : Type*} [DecidableEq 𝒳] (K : 𝒳 → 𝒳 → ℝ) (x y : 𝒳) :
    kernelGramForm K (preRKHSFeature x) (preRKHSFeature y) = K x y :=
  kernelGramForm.single_one_single_one K x y

/-! ### Reproducing realisation of *any* kernel that has a feature map

The Aronszajn theorem promises that every symmetric PSD kernel `K`
admits a reproducing realisation `(E, φ, eval)` as in
`IsReproducingFeatureMap`. Conversely, if one is **given** a real
inner-product space `E` and a map `φ : 𝒳 → E` such that
`K x y = ⟨φ x, φ y⟩_ℝ`, then `(E, φ, eval := fun f x => ⟨f, φ x⟩)`
forms such a realisation. This converse direction is *constructive in
Lean* and packages neatly into a tool that downstream theorems (e.g.
the typed-RKHS representer theorem) can use.
-/

/-- **Reproducing realisation from a feature map.** Given any real
inner-product space `E` and a map `φ : 𝒳 → E` that reproduces `K` (i.e.
`K x y = ⟨φ x, φ y⟩_ℝ`), the data `(E, φ, fun f x => ⟨f, φ x⟩_ℝ)` is
a reproducing realisation of `K`. -/
def IsReproducingFeatureMap.ofFeatureMap
    {𝒳 E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {K : 𝒳 → 𝒳 → ℝ} {φ : 𝒳 → E}
    (h : ∀ x y, K x y = ⟪φ x, φ y⟫_ℝ) :
    IsReproducingFeatureMap K φ (fun f x => ⟪f, φ x⟫_ℝ) where
  reproducing := by intro f x; rfl
  kernel_eq := h

/-- **Packaged RKHS from a feature map.** Given a real inner-product
space `E` and a map `φ : 𝒳 → E` reproducing `K`, package the data into
an `RKHS_of_kernel K` record. This is the converse direction of
Aronszajn (the easier direction — full Aronszajn produces such an `E`
from the kernel alone, which is the documented Mathlib gap). -/
noncomputable def RKHS_of_kernel.ofFeatureMap
    {𝒳 : Type*} {K : 𝒳 → 𝒳 → ℝ} (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (φ : 𝒳 → E) (h : ∀ x y, K x y = ⟪φ x, φ y⟫_ℝ) :
    RKHS_of_kernel K where
  E := E
  φ := φ
  eval f x := ⟪f, φ x⟫_ℝ
  is_repro := IsReproducingFeatureMap.ofFeatureMap h

/-! ### NEEDS_HELP marker for full Moore–Aronszajn

The construction of the *Hilbert-space* RKHS `H_K` from an abstract
symmetric PSD kernel — by `SeparationQuotient`-then-`Completion` of the
pre-RKHS — requires threading the inner product, the feature map, and
the reproducing identity through both functors. This is mechanical but
voluminous; in particular, it requires:

  * Promoting `preRKHSCore_of_psd_kernel` to a
    `SeminormedAddCommGroup (𝒳 →₀ ℝ)` instance (via
    `PreInnerProductSpace.Core.toSeminormedAddCommGroup`), then to a
    `NormedAddCommGroup (SeparationQuotient (𝒳 →₀ ℝ))`.
  * Wrapping with `UniformSpace.Completion` to land in a `CompleteSpace`
    `InnerProductSpace ℝ` (Mathlib's
    `Completion.innerProductSpace` instance, see
    `Mathlib.Analysis.InnerProductSpace.Completion`).
  * Tracking the feature map and reproducing identity through each
    stage; the inner product on the completion of an
    `InnerProductSpace` is `Mathlib`-defined, but its extension to
    formal sums via `Completion.coe` is a chase across multiple
    `UniformSpace.Completion` lemmas.

This is the documented Tier-C gap; downstream theorems do **not** need
the full Hilbert RKHS to land, because the typed RKHS interface
`RKHS_of_kernel` already lets them consume any reproducing realisation
constructed by other means (e.g. the linear-kernel case in
`RKHS_of_kernel.linear`, or callers' bespoke kernels). -/

end LTFP.MathlibExt.Analysis
