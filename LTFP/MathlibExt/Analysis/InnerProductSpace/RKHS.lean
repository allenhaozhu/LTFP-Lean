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
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
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

end LTFP.MathlibExt.Analysis
