/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Pi
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# `Fin 2` block compression adapter for `CStarMatrix`

This file provides the bridging infrastructure that lets us transfer
operator inequalities between the C⋆-algebra `A` and the C⋆-algebra
`CStarMatrix (Fin 2) (Fin 2) A` of `2 × 2` matrices with entries in
`A`. It is the decisive classification spike for Part 6 of the B6 L3
carrier closure (Effros perspective concavity).

## Main declarations

* `LTFP.MathlibExt.MatrixAnalysis.diag₂` — the block-diagonal `2 × 2`
  matrix `!![x, 0; 0, y]` viewed as an element of
  `CStarMatrix (Fin 2) (Fin 2) A`.
* `LTFP.MathlibExt.MatrixAnalysis.col₂` — the "column-like" `2 × 2`
  matrix `!![v, 0; w, 0]` viewed as an element of
  `CStarMatrix (Fin 2) (Fin 2) A`.
* `LTFP.MathlibExt.MatrixAnalysis.diag₂Hom` — the unital
  `⋆`-algebra homomorphism `A × A →⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) A`
  sending `(x, y)` to `diag₂ x y`.
* `LTFP.MathlibExt.MatrixAnalysis.CFC.rpow_diag₂` — for `0 ≤ p`,
  `(diag₂ x y) ^ p = diag₂ (x ^ p) (y ^ p)`.
* `LTFP.MathlibExt.MatrixAnalysis.diag₂_le_diag₂_iff_left` — the order
  inequality `diag₂ x 0 ≤ diag₂ y 0 ↔ x ≤ y`.

## Implementation notes

* `CStarMatrix m n A` is a *type copy* of `Matrix m n A`; we use
  `CStarMatrix.ofMatrix` to mediate between the two views and rely on
  the existing C⋆-algebra structure declared on the matrix side.
* The `rpow_diag₂` proof goes through `cfc_map_prod` to package
  `(x ^ p, y ^ p)` as `(x, y) ^ p` in the product C⋆-algebra `A × A`,
  and then transports through `diag₂Hom.map_cfc` using that ⋆-algebra
  homomorphisms commute with the continuous functional calculus.
  This avoids any invertibility hypothesis on `x` or `y`.
* The forward direction of `diag₂_le_diag₂_iff_left` extracts the
  `(0,0)` corner of a positive matrix using the
  `StarOrderedRing.le_iff` characterisation of positivity as a sum of
  `star Q * Q`. The reverse direction follows because
  `diag₂Hom` is a `⋆`-algebra homomorphism and hence order-preserving.
-/

@[expose] public section

namespace LTFP.MathlibExt.MatrixAnalysis

open scoped NNReal CStarAlgebra
open CStarMatrix

variable {A : Type*} [CStarAlgebra A]

/-! ### Block-diagonal and column-like 2×2 matrices -/

/-- The block-diagonal `2 × 2` matrix `!![x, 0; 0, y]` viewed as an
element of `CStarMatrix (Fin 2) (Fin 2) A`.

Because `CStarMatrix m n A` is a type copy of `Matrix m n A`
(`CStarMatrix.ofMatrix` is `Equiv.refl`), we use the standard
`Matrix.diagonal` construction directly. -/
noncomputable def diag₂ (x y : A) : CStarMatrix (Fin 2) (Fin 2) A :=
  Matrix.diagonal ![x, y]

/-- The "column-like" `2 × 2` matrix `!![v, 0; w, 0]` viewed as an
element of `CStarMatrix (Fin 2) (Fin 2) A`. Both nontrivial entries
sit in the first column; the second column is zero. -/
noncomputable def col₂ (v w : A) : CStarMatrix (Fin 2) (Fin 2) A :=
  !![v, 0; w, 0]

@[simp]
lemma diag₂_apply_zero_zero (x y : A) : (diag₂ x y) 0 0 = x := by
  simp [diag₂]

@[simp]
lemma diag₂_apply_one_one (x y : A) : (diag₂ x y) 1 1 = y := by
  simp [diag₂]

@[simp]
lemma diag₂_apply_zero_one (x y : A) : (diag₂ x y) 0 1 = 0 := by
  simp [diag₂]

@[simp]
lemma diag₂_apply_one_zero (x y : A) : (diag₂ x y) 1 0 = 0 := by
  simp [diag₂]

/-! ### Algebraic structure of `diag₂` -/

@[simp]
lemma diag₂_zero_zero : diag₂ (0 : A) (0 : A) = 0 := by
  show (Matrix.diagonal ![(0 : A), 0] : CStarMatrix (Fin 2) (Fin 2) A) = 0
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

@[simp]
lemma diag₂_one_one : diag₂ (1 : A) (1 : A) = 1 := by
  -- The identity element of `CStarMatrix (Fin 2) (Fin 2) A` is the identity
  -- matrix.
  show (Matrix.diagonal ![(1 : A), 1] : CStarMatrix (Fin 2) (Fin 2) A) = 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal]

lemma diag₂_add (x₁ x₂ y₁ y₂ : A) :
    diag₂ (x₁ + x₂) (y₁ + y₂) = diag₂ x₁ y₁ + diag₂ x₂ y₂ := by
  show (Matrix.diagonal ![x₁ + x₂, y₁ + y₂] : CStarMatrix (Fin 2) (Fin 2) A) =
    Matrix.diagonal ![x₁, y₁] + Matrix.diagonal ![x₂, y₂]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, Matrix.add_apply]

lemma diag₂_neg (x y : A) : diag₂ (-x) (-y) = -diag₂ x y := by
  show (Matrix.diagonal ![-x, -y] : CStarMatrix (Fin 2) (Fin 2) A) =
    -Matrix.diagonal ![x, y]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, Matrix.neg_apply]

lemma diag₂_sub (x₁ x₂ y₁ y₂ : A) :
    diag₂ (x₁ - x₂) (y₁ - y₂) = diag₂ x₁ y₁ - diag₂ x₂ y₂ := by
  show (Matrix.diagonal ![x₁ - x₂, y₁ - y₂] : CStarMatrix (Fin 2) (Fin 2) A) =
    Matrix.diagonal ![x₁, y₁] - Matrix.diagonal ![x₂, y₂]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal, Matrix.sub_apply, sub_eq_add_neg]

lemma diag₂_mul (x₁ x₂ y₁ y₂ : A) :
    diag₂ (x₁ * x₂) (y₁ * y₂) = diag₂ x₁ y₁ * diag₂ x₂ y₂ := by
  -- Multiplication on `CStarMatrix (Fin 2) (Fin 2) A` is the same as matrix
  -- multiplication via the type-copy structure; for diagonal matrices it is
  -- entrywise.
  show (Matrix.diagonal ![x₁ * x₂, y₁ * y₂] : CStarMatrix (Fin 2) (Fin 2) A) =
    Matrix.diagonal ![x₁, y₁] * Matrix.diagonal ![x₂, y₂]
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]

lemma diag₂_smul (c : ℂ) (x y : A) :
    diag₂ (c • x) (c • y) = c • diag₂ x y := by
  show (Matrix.diagonal ![c • x, c • y] : CStarMatrix (Fin 2) (Fin 2) A) =
    c • Matrix.diagonal ![x, y]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, Matrix.smul_apply]

lemma diag₂_star (x y : A) : diag₂ (star x) (star y) = star (diag₂ x y) := by
  show (Matrix.diagonal ![star x, star y] : CStarMatrix (Fin 2) (Fin 2) A) =
    star (Matrix.diagonal ![x, y] : CStarMatrix (Fin 2) (Fin 2) A)
  ext i j
  -- `star` on `CStarMatrix` agrees with `Matrix.star`, which is conjugate
  -- transpose. The diagonal is selfconjugate-transpose (off-diagonal stays 0).
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.diagonal]

lemma diag₂_algebraMap (c : ℂ) :
    diag₂ (algebraMap ℂ A c) (algebraMap ℂ A c) =
      algebraMap ℂ (CStarMatrix (Fin 2) (Fin 2) A) c := by
  -- `algebraMap` on `CStarMatrix n n A` is the diagonal embedding through
  -- `algebraMap` on `A`.
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diag₂, Matrix.diagonal, CStarMatrix.algebraMap_apply]

/-! ### `diag₂Hom` as a `⋆`-algebra homomorphism -/

/-- The unital `⋆`-algebra homomorphism
`A × A →⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) A` sending `(x, y)` to
the block-diagonal matrix `diag₂ x y`. -/
noncomputable def diag₂Hom : A × A →⋆ₐ[ℂ] CStarMatrix (Fin 2) (Fin 2) A where
  toFun := fun p => diag₂ p.1 p.2
  map_one' := by simp [diag₂_one_one]
  map_zero' := by simp [diag₂_zero_zero]
  map_add' := fun p q => by
    -- `(x₁ + x₂, y₁ + y₂)` maps to `diag₂ x₁ y₁ + diag₂ x₂ y₂`.
    have := diag₂_add (A := A) p.1 q.1 p.2 q.2
    simpa using this
  map_mul' := fun p q => by
    have := diag₂_mul (A := A) p.1 q.1 p.2 q.2
    simpa using this
  map_star' := fun p => by
    have := diag₂_star (A := A) p.1 p.2
    simpa using this
  commutes' := fun c => by
    -- The algebra map on `A × A` is componentwise.
    have h₁ : (algebraMap ℂ (A × A) c).1 = algebraMap ℂ A c := rfl
    have h₂ : (algebraMap ℂ (A × A) c).2 = algebraMap ℂ A c := rfl
    show diag₂ (algebraMap ℂ (A × A) c).1 (algebraMap ℂ (A × A) c).2 =
      algebraMap ℂ (CStarMatrix (Fin 2) (Fin 2) A) c
    rw [h₁, h₂]
    exact diag₂_algebraMap (A := A) c

@[simp]
lemma diag₂Hom_apply (x y : A) :
    (diag₂Hom : A × A →⋆ₐ[ℂ] _) (x, y) = diag₂ x y := rfl

lemma continuous_diag₂Hom : Continuous (diag₂Hom : A × A → _) := by
  -- Composition: `(x, y) ↦ Matrix.diagonal ![x, y] ↦ ofMatrix(...)`,
  -- where `ofMatrixL` is a continuous linear equivalence.
  have h_cont_matrix : Continuous fun p : A × A =>
      (Matrix.diagonal ![p.1, p.2] : Matrix (Fin 2) (Fin 2) A) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;>
      (simp only [Matrix.diagonal, Matrix.of_apply]
       first
         | exact continuous_const
         | exact continuous_fst
         | exact continuous_snd)
  -- `CStarMatrix.ofMatrixL` is a continuous linear equiv `Matrix ≃L[ℂ] CStarMatrix`.
  exact (CStarMatrix.ofMatrixL (m := Fin 2) (n := Fin 2) (A := A)).continuous.comp
    h_cont_matrix

/-! ### Rpow commutes with `diag₂` -/

section Order

variable [PartialOrder A] [StarOrderedRing A]

/-- **Functional-calculus compatibility.** For a continuous function
`f : ℝ≥0 → ℝ≥0` and nonneg elements `x, y : A`, the continuous
functional calculus of `f` on the block-diagonal `diag₂ x y`
distributes through the corner entries. -/
lemma diag₂_cfc {f : ℝ≥0 → ℝ≥0} (hf : Continuous f) {x y : A}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    cfc f (diag₂ x y) = diag₂ (cfc f x) (cfc f y) := by
  -- Step 1: the product `(x, y) : A × A` is nonneg componentwise.
  have hxy : 0 ≤ ((x, y) : A × A) := ⟨hx, hy⟩
  -- Step 2: `diag₂Hom` is positive (preserves order), so `diag₂ x y` is nonneg.
  have h_diag_nonneg : 0 ≤ (diag₂Hom : A × A →⋆ₐ[ℂ] _) (x, y) := by
    have : (diag₂Hom : A × A →⋆ₐ[ℂ] _) 0 ≤ diag₂Hom (x, y) :=
      OrderHomClass.mono diag₂Hom (a := (0 : A × A)) (b := ((x, y) : A × A)) hxy
    simpa using this
  -- Step 3: apply `cfc_map_prod` for the product `(x, y)`.
  -- We use `R := ℝ≥0` (the rpow predicate ring) and `S := ℝ`
  -- (which satisfies `CommRing` and bridges `ℝ≥0 → A`).
  have h_prod :
      cfc f ((x, y) : A × A) = (cfc f x, cfc f y) :=
    cfc_map_prod (R := ℝ≥0) (S := ℝ) (f := f) (a := x) (b := y)
      hf.continuousOn hxy hx hy
  -- Step 4: transport `cfc f (x, y)` through `diag₂Hom`.
  have h_hom :
      (diag₂Hom : A × A →⋆ₐ[ℂ] _) (cfc f ((x, y) : A × A)) =
        cfc f (diag₂Hom ((x, y) : A × A)) :=
    StarAlgHom.map_cfc (S := ℂ) (φ := diag₂Hom) (f := f)
      (a := ((x, y) : A × A))
      hf.continuousOn continuous_diag₂Hom hxy (by simpa using h_diag_nonneg)
  -- Step 5: combine.
  -- LHS: `diag₂Hom (cfc f (x, y)) = diag₂Hom (cfc f x, cfc f y) = diag₂ (cfc f x) (cfc f y)`.
  -- RHS: `cfc f (diag₂Hom (x, y)) = cfc f (diag₂ x y)`.
  have h₁ : (diag₂Hom : A × A →⋆ₐ[ℂ] _) (cfc f ((x, y) : A × A)) =
      diag₂ (cfc f x) (cfc f y) := by
    rw [h_prod]; rfl
  have h₂ : (diag₂Hom : A × A →⋆ₐ[ℂ] _) ((x, y) : A × A) = diag₂ x y := rfl
  rw [h₂] at h_hom
  exact h_hom.symm.trans h₁

/-- **`rpow` of a block-diagonal matrix is the block-diagonal of `rpow`s.**
For `0 ≤ p`, `(diag₂ x y) ^ p = diag₂ (x ^ p) (y ^ p)`. -/
lemma CFC.rpow_diag₂ {p : ℝ} (hp : 0 ≤ p) {x y : A}
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (diag₂ x y) ^ p = diag₂ (x ^ p) (y ^ p) := by
  -- Both sides unfold to `cfc (fun t : ℝ≥0 => t ^ p)` on their inputs.
  rw [show ((diag₂ x y) ^ p : CStarMatrix (Fin 2) (Fin 2) A) =
        cfc (fun t : ℝ≥0 => t ^ p) (diag₂ x y) from _root_.CFC.rpow_def,
      show (x ^ p : A) = cfc (fun t : ℝ≥0 => t ^ p) x from _root_.CFC.rpow_def,
      show (y ^ p : A) = cfc (fun t : ℝ≥0 => t ^ p) y from _root_.CFC.rpow_def]
  exact diag₂_cfc (NNReal.continuous_rpow_const hp) hx hy

/-! ### Order on `diag₂` -/

/-- **Reverse direction of the corner-compression equivalence.**
If `x ≤ y` in `A`, then `diag₂ x 0 ≤ diag₂ y 0` in
`CStarMatrix (Fin 2) (Fin 2) A`. -/
lemma diag₂_mono_left {x y : A} (hxy : x ≤ y) :
    diag₂ x 0 ≤ diag₂ y 0 := by
  -- `diag₂Hom` is a ⋆-algebra hom, hence order-preserving.
  have : (diag₂Hom : A × A →⋆ₐ[ℂ] _) (x, 0) ≤ diag₂Hom (y, 0) :=
    OrderHomClass.mono diag₂Hom (a := (x, 0)) (b := (y, 0))
      ⟨hxy, le_refl _⟩
  simpa using this

/-- **(0,0) corner of a nonneg `2×2` matrix is nonneg in `A`.**
This is the load-bearing forward step of the corner-compression
equivalence. -/
lemma corner_zero_zero_nonneg {M : CStarMatrix (Fin 2) (Fin 2) A}
    (hM : 0 ≤ M) : 0 ≤ M 0 0 := by
  -- Unfold the StarOrderedRing characterisation of positivity.
  rw [StarOrderedRing.nonneg_iff] at hM
  -- `M` lies in the additive submonoid generated by `{star Q * Q | Q}`.
  refine AddSubmonoid.closure_induction
    (motive := fun P _ => 0 ≤ P 0 0)
    ?mem ?zero ?add hM
  · -- Base case: `P = star Q * Q` for some `Q`.
    rintro P ⟨Q, rfl⟩
    -- `(star Q * Q) 0 0 = ∑ k, star (Q k 0) * Q k 0` ≥ 0 in `A`.
    show 0 ≤ ((star Q * Q : Matrix (Fin 2) (Fin 2) A)) 0 0
    rw [Matrix.mul_apply]
    refine Finset.sum_nonneg ?_
    intro k _
    -- `(star Q) 0 k = star (Q k 0)`.
    have hstar : (star Q : Matrix (Fin 2) (Fin 2) A) 0 k = star (Q k 0) := by
      simp [Matrix.star_apply]
    rw [hstar]
    exact star_mul_self_nonneg (Q k 0)
  · -- Zero case.
    show 0 ≤ ((0 : Matrix (Fin 2) (Fin 2) A)) 0 0
    simp
  · -- Additivity case.
    intro P₁ P₂ _ _ hP₁ hP₂
    show 0 ≤ ((P₁ + P₂ : Matrix (Fin 2) (Fin 2) A)) 0 0
    rw [Matrix.add_apply]
    exact add_nonneg hP₁ hP₂

/-- **Forward direction of the corner-compression equivalence.**
If `diag₂ x 0 ≤ diag₂ y 0`, then `x ≤ y`. -/
lemma le_of_diag₂_le_diag₂_left {x y : A}
    (h : diag₂ x 0 ≤ diag₂ y 0) : x ≤ y := by
  -- Rewrite as `0 ≤ y - x` using `0 ≤ diag₂ y 0 - diag₂ x 0 = diag₂ (y - x) 0`.
  have h₀ : (0 : CStarMatrix (Fin 2) (Fin 2) A) ≤ diag₂ y 0 - diag₂ x 0 :=
    sub_nonneg.mpr h
  have hsub : (diag₂ y 0 - diag₂ x 0 : CStarMatrix (Fin 2) (Fin 2) A) =
      diag₂ (y - x) 0 := by
    have h := diag₂_sub (A := A) y x (0 : A) (0 : A)
    simpa [sub_zero] using h.symm
  rw [hsub] at h₀
  -- Extract the `(0,0)` entry, which equals `y - x` in `A`.
  have h₁ : 0 ≤ (diag₂ (y - x) 0) 0 0 := corner_zero_zero_nonneg h₀
  rw [diag₂_apply_zero_zero] at h₁
  exact sub_nonneg.mp h₁

/-- **Corner-compression equivalence.**
`diag₂ x 0 ≤ diag₂ y 0` if and only if `x ≤ y`. -/
lemma diag₂_le_diag₂_iff_left {x y : A} :
    diag₂ x 0 ≤ diag₂ y 0 ↔ x ≤ y :=
  ⟨le_of_diag₂_le_diag₂_left, diag₂_mono_left⟩

end Order

end LTFP.MathlibExt.MatrixAnalysis
