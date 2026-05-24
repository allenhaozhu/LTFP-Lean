/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.MatrixAnalysis.CStarFin2Adapter
import LTFP.MathlibExt.MatrixAnalysis.CStarHansenPedersen

/-!
# Two-state Hansen-Pedersen Jensen via the Effros block matrix route

This file lifts the C⋆-algebraic Hansen-Pedersen Jensen inequality
(`LTFP.MathlibExt.MatrixAnalysis.CFC.star_mul_rpow_mul_le_rpow_star_mul`,
single-state Part 5) to its two-state form via the standard Effros block
matrix trick: package the two states `(x₁, x₂)` as a block-diagonal
`2 × 2` matrix `M = diag₂ x₁ x₂` and the two convex weights `(v₁, v₂)`
as a "column" matrix `V = col₂ v₁ v₂`. Then Part 5 applied to `M, V`
gives a matrix inequality whose `(0, 0)` corner is the desired
two-state Hansen-Pedersen Jensen statement.

## Main declaration

* `LTFP.MathlibExt.MatrixAnalysis.CFC.sum_star_mul_rpow_mul_le_rpow_sum_star_mul`
  — for `0 ≤ x₁, 0 ≤ x₂` and `star v₁ * v₁ + star v₂ * v₂ = 1` in a
  unital C⋆-algebra `A` and `p ∈ [0, 1]`,

  ```
  star v₁ * (x₁ ^ p) * v₁ + star v₂ * (x₂ ^ p) * v₂
    ≤ (star v₁ * x₁ * v₁ + star v₂ * x₂ * v₂) ^ p
  ```

  in the operator order. This is B6 L3 Sub-Part 6.2.

## Implementation notes

* The block-matrix identities used here are proven by `ext` /
  `fin_cases` from `Matrix.mul_apply` and `Matrix.star_apply`. These
  are robust because `diag₂ x y` and `col₂ v w` unfold to concrete
  `Matrix.of` definitions.
* The corner-extraction step is the forward direction
  `corner_zero_zero_nonneg` from the adapter: from a *positive*
  `2 × 2` matrix, the `(0, 0)` entry is positive in `A`. We apply this
  to the *difference* `RHS - LHS` of the lifted Part-5 inequality, so
  the leftover `0 ^ p` factor at the `(1, 1)` corner (which is `1` for
  `p = 0` and `0` for `p > 0`, but in any case nonneg) does not
  interfere with the `(0, 0)` corner reading.
-/

@[expose] public section

namespace LTFP.MathlibExt.MatrixAnalysis

open scoped NNReal CStarAlgebra
open CStarMatrix

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-! ### Block-matrix identities for `V := col₂ v₁ v₂` -/

section BlockIdentities

omit [PartialOrder A] [StarOrderedRing A]

variable (v₁ v₂ x₁ x₂ : A)

/-- `star (col₂ v₁ v₂) 0 0 = star v₁`. -/
@[simp]
private lemma star_col₂_apply_zero_zero :
    (star (col₂ v₁ v₂ : CStarMatrix (Fin 2) (Fin 2) A)) 0 0 = star v₁ := by
  rw [star_apply]; simp [col₂]

@[simp]
private lemma star_col₂_apply_zero_one :
    (star (col₂ v₁ v₂ : CStarMatrix (Fin 2) (Fin 2) A)) 0 1 = star v₂ := by
  rw [star_apply]; simp [col₂]

@[simp]
private lemma star_col₂_apply_one_zero :
    (star (col₂ v₁ v₂ : CStarMatrix (Fin 2) (Fin 2) A)) 1 0 = 0 := by
  rw [star_apply]; simp [col₂]

@[simp]
private lemma star_col₂_apply_one_one :
    (star (col₂ v₁ v₂ : CStarMatrix (Fin 2) (Fin 2) A)) 1 1 = 0 := by
  rw [star_apply]; simp [col₂]

@[simp]
private lemma col₂_apply_zero_zero :
    (col₂ v₁ v₂ : CStarMatrix (Fin 2) (Fin 2) A) 0 0 = v₁ := by
  simp [col₂]

@[simp]
private lemma col₂_apply_zero_one :
    (col₂ v₁ v₂ : CStarMatrix (Fin 2) (Fin 2) A) 0 1 = 0 := by
  simp [col₂]

@[simp]
private lemma col₂_apply_one_zero :
    (col₂ v₁ v₂ : CStarMatrix (Fin 2) (Fin 2) A) 1 0 = v₂ := by
  simp [col₂]

@[simp]
private lemma col₂_apply_one_one :
    (col₂ v₁ v₂ : CStarMatrix (Fin 2) (Fin 2) A) 1 1 = 0 := by
  simp [col₂]

/-- `star V * V = diag₂ (star v₁ * v₁ + star v₂ * v₂) 0` where
`V := col₂ v₁ v₂`. -/
private lemma star_col₂_mul_col₂ :
    (star (col₂ v₁ v₂) * col₂ v₁ v₂ :
        CStarMatrix (Fin 2) (Fin 2) A) =
      diag₂ (star v₁ * v₁ + star v₂ * v₂) 0 := by
  have h00 :
      (star (col₂ v₁ v₂) * col₂ v₁ v₂ :
          CStarMatrix (Fin 2) (Fin 2) A) 0 0 = star v₁ * v₁ + star v₂ * v₂ := by
    rw [CStarMatrix.mul_apply, Fin.sum_univ_two,
      star_col₂_apply_zero_zero, star_col₂_apply_zero_one,
      col₂_apply_zero_zero, col₂_apply_one_zero]
  have h01 :
      (star (col₂ v₁ v₂) * col₂ v₁ v₂ :
          CStarMatrix (Fin 2) (Fin 2) A) 0 1 = 0 := by
    rw [CStarMatrix.mul_apply, Fin.sum_univ_two,
      star_col₂_apply_zero_zero, star_col₂_apply_zero_one,
      col₂_apply_zero_one, col₂_apply_one_one]
    simp
  have h10 :
      (star (col₂ v₁ v₂) * col₂ v₁ v₂ :
          CStarMatrix (Fin 2) (Fin 2) A) 1 0 = 0 := by
    rw [CStarMatrix.mul_apply, Fin.sum_univ_two,
      star_col₂_apply_one_zero, star_col₂_apply_one_one,
      col₂_apply_zero_zero, col₂_apply_one_zero]
    simp
  have h11 :
      (star (col₂ v₁ v₂) * col₂ v₁ v₂ :
          CStarMatrix (Fin 2) (Fin 2) A) 1 1 = 0 := by
    rw [CStarMatrix.mul_apply, Fin.sum_univ_two,
      star_col₂_apply_one_zero, star_col₂_apply_one_one,
      col₂_apply_zero_one, col₂_apply_one_one]
    simp
  ext i j
  fin_cases i
  · fin_cases j
    · show (star (col₂ v₁ v₂) * col₂ v₁ v₂ :
          CStarMatrix (Fin 2) (Fin 2) A) 0 0 =
          diag₂ (star v₁ * v₁ + star v₂ * v₂) (0 : A) 0 0
      rw [h00]; simp [diag₂, Matrix.diagonal]
    · show (star (col₂ v₁ v₂) * col₂ v₁ v₂ :
          CStarMatrix (Fin 2) (Fin 2) A) 0 1 =
          diag₂ (star v₁ * v₁ + star v₂ * v₂) (0 : A) 0 1
      rw [h01]; simp [diag₂, Matrix.diagonal]
  · fin_cases j
    · show (star (col₂ v₁ v₂) * col₂ v₁ v₂ :
          CStarMatrix (Fin 2) (Fin 2) A) 1 0 =
          diag₂ (star v₁ * v₁ + star v₂ * v₂) (0 : A) 1 0
      rw [h10]; simp [diag₂, Matrix.diagonal]
    · show (star (col₂ v₁ v₂) * col₂ v₁ v₂ :
          CStarMatrix (Fin 2) (Fin 2) A) 1 1 =
          diag₂ (star v₁ * v₁ + star v₂ * v₂) (0 : A) 1 1
      rw [h11]; simp [diag₂, Matrix.diagonal]

/-- `star V * M` has explicit row form: row 0 = `(star v₁ * x₁, star v₂ * x₂)`,
row 1 = `(0, 0)`. -/
private lemma star_col₂_mul_diag₂_apply_zero_zero :
    (star (col₂ v₁ v₂) * diag₂ x₁ x₂ :
        CStarMatrix (Fin 2) (Fin 2) A) 0 0 = star v₁ * x₁ := by
  rw [CStarMatrix.mul_apply]
  simp [diag₂, Matrix.diagonal]

private lemma star_col₂_mul_diag₂_apply_zero_one :
    (star (col₂ v₁ v₂) * diag₂ x₁ x₂ :
        CStarMatrix (Fin 2) (Fin 2) A) 0 1 = star v₂ * x₂ := by
  rw [CStarMatrix.mul_apply]
  simp [diag₂, Matrix.diagonal]

private lemma star_col₂_mul_diag₂_apply_one_zero :
    (star (col₂ v₁ v₂) * diag₂ x₁ x₂ :
        CStarMatrix (Fin 2) (Fin 2) A) 1 0 = 0 := by
  rw [CStarMatrix.mul_apply]
  simp [diag₂, Matrix.diagonal]

private lemma star_col₂_mul_diag₂_apply_one_one :
    (star (col₂ v₁ v₂) * diag₂ x₁ x₂ :
        CStarMatrix (Fin 2) (Fin 2) A) 1 1 = 0 := by
  rw [CStarMatrix.mul_apply]
  simp [diag₂, Matrix.diagonal]

/-- `star V * M * V = diag₂ (star v₁ * x₁ * v₁ + star v₂ * x₂ * v₂) 0`,
where `V := col₂ v₁ v₂`, `M := diag₂ x₁ x₂`. -/
private lemma star_col₂_mul_diag₂_mul_col₂ :
    (star (col₂ v₁ v₂) * diag₂ x₁ x₂ * col₂ v₁ v₂ :
        CStarMatrix (Fin 2) (Fin 2) A) =
      diag₂ (star v₁ * x₁ * v₁ + star v₂ * x₂ * v₂) 0 := by
  -- Entry (0,0).
  have h00 :
      (star (col₂ v₁ v₂) * diag₂ x₁ x₂ * col₂ v₁ v₂ :
          CStarMatrix (Fin 2) (Fin 2) A) 0 0 =
        star v₁ * x₁ * v₁ + star v₂ * x₂ * v₂ := by
    rw [CStarMatrix.mul_apply, Fin.sum_univ_two,
      star_col₂_mul_diag₂_apply_zero_zero,
      star_col₂_mul_diag₂_apply_zero_one,
      col₂_apply_zero_zero, col₂_apply_one_zero]
  -- Entry (0,1).
  have h01 :
      (star (col₂ v₁ v₂) * diag₂ x₁ x₂ * col₂ v₁ v₂ :
          CStarMatrix (Fin 2) (Fin 2) A) 0 1 = 0 := by
    rw [CStarMatrix.mul_apply, Fin.sum_univ_two,
      star_col₂_mul_diag₂_apply_zero_zero,
      star_col₂_mul_diag₂_apply_zero_one,
      col₂_apply_zero_one, col₂_apply_one_one]
    simp
  -- Entry (1,0).
  have h10 :
      (star (col₂ v₁ v₂) * diag₂ x₁ x₂ * col₂ v₁ v₂ :
          CStarMatrix (Fin 2) (Fin 2) A) 1 0 = 0 := by
    rw [CStarMatrix.mul_apply, Fin.sum_univ_two,
      star_col₂_mul_diag₂_apply_one_zero,
      star_col₂_mul_diag₂_apply_one_one,
      col₂_apply_zero_zero, col₂_apply_one_zero]
    simp
  -- Entry (1,1).
  have h11 :
      (star (col₂ v₁ v₂) * diag₂ x₁ x₂ * col₂ v₁ v₂ :
          CStarMatrix (Fin 2) (Fin 2) A) 1 1 = 0 := by
    rw [CStarMatrix.mul_apply, Fin.sum_univ_two,
      star_col₂_mul_diag₂_apply_one_zero,
      star_col₂_mul_diag₂_apply_one_one,
      col₂_apply_zero_one, col₂_apply_one_one]
    simp
  ext i j
  fin_cases i
  · fin_cases j
    · show (star (col₂ v₁ v₂) * diag₂ x₁ x₂ * col₂ v₁ v₂ :
          CStarMatrix (Fin 2) (Fin 2) A) 0 0 =
          diag₂ (star v₁ * x₁ * v₁ + star v₂ * x₂ * v₂) (0 : A) 0 0
      rw [h00]; simp [diag₂, Matrix.diagonal]
    · show (star (col₂ v₁ v₂) * diag₂ x₁ x₂ * col₂ v₁ v₂ :
          CStarMatrix (Fin 2) (Fin 2) A) 0 1 =
          diag₂ (star v₁ * x₁ * v₁ + star v₂ * x₂ * v₂) (0 : A) 0 1
      rw [h01]; simp [diag₂, Matrix.diagonal]
  · fin_cases j
    · show (star (col₂ v₁ v₂) * diag₂ x₁ x₂ * col₂ v₁ v₂ :
          CStarMatrix (Fin 2) (Fin 2) A) 1 0 =
          diag₂ (star v₁ * x₁ * v₁ + star v₂ * x₂ * v₂) (0 : A) 1 0
      rw [h10]; simp [diag₂, Matrix.diagonal]
    · show (star (col₂ v₁ v₂) * diag₂ x₁ x₂ * col₂ v₁ v₂ :
          CStarMatrix (Fin 2) (Fin 2) A) 1 1 =
          diag₂ (star v₁ * x₁ * v₁ + star v₂ * x₂ * v₂) (0 : A) 1 1
      rw [h11]; simp [diag₂, Matrix.diagonal]

end BlockIdentities

/-! ### Two-state Hansen-Pedersen Jensen -/

/-- **Two-state Hansen-Pedersen Jensen inequality (B6 L3 Sub-Part 6.2).**

For `0 ≤ x₁, x₂` in a unital C⋆-algebra `A`, convex weights
`v₁, v₂ : A` with `star v₁ * v₁ + star v₂ * v₂ = 1`, and `p ∈ [0, 1]`,

```
star v₁ * (x₁ ^ p) * v₁ + star v₂ * (x₂ ^ p) * v₂
  ≤ (star v₁ * x₁ * v₁ + star v₂ * x₂ * v₂) ^ p
```

holds in the operator order.

The proof packages the data into a `2 × 2` block matrix calculation:
with `V := col₂ v₁ v₂` and `M := diag₂ x₁ x₂` we have
`star V * V = diag₂ 1 0 ≤ 1` and the single-state Hansen-Pedersen
inequality applied to `(M, V)` reads
`star V * M^p * V ≤ (star V * M * V)^p`. Both sides have explicit
diagonal form; extracting the `(0, 0)` corner of the (positive)
difference gives the desired scalar inequality. -/
theorem CFC.sum_star_mul_rpow_mul_le_rpow_sum_star_mul
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    {x₁ x₂ v₁ v₂ : A} (hx₁ : 0 ≤ x₁) (hx₂ : 0 ≤ x₂)
    (hv : star v₁ * v₁ + star v₂ * v₂ = 1) :
    star v₁ * (x₁ ^ p) * v₁ + star v₂ * (x₂ ^ p) * v₂ ≤
      (star v₁ * x₁ * v₁ + star v₂ * x₂ * v₂) ^ p := by
  -- Package the two states as a block-diagonal matrix and the two weights as a
  -- column matrix.
  set V : CStarMatrix (Fin 2) (Fin 2) A := col₂ v₁ v₂ with hV_def
  set M : CStarMatrix (Fin 2) (Fin 2) A := diag₂ x₁ x₂ with hM_def
  set s : A := star v₁ * x₁ * v₁ + star v₂ * x₂ * v₂ with hs_def
  -- Nonnegativity of `s`: sum of two `star_left_conjugate_nonneg`.
  have hs_nonneg : 0 ≤ s := by
    have h₁ : 0 ≤ star v₁ * x₁ * v₁ := star_left_conjugate_nonneg hx₁ v₁
    have h₂ : 0 ≤ star v₂ * x₂ * v₂ := star_left_conjugate_nonneg hx₂ v₂
    exact add_nonneg h₁ h₂
  -- `0 ≤ M`: image of `(x₁, x₂) ≥ 0` under the `⋆`-algebra hom `diag₂Hom`.
  have hM_pos : 0 ≤ M := by
    have hpair : (0 : A × A) ≤ ((x₁, x₂) : A × A) := ⟨hx₁, hx₂⟩
    have := OrderHomClass.mono (diag₂Hom (A := A))
      (a := (0 : A × A)) (b := ((x₁, x₂) : A × A)) hpair
    -- `diag₂Hom (0, 0) = 0` and `diag₂Hom (x₁, x₂) = diag₂ x₁ x₂ = M`.
    simpa [diag₂Hom_apply, diag₂_zero_zero, hM_def] using this
  -- `star V * V = diag₂ 1 0 ≤ 1`.
  have hVV_eq : star V * V = diag₂ (1 : A) 0 := by
    rw [hV_def]
    have := star_col₂_mul_col₂ (A := A) v₁ v₂
    rw [hv] at this
    exact this
  have hVV_le_one : star V * V ≤ 1 := by
    -- `diag₂ 1 0 ≤ diag₂ 1 1 = 1` via `diag₂Hom` mono on `(1, 0) ≤ (1, 1)`.
    rw [hVV_eq]
    have hpair : ((1, 0) : A × A) ≤ ((1, 1) : A × A) := ⟨le_rfl, zero_le_one⟩
    have := OrderHomClass.mono (diag₂Hom (A := A))
      (a := ((1, 0) : A × A)) (b := ((1, 1) : A × A)) hpair
    simpa [diag₂Hom_apply, diag₂_one_one] using this
  -- Apply Part 5 (single-state Hansen-Pedersen) to `M, V` in
  -- `CStarMatrix (Fin 2) (Fin 2) A`.
  have hHP :
      star V * (M ^ p) * V ≤ (star V * M * V) ^ p :=
    CFC.star_mul_rpow_mul_le_rpow_star_mul hp hM_pos hVV_le_one
  -- Rewrite both sides using the block-matrix identities.
  -- RHS: `star V * M * V = diag₂ s 0`, so RHS = `(diag₂ s 0) ^ p`.
  have hVMV_eq : star V * M * V = diag₂ s 0 := by
    rw [hV_def, hM_def, hs_def]
    exact star_col₂_mul_diag₂_mul_col₂ (A := A) v₁ v₂ x₁ x₂
  -- LHS uses `rpow_diag₂`: `M ^ p = diag₂ (x₁ ^ p) (x₂ ^ p)`.
  have hMp_eq : M ^ p = diag₂ (x₁ ^ p) (x₂ ^ p) :=
    CFC.rpow_diag₂ hp.1 hx₁ hx₂
  -- Then `star V * M^p * V = diag₂ (star v₁ * x₁^p * v₁ + star v₂ * x₂^p * v₂) 0`
  -- by the same matrix identity.
  have hVMpV_eq :
      star V * (M ^ p) * V =
        diag₂ (star v₁ * (x₁ ^ p) * v₁ + star v₂ * (x₂ ^ p) * v₂) 0 := by
    rw [hMp_eq, hV_def]
    exact star_col₂_mul_diag₂_mul_col₂ (A := A) v₁ v₂ (x₁ ^ p) (x₂ ^ p)
  -- And `(star V * M * V) ^ p = (diag₂ s 0) ^ p = diag₂ (s ^ p) (0 ^ p)`.
  have hRpow_eq : (star V * M * V) ^ p = diag₂ (s ^ p) ((0 : A) ^ p) := by
    rw [hVMV_eq]; exact CFC.rpow_diag₂ hp.1 hs_nonneg le_rfl
  -- Substitute into the matrix inequality `hHP`.
  rw [hVMpV_eq, hRpow_eq] at hHP
  -- Now `hHP : diag₂ (sum_conj_rpow) 0 ≤ diag₂ (s^p) (0^p)`.
  -- Pass to the (positive) difference and read the `(0, 0)` corner.
  have hdiff : 0 ≤ diag₂ (s ^ p) ((0 : A) ^ p) -
      diag₂ (star v₁ * (x₁ ^ p) * v₁ + star v₂ * (x₂ ^ p) * v₂) 0 :=
    sub_nonneg.mpr hHP
  -- The difference of two block-diagonals is block-diagonal entrywise.
  have hsub_eq :
      diag₂ (s ^ p) ((0 : A) ^ p) -
          diag₂ (star v₁ * (x₁ ^ p) * v₁ + star v₂ * (x₂ ^ p) * v₂) 0 =
      diag₂ (s ^ p - (star v₁ * (x₁ ^ p) * v₁ + star v₂ * (x₂ ^ p) * v₂))
            ((0 : A) ^ p - 0) := by
    have := diag₂_sub (A := A) (s ^ p)
      (star v₁ * (x₁ ^ p) * v₁ + star v₂ * (x₂ ^ p) * v₂)
      ((0 : A) ^ p) (0 : A)
    exact this.symm
  rw [hsub_eq] at hdiff
  -- Extract the `(0, 0)` corner; it equals `s ^ p - (conjugated sum)`.
  have h00 :
      0 ≤ (diag₂ (s ^ p -
            (star v₁ * (x₁ ^ p) * v₁ + star v₂ * (x₂ ^ p) * v₂))
            ((0 : A) ^ p - 0)) 0 0 :=
    corner_zero_zero_nonneg hdiff
  rw [diag₂_apply_zero_zero] at h00
  -- Conclude.
  exact sub_nonneg.mp h00

end LTFP.MathlibExt.MatrixAnalysis
