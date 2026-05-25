/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Closedness of the positive-semidefinite cone in `Matrix n n ℂ`

For a finite index type `n`, the set of positive-semidefinite matrices
`{A : Matrix n n ℂ | A.PosSemidef}` is closed in the natural product
topology on `Matrix n n ℂ`.

The proof uses the dot-product characterisation
`Matrix.posSemidef_iff_dotProduct_mulVec`:

  `A.PosSemidef ↔ A.IsHermitian ∧ ∀ x, 0 ≤ star x ⬝ᵥ (A *ᵥ x)`.

Both conjuncts cut out closed sets:

* `{A | A.IsHermitian}` is the equalizer of the two continuous maps
  `A ↦ Aᴴ` and `A ↦ A`.
* For each fixed `x : n → ℂ`, the map `A ↦ star x ⬝ᵥ (A *ᵥ x)` is continuous
  in `A`, and `{z : ℂ | 0 ≤ z}` is closed under `ComplexOrder`
  (it is the preimage of the closed sets `{z | 0 ≤ z.re}` and `{z | z.im = 0}`).
  Hence `{A | 0 ≤ star x ⬝ᵥ (A *ᵥ x)}` is closed for each `x`,
  and the intersection over all `x` is closed.

This module also derives, as a useful corollary in the Loewner order on
`Matrix n n ℂ`, that any Loewner interval `{A | A.IsHermitian ∧ r • 1 ≤ A ∧ A ≤ R' • 1}`
is closed. This is the typical "spectral box" set used to assert that a
limit of bounded operators remains bounded.

This file is a candidate for upstream Mathlib contribution: closedness of
the PSD cone in the matrix-norm topology is fundamentally useful and is
not currently provided.
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Complex.Order
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Complex

open scoped ComplexOrder MatrixOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- For each fixed vector `x : n → ℂ`, the quadratic form
`A ↦ star x ⬝ᵥ (A *ᵥ x)` is continuous in the matrix entry `A`. -/
theorem continuous_dotProduct_mulVec (x : n → ℂ) :
    Continuous fun A : Matrix n n ℂ => star x ⬝ᵥ (A *ᵥ x) :=
  (continuous_const : Continuous fun _ : Matrix n n ℂ => star x).dotProduct
    (continuous_id.matrix_mulVec continuous_const)

omit [Fintype n] [DecidableEq n] in
/-- The set of Hermitian matrices is closed in `Matrix n n ℂ`. -/
theorem isClosed_setOf_isHermitian :
    IsClosed {A : Matrix n n ℂ | A.IsHermitian} := by
  -- `IsHermitian A` unfolds to `Aᴴ = A`, the equalizer of two continuous maps.
  have h : {A : Matrix n n ℂ | A.IsHermitian} = {A | Aᴴ = A} := rfl
  rw [h]
  exact isClosed_eq continuous_id.matrix_conjTranspose continuous_id

/-- The closed nonnegative half-space `{z : ℂ | 0 ≤ z}` in the
`ComplexOrder` partial order. -/
theorem _root_.Complex.isClosed_setOf_nonneg :
    IsClosed {z : ℂ | 0 ≤ z} := by
  -- `0 ≤ z ↔ 0 ≤ z.re ∧ 0 = z.im`.
  have hset :
      {z : ℂ | 0 ≤ z} = {z : ℂ | 0 ≤ z.re} ∩ {z : ℂ | (0 : ℝ) = z.im} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Complex.nonneg_iff]
  rw [hset]
  refine IsClosed.inter ?_ ?_
  · exact isClosed_le continuous_const Complex.continuous_re
  · exact isClosed_eq continuous_const Complex.continuous_im

omit [DecidableEq n] in
/-- **Main result**: the set of positive-semidefinite matrices
`{A : Matrix n n ℂ | A.PosSemidef}` is closed in `Matrix n n ℂ`.

This is a candidate upstream Mathlib lemma. The proof is the standard
quadratic-form argument: PSD is cut out by countably many continuous
linear inequalities `0 ≤ ⟨x, A x⟩` together with the (closed) Hermitian
condition. -/
theorem isClosed_posSemidef :
    IsClosed {A : Matrix n n ℂ | A.PosSemidef} := by
  -- Rewrite via the dot-product characterisation
  -- `A.PosSemidef ↔ A.IsHermitian ∧ ∀ x, 0 ≤ star x ⬝ᵥ (A *ᵥ x)`.
  have hset :
      {A : Matrix n n ℂ | A.PosSemidef}
        = {A : Matrix n n ℂ | A.IsHermitian} ∩
          ⋂ x : n → ℂ, {A : Matrix n n ℂ | 0 ≤ star x ⬝ᵥ (A *ᵥ x)} := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    exact Matrix.posSemidef_iff_dotProduct_mulVec
  rw [hset]
  refine IsClosed.inter isClosed_setOf_isHermitian ?_
  refine isClosed_iInter (fun x => ?_)
  -- For each `x`, the set `{A | 0 ≤ ⟨x, A x⟩}` is the preimage of the
  -- closed half-space `{z : ℂ | 0 ≤ z}` under the continuous map
  -- `A ↦ star x ⬝ᵥ (A *ᵥ x)`.
  have : {A : Matrix n n ℂ | 0 ≤ star x ⬝ᵥ (A *ᵥ x)}
      = (fun A : Matrix n n ℂ => star x ⬝ᵥ (A *ᵥ x)) ⁻¹' {z : ℂ | 0 ≤ z} := rfl
  rw [this]
  exact Complex.isClosed_setOf_nonneg.preimage (continuous_dotProduct_mulVec x)

omit [DecidableEq n] in
/-- The Loewner-nonnegative cone `{A | 0 ≤ A}` is closed in `Matrix n n ℂ`.

Under the `MatrixOrder` partial order, `0 ≤ A` is equivalent to `A.PosSemidef`. -/
theorem isClosed_setOf_nonneg :
    IsClosed {A : Matrix n n ℂ | (0 : Matrix n n ℂ) ≤ A} := by
  have hset :
      {A : Matrix n n ℂ | (0 : Matrix n n ℂ) ≤ A}
        = {A : Matrix n n ℂ | A.PosSemidef} := by
    ext A; exact Matrix.nonneg_iff_posSemidef
  rw [hset]
  exact isClosed_posSemidef

omit [DecidableEq n] in
/-- For any fixed `B : Matrix n n ℂ`, the Loewner upper half-space
`{A | B ≤ A}` is closed. -/
theorem isClosed_setOf_le_left (B : Matrix n n ℂ) :
    IsClosed {A : Matrix n n ℂ | B ≤ A} := by
  -- `B ≤ A ↔ (A - B).PosSemidef`, so this is the preimage of
  -- `{C | C.PosSemidef}` under the continuous map `A ↦ A - B`.
  have hset :
      {A : Matrix n n ℂ | B ≤ A}
        = (fun A : Matrix n n ℂ => A - B) ⁻¹' {C | C.PosSemidef} := by
    ext A; exact Matrix.le_iff
  rw [hset]
  exact isClosed_posSemidef.preimage (continuous_id.sub continuous_const)

omit [DecidableEq n] in
/-- For any fixed `B : Matrix n n ℂ`, the Loewner lower half-space
`{A | A ≤ B}` is closed. -/
theorem isClosed_setOf_le_right (B : Matrix n n ℂ) :
    IsClosed {A : Matrix n n ℂ | A ≤ B} := by
  have hset :
      {A : Matrix n n ℂ | A ≤ B}
        = (fun A : Matrix n n ℂ => B - A) ⁻¹' {C | C.PosSemidef} := by
    ext A; exact Matrix.le_iff
  rw [hset]
  exact isClosed_posSemidef.preimage (continuous_const.sub continuous_id)

/-- **Useful corollary**: the Loewner-spectral box
`{A | A.IsHermitian ∧ r • 1 ≤ A ∧ A ≤ R' • 1}` is closed in `Matrix n n ℂ`.

This is the canonical "matrices with spectrum in `[r, R']`" set used to
assert that a limit of uniformly Loewner-bounded matrices remains
bounded. -/
theorem isClosed_Icc_smul_one (r R' : ℝ) :
    IsClosed {A : Matrix n n ℂ |
      A.IsHermitian ∧ (r • (1 : Matrix n n ℂ)) ≤ A ∧ A ≤ R' • (1 : Matrix n n ℂ)} := by
  -- Rewrite as a triple intersection of closed sets.
  have hset :
      {A : Matrix n n ℂ |
        A.IsHermitian ∧ (r • (1 : Matrix n n ℂ)) ≤ A ∧ A ≤ R' • (1 : Matrix n n ℂ)}
        = {A : Matrix n n ℂ | A.IsHermitian}
          ∩ {A : Matrix n n ℂ | (r • (1 : Matrix n n ℂ)) ≤ A}
          ∩ {A : Matrix n n ℂ | A ≤ R' • (1 : Matrix n n ℂ)} := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    tauto
  rw [hset]
  refine IsClosed.inter (IsClosed.inter isClosed_setOf_isHermitian ?_) ?_
  · exact isClosed_setOf_le_left (r • (1 : Matrix n n ℂ))
  · exact isClosed_setOf_le_right (R' • (1 : Matrix n n ℂ))

end Matrix
