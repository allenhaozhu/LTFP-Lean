/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import LTFP.MathlibExt.MatrixAnalysis.LiebSuperoperator

/-!
# `CStarMatrix` wrappers for the Lieb left/right superoperators

This file lifts the left/right multiplication superoperators
`LiebSuperop.L` and `LiebSuperop.R` from raw matrices to the C⋆-algebra
view `CStarMatrix (n × n) (n × n) ℂ`.  The lifted operators `LC` and
`RC` agree with `L` and `R` under the `CStarMatrix.ofMatrix` type-copy
equivalence; their additional value is that they are *elements of a
C⋆-algebra* and so participate in the spectral order, the continuous
functional calculus on `CStarMatrix`, and the strict-positivity API.

These wrappers are the operator-algebra interface needed by Part 7.3
of the B6 L3 carrier (Lieb concavity via superoperator perspective).

## Main declarations

* `LiebSuperop.SuperAlg n` — abbreviation for the C⋆-algebra
  `CStarMatrix (n × n) (n × n) ℂ` in which the superoperators live.
* `LiebSuperop.LC` / `LiebSuperop.RC` — the C⋆-algebra wrappers of
  `L` and `R`.
* `LiebSuperop.LCHom` — `LC` packaged as a unital `⋆`-algebra
  homomorphism over `ℂ`.
* `LiebSuperop.LC_RC_commute` — `LC A` and `RC B` commute in
  the C⋆-algebra.
* `LiebSuperop.LC_nonneg` / `LiebSuperop.RC_strictlyPositive` —
  positivity / strict positivity of the wrappers when the underlying
  matrix is positive semidefinite / positive definite.
* `LiebSuperop.LC_rpow` — for nonneg `p`, `(LC A) ^ p = LC (A ^ p)`.
* `LiebSuperop.RC_rpow_pos` — for strictly positive `B` and *any* real
  `q`, `(RC B) ^ q = RC (B ^ q)`.  This generalises `R_rpow` from the
  base file (which only covers `q ≥ 0`) by exploiting that strictly
  positive elements have spectrum bounded away from zero, so negative
  exponents are admissible via the unital continuous functional
  calculus.

## Implementation notes

`CStarMatrix m n A` is a type copy of `Matrix m n A`, mediated by the
equivalence `CStarMatrix.ofMatrix = Equiv.refl _`.  All algebraic
operations agree strictly through this equivalence; only the *order*
differs (matrices carry the scoped `Matrix.instPartialOrder` from
`PosSemidef`, while `CStarMatrix n n A` carries the spectral order from
`CStarAlgebra.spectralOrder`).  The transfer of positivity between the
two views uses that any `StarRingEquiv` between two `StarOrderedRing`s
is automatically an `OrderIso` (`StarRingEquivClass.instOrderIsoClass`).

Since `ofMatrix` is `Equiv.refl _`, the underlying *types* are
definitionally equal; we therefore frequently leave `ofMatrix`
implicit and use `change` / `show` to bridge the C⋆-algebra view
to the raw-matrix view inside proofs.
-/

@[expose] public section

open scoped Kronecker ComplexOrder NNReal MatrixOrder
open CStarMatrix

namespace LiebSuperop

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### The carrier C⋆-algebra `SuperAlg n` -/

/-- The C⋆-algebra of `n² × n²` matrices over `ℂ` in which the
left/right multiplication superoperators live as elements. -/
abbrev SuperAlg (n : Type*) [Fintype n] [DecidableEq n] :=
  CStarMatrix (n × n) (n × n) ℂ

/-! ### `LC` and `RC`: the `CStarMatrix` wrappers -/

/-- Left-multiplication superoperator as an element of the C⋆-algebra
`SuperAlg n = CStarMatrix (n × n) (n × n) ℂ`. -/
noncomputable def LC (A : Matrix n n ℂ) : SuperAlg n :=
  CStarMatrix.ofMatrix (L A)

/-- Right-multiplication superoperator as an element of the C⋆-algebra
`SuperAlg n = CStarMatrix (n × n) (n × n) ℂ`. -/
noncomputable def RC (B : Matrix n n ℂ) : SuperAlg n :=
  CStarMatrix.ofMatrix (R B)

@[simp]
lemma LC_apply (A : Matrix n n ℂ) (i j : n × n) : LC A i j = (L A) i j := rfl

@[simp]
lemma RC_apply (B : Matrix n n ℂ) (i j : n × n) : RC B i j = (R B) i j := rfl

/-! ### Commutation of `LC` and `RC` -/

/-- `LC A` and `RC B` commute as elements of the C⋆-algebra. -/
lemma LC_RC_commute (A B : Matrix n n ℂ) : Commute (LC A) (RC B) := by
  -- The product on `CStarMatrix` is defined via `ofMatrix`-conjugated
  -- matrix multiplication, so the matrix-level commutation
  -- `L_R_commute` transports.
  unfold Commute SemiconjBy
  show CStarMatrix.ofMatrix (L A) * CStarMatrix.ofMatrix (R B)
      = CStarMatrix.ofMatrix (R B) * CStarMatrix.ofMatrix (L A)
  -- Both sides reduce to `ofMatrix (L A * R B)` resp. `ofMatrix (R B * L A)`
  -- via `ofMatrixRingEquiv.map_mul`, and the equation is `L_R_commute`.
  have hcomm : L A * R B = R B * L A := L_R_commute (n := n) A B
  show (CStarMatrix.ofMatrixRingEquiv (n := n × n) (A := ℂ) (L A))
      * (CStarMatrix.ofMatrixRingEquiv (n := n × n) (A := ℂ) (R B))
      = (CStarMatrix.ofMatrixRingEquiv (n := n × n) (A := ℂ) (R B))
      * (CStarMatrix.ofMatrixRingEquiv (n := n × n) (A := ℂ) (L A))
  rw [← map_mul, ← map_mul, hcomm]

/-! ### `LCHom`: `LC` as a `⋆`-algebra homomorphism -/

/-- `LC` packaged as a unital `⋆`-algebra homomorphism over `ℂ` from
`Matrix n n ℂ` to the C⋆-algebra `SuperAlg n`.

Built directly (not as a composition) so that `LCHom A = LC A` holds
definitionally and `simp`-rewrites cleanly. -/
noncomputable def LCHom :
    Matrix n n ℂ →⋆ₐ[ℂ] SuperAlg n where
  toFun := LC
  map_one' := by
    show CStarMatrix.ofMatrix (L (1 : Matrix n n ℂ)) = 1
    rw [L_one]
    rfl
  map_mul' A B := by
    show CStarMatrix.ofMatrix (L (A * B))
      = CStarMatrix.ofMatrix (L A) * CStarMatrix.ofMatrix (L B)
    rw [L_mul]
    rfl
  map_zero' := by
    show CStarMatrix.ofMatrix (L (0 : Matrix n n ℂ)) = 0
    rw [L_zero]
    rfl
  map_add' A B := by
    show CStarMatrix.ofMatrix (L (A + B))
      = CStarMatrix.ofMatrix (L A) + CStarMatrix.ofMatrix (L B)
    rw [L_add]
    rfl
  commutes' c := by
    -- `algebraMap ℂ _ c = c • 1` on both sides.
    show CStarMatrix.ofMatrix (L (algebraMap ℂ (Matrix n n ℂ) c))
        = algebraMap ℂ (SuperAlg n) c
    rw [Algebra.algebraMap_eq_smul_one (R := ℂ) (A := Matrix n n ℂ),
        L_smul, L_one,
        Algebra.algebraMap_eq_smul_one (R := ℂ) (A := SuperAlg n)]
    rfl
  map_star' A := by
    show CStarMatrix.ofMatrix (L (star A)) = star (CStarMatrix.ofMatrix (L A))
    rw [L_star]
    rfl

@[simp]
lemma LCHom_apply (A : Matrix n n ℂ) : LCHom A = LC A := rfl

open scoped Matrix.Norms.Elementwise in
/-- Continuity of `LCHom`: continuity of `LHom` composed with the
continuous linear equivalence `CStarMatrix.ofMatrixL`. -/
lemma continuous_LCHom : Continuous (LCHom : Matrix n n ℂ → SuperAlg n) := by
  -- `LCHom A = ofMatrix (L A) = ofMatrixL (L A)` (the linear equiv
  -- version), which is continuous.
  have h : (LCHom : Matrix n n ℂ → SuperAlg n)
      = (CStarMatrix.ofMatrixL (m := n × n) (n := n × n) (A := ℂ))
        ∘ (LHom : Matrix n n ℂ → Matrix (n × n) (n × n) ℂ) := by
    funext A
    show LC A
      = (CStarMatrix.ofMatrixL (m := n × n) (n := n × n) (A := ℂ)) (LHom A)
    rfl
  rw [h]
  exact (CStarMatrix.ofMatrixL (m := n × n) (n := n × n) (A := ℂ)).continuous.comp
    continuous_LHom

/-! ### Positivity / strict positivity of `LC` and `RC` -/

/-- `ofMatrix` transports nonnegativity from the matrix order
(`MatrixOrder` scope, via `PosSemidef`) to the spectral order on
`CStarMatrix`.  This is the order direction of the fact that
`ofMatrixStarAlgEquiv` is an `OrderIso` between two `StarOrderedRing`s
(via `StarRingEquivClass.instOrderIsoClass`). -/
lemma ofMatrix_nonneg_of_nonneg {M : Matrix (n × n) (n × n) ℂ} (hM : 0 ≤ M) :
    (0 : SuperAlg n) ≤ CStarMatrix.ofMatrix M := by
  have h := (OrderHomClass.mono
      (CStarMatrix.ofMatrixStarAlgEquiv (n := n × n) (A := ℂ))
      (a := (0 : Matrix (n × n) (n × n) ℂ)) (b := M) hM)
  simpa using h

/-- The left superoperator wrapper preserves positive semidefiniteness:
if `A.PosSemidef`, then `0 ≤ LC A` in the spectral order on
`SuperAlg n`. -/
lemma LC_nonneg {A : Matrix n n ℂ} (hA : A.PosSemidef) :
    (0 : SuperAlg n) ≤ LC A := by
  have h_raw : (0 : Matrix (n × n) (n × n) ℂ) ≤ L A :=
    Matrix.nonneg_iff_posSemidef.mpr (L_posSemidef_of_posSemidef hA)
  exact ofMatrix_nonneg_of_nonneg (n := n) h_raw

/-- The right superoperator wrapper preserves positive semidefiniteness:
if `B.PosSemidef`, then `0 ≤ RC B` in the spectral order on
`SuperAlg n`. -/
lemma RC_nonneg {B : Matrix n n ℂ} (hB : B.PosSemidef) :
    (0 : SuperAlg n) ≤ RC B := by
  have h_raw : (0 : Matrix (n × n) (n × n) ℂ) ≤ R B :=
    Matrix.nonneg_iff_posSemidef.mpr (R_posSemidef_of_posSemidef hB)
  exact ofMatrix_nonneg_of_nonneg (n := n) h_raw

/-- `ofMatrix` transports `IsUnit` (a ring-theoretic property) from
matrices to `CStarMatrix`.  Direct consequence of `ofMatrixRingEquiv`
being a ring equivalence. -/
lemma ofMatrix_isUnit_iff {M : Matrix (n × n) (n × n) ℂ} :
    IsUnit (CStarMatrix.ofMatrix M : SuperAlg n) ↔ IsUnit M := by
  constructor
  · intro h
    have hsymm : IsUnit ((CStarMatrix.ofMatrixRingEquiv
        (n := n × n) (A := ℂ)).symm
          (CStarMatrix.ofMatrix M : SuperAlg n)) := h.map _
    simpa using hsymm
  · intro h
    exact h.map (CStarMatrix.ofMatrixRingEquiv (n := n × n) (A := ℂ))

/-- The right superoperator wrapper preserves *strict* positivity:
if `B` is strictly positive (equivalently, `B.PosDef`), then so is
`RC B` in the C⋆-algebra `SuperAlg n`.

The proof routes through `Matrix.PosDef.kronecker`: with `B.PosDef`
we get `B.transpose.PosDef`; the identity is `PosDef.one`; their
Kronecker product is `(R B).PosDef`, equivalently
`IsStrictlyPositive (R B)`; finally, `ofMatrix` transports both the
nonnegativity and the invertibility. -/
lemma RC_strictlyPositive {B : Matrix n n ℂ} (hB : IsStrictlyPositive B) :
    IsStrictlyPositive (RC B) := by
  have hBdef : B.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp hB
  have h1def : (1 : Matrix n n ℂ).PosDef := Matrix.PosDef.one
  have hBtdef : (B.transpose).PosDef := hBdef.transpose
  have hRdef : (R B).PosDef := by
    unfold R
    exact hBtdef.kronecker h1def
  have hR_sp : IsStrictlyPositive (R B) := hRdef.isStrictlyPositive
  refine ⟨ofMatrix_nonneg_of_nonneg (n := n) hR_sp.nonneg, ?_⟩
  exact (ofMatrix_isUnit_iff (n := n) (M := R B)).mpr hR_sp.isUnit

/-! ### Compatibility of `LC` with real powers via the CFC -/

/-- The left superoperator wrapper `LC` commutes with nonneg real
powers on positive semidefinite matrices:
`(LC A) ^ p = LC (A ^ p)`.

The proof transports `L_rpow` through the C⋆-algebra view using
`StarAlgHom.map_cfc` for the bundled `LCHom`. -/
lemma LC_rpow {A : Matrix n n ℂ} {p : ℝ} (hp : 0 ≤ p) (hA : A.PosSemidef) :
    (LC A) ^ p = LC (A ^ p) := by
  -- Nonnegativity witnesses for the CFC predicate (`R := ℝ≥0`).
  have hA0 : (0 : Matrix n n ℂ) ≤ A := hA.nonneg
  have hLCA0 : (0 : SuperAlg n) ≤ LCHom A := LC_nonneg (n := n) hA
  -- Continuity of `x ↦ x ^ p` on `ℝ≥0`.
  have hcont : Continuous (fun x : ℝ≥0 => x ^ p) := NNReal.continuous_rpow_const hp
  -- Transport the CFC through `LCHom`.
  have hmap :=
    (LCHom (n := n)).map_cfc (S := ℂ) (R := ℝ≥0)
      (fun x : ℝ≥0 => x ^ p) A hcont.continuousOn continuous_LCHom hA0 hLCA0
  -- Unfold `^ p` on both sides via `CFC.rpow_def`.
  simp only [LCHom_apply] at hmap
  show cfc (fun x : ℝ≥0 => x ^ p) (LC A) = LC (A ^ p)
  exact hmap.symm

/-! ### Compatibility of `RC` with all real powers on strictly positive `B`

For strictly positive `B`, the spectrum of `B` (and hence of `RC B`)
is bounded away from zero, so the unital continuous functional
calculus admits the function `x ↦ x ^ q` for *any* real `q` (not just
`q ≥ 0`).  We route through `Rconj` (which is a genuine real
`*`-algebra homomorphism) and the `CStarMatrix.ofMatrix` equivalence.
-/

/-- `RC B` agrees with `ofMatrix (Rconj B)` whenever `B` is Hermitian. -/
private lemma RC_eq_ofMatrix_Rconj_of_isHermitian
    {B : Matrix n n ℂ} (hB : B.IsHermitian) :
    RC B = CStarMatrix.ofMatrix (Rconj B) := by
  show CStarMatrix.ofMatrix (R B) = CStarMatrix.ofMatrix (Rconj B)
  rw [R_eq_Rconj_of_isHermitian hB]

/-- `RconjCHom`: `Rconj` followed by `CStarMatrix.ofMatrix`, packaged
as a unital real `⋆`-algebra homomorphism. -/
noncomputable def RconjCHom :
    Matrix n n ℂ →⋆ₐ[ℝ] SuperAlg n where
  toFun := fun B => CStarMatrix.ofMatrix (Rconj B)
  map_one' := by
    show CStarMatrix.ofMatrix (Rconj (1 : Matrix n n ℂ)) = 1
    rw [Rconj_one]
    rfl
  map_mul' A B := by
    show CStarMatrix.ofMatrix (Rconj (A * B))
      = CStarMatrix.ofMatrix (Rconj A) * CStarMatrix.ofMatrix (Rconj B)
    rw [Rconj_mul]
    rfl
  map_zero' := by
    show CStarMatrix.ofMatrix (Rconj (0 : Matrix n n ℂ)) = 0
    rw [Rconj_zero]
    rfl
  map_add' A B := by
    show CStarMatrix.ofMatrix (Rconj (A + B))
      = CStarMatrix.ofMatrix (Rconj A) + CStarMatrix.ofMatrix (Rconj B)
    rw [Rconj_add]
    rfl
  commutes' r := by
    show CStarMatrix.ofMatrix (Rconj (algebraMap ℝ (Matrix n n ℂ) r))
        = algebraMap ℝ (SuperAlg n) r
    rw [Algebra.algebraMap_eq_smul_one (R := ℝ) (A := Matrix n n ℂ),
        Rconj_smul_real, Rconj_one,
        Algebra.algebraMap_eq_smul_one (R := ℝ) (A := SuperAlg n)]
    rfl
  map_star' B := by
    show CStarMatrix.ofMatrix (Rconj (star B))
      = star (CStarMatrix.ofMatrix (Rconj B))
    rw [Rconj_star]
    rfl

@[simp]
lemma RconjCHom_apply (B : Matrix n n ℂ) :
    RconjCHom B = CStarMatrix.ofMatrix (Rconj B) := rfl

open scoped Matrix.Norms.Elementwise in
/-- Continuity of `RconjCHom`: continuity of `RconjHom` composed with
the continuous linear equivalence `CStarMatrix.ofMatrixL`. -/
lemma continuous_RconjCHom :
    Continuous (RconjCHom : Matrix n n ℂ → SuperAlg n) := by
  have h : (RconjCHom : Matrix n n ℂ → SuperAlg n)
      = (CStarMatrix.ofMatrixL (m := n × n) (n := n × n) (A := ℂ))
        ∘ (RconjHom : Matrix n n ℂ → Matrix (n × n) (n × n) ℂ) := by
    funext B
    show CStarMatrix.ofMatrix (Rconj B)
      = (CStarMatrix.ofMatrixL (m := n × n) (n := n × n) (A := ℂ)) (RconjHom B)
    rfl
  rw [h]
  exact (CStarMatrix.ofMatrixL (m := n × n) (n := n × n) (A := ℂ)).continuous.comp
    continuous_RconjHom

/-- The right superoperator wrapper `RC` commutes with **all** real
powers on *strictly positive* matrices `B`:
`(RC B) ^ q = RC (B ^ q)` for any real `q`.

This generalises `R_rpow` (which requires `q ≥ 0`) by exploiting that
strictly positive `B` has spectrum (in `ℝ≥0`) bounded away from zero,
so `x ↦ x ^ q` is continuous on `spectrum ℝ≥0 B` for any real `q`. -/
lemma RC_rpow_pos {B : Matrix n n ℂ} {q : ℝ} (hB : IsStrictlyPositive B) :
    (RC B) ^ q = RC (B ^ q) := by
  -- Hermitian / nonnegativity witnesses.
  have hB0 : (0 : Matrix n n ℂ) ≤ B := hB.nonneg
  have hBpsd : B.PosSemidef := Matrix.nonneg_iff_posSemidef.mp hB0
  have hBherm : B.IsHermitian := hBpsd.isHermitian
  -- `B^q` is also nonnegative, in particular hermitian.
  have hBq0 : (0 : Matrix n n ℂ) ≤ B ^ q := CFC.rpow_nonneg
  have hBqpsd : (B ^ q).PosSemidef := Matrix.nonneg_iff_posSemidef.mp hBq0
  have hBqherm : (B ^ q).IsHermitian := hBqpsd.isHermitian
  -- Strict positivity of `RC B` (the LHS argument of `cfc` on
  -- `CStarMatrix`).
  have hRC_sp : IsStrictlyPositive (RC B) := RC_strictlyPositive (n := n) hB
  have hRC0 : (0 : SuperAlg n) ≤ RC B := hRC_sp.nonneg
  -- Rewrite via the `Rconj` surrogate so that we can transport along
  -- the real `⋆`-algebra homomorphism `RconjCHom = ofMatrix ∘ Rconj`.
  rw [RC_eq_ofMatrix_Rconj_of_isHermitian (n := n) hBherm,
      RC_eq_ofMatrix_Rconj_of_isHermitian (n := n) hBqherm]
  -- Now both sides are expressed in the form `ofMatrix (Rconj ·)`.
  -- `RconjCHom B = ofMatrix (Rconj B)`.
  have hRC_nonneg : (0 : SuperAlg n) ≤ RconjCHom B := by
    show (0 : SuperAlg n) ≤ CStarMatrix.ofMatrix (Rconj B)
    have := hRC0
    rw [RC_eq_ofMatrix_Rconj_of_isHermitian (n := n) hBherm] at this
    exact this
  -- Continuity of `x ↦ x ^ q` on `spectrum ℝ≥0 B`.
  -- Strictly positive ⇒ spectrum is bounded away from 0, so `x ^ q`
  -- is continuous on the spectrum even for `q < 0`.
  have hq_cont : ContinuousOn (fun x : ℝ≥0 => x ^ q) (spectrum ℝ≥0 B) := by
    refine NNReal.continuousOn_rpow_const (.inl ?_)
    exact spectrum.zero_notMem _ hB.isUnit
  -- Transport CFC through the real ⋆-algebra hom `RconjCHom`.
  have hmap :=
    (RconjCHom (n := n)).map_cfc (S := ℝ) (R := ℝ≥0)
      (fun x : ℝ≥0 => x ^ q) B hq_cont continuous_RconjCHom hB0 hRC_nonneg
  simp only [RconjCHom_apply] at hmap
  -- Now both sides match the rpow definition; convert each via
  -- `CFC.rpow_def`.
  show (CStarMatrix.ofMatrix (Rconj B)) ^ q
      = CStarMatrix.ofMatrix (Rconj (B ^ q))
  rw [show ((CStarMatrix.ofMatrix (Rconj B)) ^ q : SuperAlg n)
        = cfc (fun x : ℝ≥0 => x ^ q) (CStarMatrix.ofMatrix (Rconj B))
        from _root_.CFC.rpow_def,
      show (B ^ q : Matrix n n ℂ)
        = cfc (fun x : ℝ≥0 => x ^ q) B from _root_.CFC.rpow_def]
  exact hmap.symm

end LiebSuperop
