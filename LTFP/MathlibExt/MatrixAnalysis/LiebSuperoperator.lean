/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Lieb superoperators on `Matrix (n × n) (n × n) ℂ`

This file introduces the **left** and **right** multiplication
superoperators on matrices over `ℂ`, encoded as Kronecker-product
matrices on the doubled index `n × n`.  These operators are the
algebraic substrate of Lieb's concavity theorem (1973) and the basic
machinery for the operator-valued Jensen / Hansen–Pedersen calculus.

Concretely, for `A B : Matrix n n ℂ`,

```
L A := 1 ⊗ₖ A             -- acts as  X ↦ A * X        (in vectorized form)
R B := Bᵀ ⊗ₖ 1            -- acts as  X ↦ X * B        (in vectorized form)
```

The choice of `Bᵀ` (rather than `B`) for the right superoperator is
standard and follows from the identity

```
vec (A * X * B) = (Bᵀ ⊗ A) * vec X.
```

## Main results

* `LiebSuperop.L_add`, `LiebSuperop.L_smul`,
  `LiebSuperop.R_add`, `LiebSuperop.R_smul`
  — affine behaviour of `L` and `R` in their matrix argument.
* `LiebSuperop.L_mul_R` and `LiebSuperop.R_mul_L`
  — both compositions equal `Bᵀ ⊗ₖ A`.
* `LiebSuperop.L_R_commute` — the left and right superoperators commute.
* `LiebSuperop.L_posSemidef_of_posSemidef`,
  `LiebSuperop.R_posSemidef_of_posSemidef`
  — `L A` (resp. `R B`) is positive semidefinite whenever `A` (resp. `B`)
  is positive semidefinite.

## Implementation notes

We package both superoperators inside the `LiebSuperop` namespace so
that downstream files importing this module can write `LiebSuperop.L A`
and `LiebSuperop.R B` without name collisions with the algebraic
left/right multiplication operators on `n × n` matrices.
-/

open scoped Kronecker ComplexOrder NNReal

namespace LiebSuperop

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Left-multiplication superoperator: the matrix on the doubled index
`n × n` that represents the linear map `X ↦ A * X`.  Encoded as the
Kronecker product `1 ⊗ₖ A`. -/
noncomputable def L (A : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ :=
  (1 : Matrix n n ℂ) ⊗ₖ A

/-- Right-multiplication superoperator: the matrix on the doubled index
`n × n` that represents the linear map `X ↦ X * B`.  Encoded as the
Kronecker product `Bᵀ ⊗ₖ 1`. -/
noncomputable def R (B : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ :=
  B.transpose ⊗ₖ (1 : Matrix n n ℂ)

/-! ### Affine behaviour -/

omit [Fintype n] in
@[simp]
lemma L_add (A₁ A₂ : Matrix n n ℂ) : L (A₁ + A₂) = L A₁ + L A₂ := by
  unfold L
  exact Matrix.kroneckerMap_add_right (· * ·) (fun a b₁ b₂ => mul_add a b₁ b₂) _ _ _

omit [Fintype n] in
@[simp]
lemma L_smul (c : ℂ) (A : Matrix n n ℂ) : L (c • A) = c • L A := by
  unfold L
  exact Matrix.kroneckerMap_smul_right (· * ·) c
    (fun a b => Algebra.mul_smul_comm c a b) _ _

omit [Fintype n] in
@[simp]
lemma R_add (B₁ B₂ : Matrix n n ℂ) : R (B₁ + B₂) = R B₁ + R B₂ := by
  unfold R
  simp only [Matrix.transpose_add]
  exact Matrix.kroneckerMap_add_left (· * ·) (fun a₁ a₂ b => add_mul a₁ a₂ b) _ _ _

omit [Fintype n] in
@[simp]
lemma R_smul (c : ℂ) (B : Matrix n n ℂ) : R (c • B) = c • R B := by
  unfold R
  simp only [Matrix.transpose_smul]
  exact Matrix.kroneckerMap_smul_left (· * ·) c
    (fun a b => Algebra.smul_mul_assoc c a b) _ _

/-! ### Commutation of the left and right superoperators -/

/-- Composing the left and right superoperators yields the Kronecker
product `Bᵀ ⊗ₖ A`. -/
lemma L_mul_R (A B : Matrix n n ℂ) :
    L A * R B = B.transpose ⊗ₖ A := by
  unfold L R
  -- `(1 ⊗ Bᵀ) * (... ) = (1 * Bᵀ) ⊗ (A * 1)` via `mul_kronecker_mul`.
  rw [← Matrix.mul_kronecker_mul]
  simp

/-- Composing the right and left superoperators yields the Kronecker
product `Bᵀ ⊗ₖ A`. -/
lemma R_mul_L (A B : Matrix n n ℂ) :
    R B * L A = B.transpose ⊗ₖ A := by
  unfold L R
  rw [← Matrix.mul_kronecker_mul]
  simp

/-- The left and right superoperators commute as matrices on `n × n`. -/
lemma L_R_commute (A B : Matrix n n ℂ) : Commute (L A) (R B) := by
  unfold Commute SemiconjBy
  rw [L_mul_R, R_mul_L]

/-! ### Positivity preservation -/

/-- The left superoperator preserves positive semidefiniteness. -/
lemma L_posSemidef_of_posSemidef
    {A : Matrix n n ℂ} (hA : A.PosSemidef) : (L A).PosSemidef := by
  unfold L
  exact (Matrix.PosSemidef.one : (1 : Matrix n n ℂ).PosSemidef).kronecker hA

/-- The right superoperator preserves positive semidefiniteness.

Note: since `B.PosSemidef` implies `B.IsHermitian`, the transpose `Bᵀ`
is also positive semidefinite, and the Kronecker product of two PSD
matrices is PSD. -/
lemma R_posSemidef_of_posSemidef
    {B : Matrix n n ℂ} (hB : B.PosSemidef) : (R B).PosSemidef := by
  unfold R
  exact hB.transpose.kronecker
    (Matrix.PosSemidef.one : (1 : Matrix n n ℂ).PosSemidef)

/-! ### Algebra laws

The following five lemmas establish that `L` is a unital `*`-algebra
homomorphism (preserves `0`, `1`, multiplication, and the star
operation) and that `R` is an anti-multiplicative map.  These are the
basic structural facts about the left/right multiplication
superoperators and form the algebraic backbone for downstream Lieb /
Hansen–Pedersen / Effros calculations.
-/

omit [Fintype n] in
@[simp]
lemma L_zero : L (0 : Matrix n n ℂ) = 0 := by
  unfold L
  exact Matrix.kronecker_zero _

omit [Fintype n] in
@[simp]
lemma L_one : L (1 : Matrix n n ℂ) = 1 := by
  unfold L
  exact Matrix.one_kronecker_one

lemma L_mul (A B : Matrix n n ℂ) : L (A * B) = L A * L B := by
  unfold L
  rw [← Matrix.mul_kronecker_mul]
  simp

omit [Fintype n] in
lemma L_star (A : Matrix n n ℂ) : L (star A) = star (L A) := by
  unfold L
  rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_kronecker]
  simp

lemma R_mul_rev (B₁ B₂ : Matrix n n ℂ) : R (B₁ * B₂) = R B₂ * R B₁ := by
  unfold R
  rw [Matrix.transpose_mul, ← Matrix.mul_kronecker_mul]
  simp

/-! ### `L` as a `*`-algebra homomorphism and its continuity

The affine, multiplicative, unital, and `star`-preserving behaviour of
`L` established above is repackaged here as a `StarAlgHom` over `ℂ`.
We then derive continuity from finite dimensionality, using the
elementwise matrix norm scope (`Matrix.Norms.Elementwise`) to expose
the relevant `NormedAddCommGroup` / `NormedSpace` instances.
-/

/-- The left superoperator `L`, packaged as a unital `*`-algebra
homomorphism from `Matrix n n ℂ` to `Matrix (n × n) (n × n) ℂ`. -/
noncomputable def LHom :
    Matrix n n ℂ →⋆ₐ[ℂ] Matrix (n × n) (n × n) ℂ where
  toFun := L
  map_one' := L_one
  map_mul' := L_mul
  map_zero' := L_zero
  map_add' := L_add
  commutes' := fun c => by
    -- `algebraMap ℂ (Matrix m m ℂ) c = c • 1` on both sides.
    simp only [Algebra.algebraMap_eq_smul_one, L_smul, L_one]
  map_star' := L_star

@[simp]
lemma LHom_apply (A : Matrix n n ℂ) : LHom A = L A := rfl

open scoped Matrix.Norms.Elementwise in
/-- The left superoperator `L` is continuous: it is a `ℂ`-linear map
between finite-dimensional `ℂ`-vector spaces (using the elementwise
matrix norm). -/
lemma continuous_LHom :
    Continuous (LHom : Matrix n n ℂ → Matrix (n × n) (n × n) ℂ) := by
  -- Expose `L` as a `ℂ`-linear map and invoke continuity from finite
  -- dimensionality.
  let Llin : Matrix n n ℂ →ₗ[ℂ] Matrix (n × n) (n × n) ℂ :=
    { toFun := L
      map_add' := L_add
      map_smul' := fun c A => L_smul c A }
  change Continuous (Llin : Matrix n n ℂ → Matrix (n × n) (n × n) ℂ)
  exact Llin.continuous_of_finiteDimensional

/-! ### Compatibility of `L` with real powers via the CFC

For a positive semidefinite `A : Matrix n n ℂ` and a nonnegative real
exponent `r`, the left superoperator `L` commutes with the operator
`rpow`: `(L A) ^ r = L (A ^ r)`.  This is the matrix-level instance of
the general fact that star algebra homomorphisms commute with the
continuous functional calculus (`StarAlgHom.map_cfc`), specialized to
the function `x ↦ x ^ r` on `ℝ≥0`.
-/

open scoped MatrixOrder in
/-- The left superoperator `L` commutes with real powers on positive
semidefinite matrices: `(L A) ^ r = L (A ^ r)`. -/
lemma L_rpow (A : Matrix n n ℂ) {r : ℝ} (hr : 0 ≤ r) (hA : A.PosSemidef) :
    (L A) ^ r = L (A ^ r) := by
  -- Strategy: rewrite both sides via `CFC.rpow_def` to expose the
  -- continuous functional calculus, then transport across `LHom`
  -- using `StarAlgHom.map_cfc`.
  have hA0 := hA.nonneg
  have hLA0 := (L_posSemidef_of_posSemidef hA).nonneg
  have hcont : Continuous (fun x : ℝ≥0 => x ^ r) := NNReal.continuous_rpow_const hr
  -- Transport the CFC across the star-algebra homomorphism `LHom`.
  have hmap :=
    (LHom (n := n)).map_cfc (S := ℂ) (R := ℝ≥0)
      (fun x : ℝ≥0 => x ^ r) A hcont.continuousOn continuous_LHom hA0 hLA0
  -- Unfold both `rpow`s and rewrite via `hmap`.
  simp only [LHom_apply] at hmap
  exact hmap.symm

/-! ### `Rconj`: the conjugated right superoperator

For the Hermitian setting we will also need the *conjugated* right
superoperator, defined using the entrywise complex conjugate `B.map star`
in place of the transpose `Bᵀ`.  For Hermitian `B`, the entrywise
relation `Bᴴ = B` gives `Bᵀ = B.map star`, hence `R B = Rconj B`.

This surrogate is the form in which the Lieb concavity calculation is
most naturally expressed, since `Rconj B` is the Kronecker product of
two `*`-related copies of `B`.
-/

/-- The *conjugated* right-multiplication superoperator: the Kronecker
product of the entrywise complex conjugate of `B` with the identity.
For Hermitian `B`, this coincides with the ordinary right
superoperator `R B`; see `R_eq_Rconj_of_isHermitian`. -/
noncomputable def Rconj (B : Matrix n n ℂ) : Matrix (n × n) (n × n) ℂ :=
  B.map star ⊗ₖ (1 : Matrix n n ℂ)

omit [Fintype n] in
/-- For a Hermitian matrix `B`, the ordinary right superoperator `R B`
(defined via the transpose) and the conjugated variant `Rconj B`
(defined via the entrywise complex conjugate) coincide.  This is a
direct consequence of the entrywise Hermitian identity
`star (B j i) = B i j`, which gives `Bᵀ = B.map star`. -/
lemma R_eq_Rconj_of_isHermitian {B : Matrix n n ℂ} (hB : B.IsHermitian) :
    R B = Rconj B := by
  unfold R Rconj
  -- It suffices to show `B.transpose = B.map star` entrywise.
  congr 1
  ext i j
  -- Goal: `B.transpose i j = B.map star i j`, i.e. `B j i = star (B i j)`.
  simp only [Matrix.transpose_apply, Matrix.map_apply]
  exact (hB.apply j i).symm

/-! ### Algebra laws for `Rconj`

Unlike `R`, the conjugated right superoperator `Rconj` is genuinely
*multiplicative* (not anti-multiplicative): the matrix index order is
unchanged under entrywise conjugation, so `(A * B).map star =
A.map star * B.map star` and the Kronecker bilinearity yields
`Rconj (A * B) = Rconj A * Rconj B`.

Together with `Rconj_zero`, `Rconj_one`, `Rconj_add`, `Rconj_smul_real`,
and `Rconj_star`, this packages `Rconj` as a unital `*`-algebra
homomorphism over `ℝ` (not over `ℂ`: scalar multiplication only commutes
with `Rconj` after conjugating the scalar; for real scalars `r`, the
conjugate is `r` itself, so ℝ-linearity is automatic).
-/

omit [Fintype n] in
@[simp]
lemma Rconj_zero : Rconj (0 : Matrix n n ℂ) = 0 := by
  unfold Rconj
  simp only [Matrix.map_zero _ (star_zero ℂ)]
  exact Matrix.zero_kronecker _

omit [Fintype n] in
@[simp]
lemma Rconj_one : Rconj (1 : Matrix n n ℂ) = 1 := by
  unfold Rconj
  -- `(1 : Matrix n n ℂ).map star = 1` entrywise.
  have h1 : ((1 : Matrix n n ℂ).map star) = (1 : Matrix n n ℂ) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.one_apply_eq, Matrix.map_apply]
    · simp [Matrix.one_apply_ne hij, Matrix.map_apply]
  rw [h1]
  exact Matrix.one_kronecker_one

omit [Fintype n] in
@[simp]
lemma Rconj_add (B₁ B₂ : Matrix n n ℂ) :
    Rconj (B₁ + B₂) = Rconj B₁ + Rconj B₂ := by
  unfold Rconj
  -- `(B₁ + B₂).map star = B₁.map star + B₂.map star` since `star`
  -- distributes over addition on `ℂ`.
  have hadd : (B₁ + B₂).map (star : ℂ → ℂ) =
      B₁.map star + B₂.map star := by
    ext i j; simp [Matrix.map_apply, Matrix.add_apply]
  rw [hadd]
  exact Matrix.kroneckerMap_add_left (· * ·)
    (fun a₁ a₂ b => add_mul a₁ a₂ b) _ _ _

omit [Fintype n] in
/-- For a *real* scalar `r`, the conjugated right superoperator is
`ℝ`-linear: `Rconj (r • B) = r • Rconj B`.  Note: this only holds for
real scalars; for general complex scalars the conjugate appears,
`Rconj (c • B) = star c • Rconj B`. -/
@[simp]
lemma Rconj_smul_real (r : ℝ) (B : Matrix n n ℂ) :
    Rconj (r • B) = r • Rconj B := by
  unfold Rconj
  -- `(r • B).map star = r • B.map star`, because `star (r • z) = r • star z`
  -- when `r` is real (the real scalar passes through conjugation unchanged).
  have hsmul : (r • B).map (star : ℂ → ℂ) = r • B.map star := by
    ext i j
    simp [Matrix.map_apply, Matrix.smul_apply]
  rw [hsmul]
  exact Matrix.kroneckerMap_smul_left (· * ·) (r : ℂ)
    (fun a b => Algebra.smul_mul_assoc (r : ℂ) a b) _ _

lemma Rconj_mul (A B : Matrix n n ℂ) :
    Rconj (A * B) = Rconj A * Rconj B := by
  unfold Rconj
  -- (A * B).map star = A.map star * B.map star, via `Matrix.map_mul`
  -- with the ring homomorphism `starRingEnd ℂ`.
  have hmul : (A * B).map (star : ℂ → ℂ) =
      A.map star * B.map star := by
    -- Apply `Matrix.map_mul` via the bundled `starRingEnd ℂ` and identify
    -- `star : ℂ → ℂ` with `(starRingEnd ℂ : ℂ → ℂ)`.
    show (A * B).map ((starRingEnd ℂ : ℂ →+* ℂ) : ℂ → ℂ) =
      A.map ((starRingEnd ℂ : ℂ →+* ℂ) : ℂ → ℂ) *
      B.map ((starRingEnd ℂ : ℂ →+* ℂ) : ℂ → ℂ)
    exact Matrix.map_mul (f := starRingEnd ℂ) (L := A) (M := B)
  rw [hmul]
  -- (A.map star * B.map star) ⊗ 1 = (A.map star ⊗ 1) * (B.map star ⊗ 1)
  rw [← Matrix.mul_kronecker_mul]
  simp

omit [Fintype n] in
lemma Rconj_star (B : Matrix n n ℂ) :
    Rconj (star B) = star (Rconj B) := by
  unfold Rconj
  -- Strategy: rewrite both matrix-level `star`s to `conjTranspose`, then
  -- distribute conjTranspose over the Kronecker product on the RHS,
  -- and finally show the two Kronecker factors agree entrywise.
  rw [show (star (B.map star ⊗ₖ (1 : Matrix n n ℂ)) :
        Matrix (n × n) (n × n) ℂ) =
      (B.map star ⊗ₖ (1 : Matrix n n ℂ)).conjTranspose from
        Matrix.star_eq_conjTranspose _,
      Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
  -- Goal:  (star B).map star ⊗ₖ 1 = (B.map star).conjTranspose ⊗ₖ 1
  -- The two Kronecker factors agree definitionally:
  -- both unfold to `fun i j => star (star (B j i))`.
  rfl

/-! ### `Rconj` as a real `*`-algebra homomorphism and its continuity

We package the lemmas above into a unital `*`-algebra homomorphism
`RconjHom` over `ℝ` (not over `ℂ`, since `Rconj` is only conjugate-linear
over `ℂ` — see `Rconj_smul_real`).  Continuity follows from finite
dimensionality of `Matrix n n ℂ` as an `ℝ`-vector space.
-/

/-- The conjugated right superoperator `Rconj`, packaged as a unital
real `*`-algebra homomorphism from `Matrix n n ℂ` to
`Matrix (n × n) (n × n) ℂ`.

Note: only ℝ-linearity is supported here, since `Rconj (c • B) =
(star c) • Rconj B` for general `c : ℂ`. For real scalars `r`, the
conjugate is `r` itself, so ℝ-linearity follows from `Rconj_smul_real`. -/
noncomputable def RconjHom :
    Matrix n n ℂ →⋆ₐ[ℝ] Matrix (n × n) (n × n) ℂ where
  toFun := Rconj
  map_one' := Rconj_one
  map_mul' := Rconj_mul
  map_zero' := Rconj_zero
  map_add' := Rconj_add
  commutes' := fun r => by
    -- `algebraMap ℝ (Matrix n n ℂ) r = r • 1` on both sides.
    simp only [Algebra.algebraMap_eq_smul_one, Rconj_smul_real, Rconj_one]
  map_star' := Rconj_star

@[simp]
lemma RconjHom_apply (B : Matrix n n ℂ) : RconjHom B = Rconj B := rfl

open scoped Matrix.Norms.Elementwise in
/-- The conjugated right superoperator `Rconj` is continuous: it is an
`ℝ`-linear map between finite-dimensional `ℝ`-vector spaces (using the
elementwise matrix norm and the fact that `Matrix n n ℂ` is a finite-
dimensional `ℝ`-vector space). -/
lemma continuous_RconjHom :
    Continuous (RconjHom : Matrix n n ℂ → Matrix (n × n) (n × n) ℂ) := by
  -- Expose `Rconj` as an `ℝ`-linear map and invoke continuity from finite
  -- dimensionality.
  let Rlin : Matrix n n ℂ →ₗ[ℝ] Matrix (n × n) (n × n) ℂ :=
    { toFun := Rconj
      map_add' := Rconj_add
      map_smul' := fun r B => Rconj_smul_real r B }
  change Continuous (Rlin : Matrix n n ℂ → Matrix (n × n) (n × n) ℂ)
  exact Rlin.continuous_of_finiteDimensional

end LiebSuperop
