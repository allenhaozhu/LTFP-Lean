/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.Order
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

open scoped Kronecker ComplexOrder

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

end LiebSuperop
