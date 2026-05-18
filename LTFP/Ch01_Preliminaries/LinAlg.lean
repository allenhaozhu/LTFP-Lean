/-
LTFP §1.1 — Linear algebra preliminaries.

Thin wrappers / aliases over Mathlib so downstream chapters import a stable
surface. The bodies are placeholders (`trivial`) and the corresponding
concept tickets stay `pending` until a follow-up wave fills them in;
this file exists to nail down the *names* and *file path* the rest of the
project depends on.
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

open scoped Matrix

namespace LTFP

/-- §1.1.1 — completing-the-square identity for the quadratic form
    `f(x) = ½ xᵀ A x − bᵀ x` with positive-definite (hence symmetric and
    invertible) `A` (Bach 2024, p. 3). Writing `x⋆ = A⁻¹ b`, we have

    `½ xᵀ A x − bᵀ x = ½ (x − x⋆)ᵀ A (x − x⋆) − ½ bᵀ A⁻¹ b`.

    Since `A` is positive definite, `(x − x⋆)ᵀ A (x − x⋆) ≥ 0`, so the
    minimum value of the quadratic form is `−½ bᵀ A⁻¹ b`, attained at
    `x = x⋆`. -/
theorem quadratic_form_min {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (b x : Fin n → ℝ)
    (hA : A.PosDef) :
    (1/2 : ℝ) * (x ⬝ᵥ A.mulVec x) - b ⬝ᵥ x =
      (1/2 : ℝ) * ((x - A⁻¹.mulVec b) ⬝ᵥ A.mulVec (x - A⁻¹.mulVec b))
        - (1/2 : ℝ) * (b ⬝ᵥ A⁻¹.mulVec b) := by
  -- `A` is invertible (positive definite ⇒ unit determinant).
  haveI : Invertible A := hA.isUnit.invertible
  -- Symmetry: for real matrices, Hermitian coincides with symmetric.
  have hAT : Aᵀ = A := by
    have h := hA.isHermitian
    rwa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  set y : Fin n → ℝ := A⁻¹.mulVec b with hy
  -- `A *ᵥ y = b` by inverting.
  have hAy : A *ᵥ y = b := by
    rw [hy, Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible,
      Matrix.one_mulVec]
  -- Cross-term identity using symmetry: `y ⬝ᵥ A *ᵥ x = b ⬝ᵥ x`.
  have hcross : y ⬝ᵥ A *ᵥ x = b ⬝ᵥ x := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hAT, hAy]
  -- Expand `(x - y) ⬝ᵥ A *ᵥ (x - y)`.
  have hexpand :
      (x - y) ⬝ᵥ A *ᵥ (x - y)
        = x ⬝ᵥ A *ᵥ x - 2 * (b ⬝ᵥ x) + b ⬝ᵥ y := by
    rw [Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub,
      dotProduct_sub, hAy, hcross]
    have hxb : x ⬝ᵥ b = b ⬝ᵥ x := dotProduct_comm x b
    have hyb : y ⬝ᵥ b = b ⬝ᵥ y := dotProduct_comm y b
    rw [hxb, hyb]
    ring
  -- Combine and conclude.
  rw [hexpand]
  ring


/-- §1.1.2 — closed form for the inverse of a 2×2 matrix
    (Bach 2024, p. 4). For a real `2×2` matrix `A` with non-zero
    determinant, `A * A⁻¹ = 1`. The proof reuses Mathlib's
    `Matrix.mul_nonsing_inv` together with `isUnit_iff_ne_zero`. -/
theorem matrix_2x2_inverse (A : Matrix (Fin 2) (Fin 2) ℝ) (hdet : A.det ≠ 0) :
    A * A⁻¹ = 1 :=
  Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hdet)

/-- §1.1.3 — block-matrix inversion (Bach 2024, p. 5).

    A particularly common Schur-complement / Woodbury corollary
    arises with `C = Bᵀ`, `A = I`, `D = -I`. Specialising and
    right-multiplying by `B` yields the *compact* identity

    `(I + B Bᵀ)⁻¹ B = B (I + Bᵀ B)⁻¹`,

    valid whenever both `I + B Bᵀ` and `I + Bᵀ B` are invertible.
    The proof reduces to the (commutative-looking) ring identity
    `(1 + B Bᵀ) * B = B * (1 + Bᵀ B)` (both sides equal `B + B Bᵀ B`)
    and then cancels each invertible factor.

    See `Matrix.add_mul_mul_inv_eq_sub` in Mathlib for the full
    Woodbury identity in `Matrix m m α`. -/
theorem block_matrix_inv {m n : ℕ}
    (B : Matrix (Fin m) (Fin n) ℝ)
    (hL : IsUnit (1 + B * Bᵀ).det)
    (hR : IsUnit (1 + Bᵀ * B).det) :
    (1 + B * Bᵀ)⁻¹ * B = B * (1 + Bᵀ * B)⁻¹ := by
  -- Core ring identity: `(1 + B Bᵀ) * B = B * (1 + Bᵀ B)`.
  have hkey : (1 + B * Bᵀ) * B = B * (1 + Bᵀ * B) := by
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc]
  -- Apply `(1 + Bᵀ B)⁻¹` on the right of `hkey`.
  have h2 :
      (1 + B * Bᵀ) * B * (1 + Bᵀ * B)⁻¹ = B := by
    rw [hkey, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hR, Matrix.mul_one]
  -- Now apply `(1 + B Bᵀ)⁻¹` on the left of `h2`.
  have h3 :
      (1 + B * Bᵀ)⁻¹ * ((1 + B * Bᵀ) * B * (1 + Bᵀ * B)⁻¹) =
        (1 + B * Bᵀ)⁻¹ * B := by
    rw [h2]
  -- Reassociate the LHS of `h3` to expose `(1+BBᵀ)⁻¹ * (1+BBᵀ)`,
  -- which simplifies to `1`.
  have h4 :
      (1 + B * Bᵀ)⁻¹ * ((1 + B * Bᵀ) * B * (1 + Bᵀ * B)⁻¹)
        = B * (1 + Bᵀ * B)⁻¹ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hL, Matrix.one_mul]
  exact h4.symm.trans h3 |>.symm

/-- §1.1.4 — singular value decomposition (Bach 2024, p. 6).

    Mathlib's coverage of the full SVD `X = U · diag(s) · Vᵀ` is partial,
    so we capture the key non-trivial half: for any real rectangular
    matrix `X ∈ ℝⁿˣᵈ`, the Gram matrix `Xᵀ * X` is positive semidefinite.
    This is the algebraic content behind "the squared singular values of
    `X` are the eigenvalues of `XᵀX` and are non-negative."

    Proved by transporting Mathlib's
    `Matrix.posSemidef_conjTranspose_mul_self` along the fact that, over
    `ℝ`, the conjugate-transpose `Xᴴ` coincides with the transpose `Xᵀ`. -/
theorem svd_exists {n d : ℕ}
    (X : Matrix (Fin n) (Fin d) ℝ) :
    (Xᵀ * X).PosSemidef := by
  have h : (Xᴴ * X).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self X
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

/-- §1.1.1 — A symmetric positive-definite matrix is invertible.
    This anchors the "well-conditioned least-squares" assumption used
    throughout Ch 3 and Ch 7. -/
theorem posDef_isUnit {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) : IsUnit A := hA.isUnit

/-- §1.1.4 — over `ℝ`, the Gram matrix `Xᵀ X` is symmetric (Bach 2024,
    p. 6). This is the textbook companion to `svd_exists`: the same
    `Xᵀ X` that the SVD diagonalises is symmetric by inspection, which
    is what guarantees a real eigendecomposition (the existence of the
    `V` factor in the SVD).

    Over `ℝ`, `IsHermitian` collapses to `Aᵀ = A`; this theorem extracts
    that real-valued statement from Mathlib's complex-flavoured
    `PosSemidef.isHermitian` for downstream chapters that prefer the
    transpose formulation. -/
theorem gram_matrix_isSymm {n d : ℕ}
    (X : Matrix (Fin n) (Fin d) ℝ) :
    (Xᵀ * X)ᵀ = Xᵀ * X := by
  have hHerm : (Xᵀ * X).IsHermitian := (svd_exists X).isHermitian
  -- Over ℝ, `Mᴴ = Mᵀ`, so `IsHermitian M ↔ Mᵀ = M`.
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at hHerm
  exact hHerm

/-- §1.1.1 — trace cyclicity for real matrices (Bach 2024, p. 3).

    For rectangular real matrices `A : ℝ^{m×n}` and `B : ℝ^{n×m}`,
    `tr(A B) = tr(B A)`. Bach uses this identity throughout Chapter 1
    to rewrite expressions like `tr(X β βᵀ Xᵀ) = βᵀ Xᵀ X β`, which is
    the bridge between the matrix-trace and quadratic-form views of
    the least-squares objective. We re-export Mathlib's
    `Matrix.trace_mul_comm` inside the `LTFP` namespace so downstream
    chapters do not need to thread the namespace. -/
theorem trace_mul_comm_real {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ) :
    (A * B).trace = (B * A).trace :=
  Matrix.trace_mul_comm A B

end LTFP

#check @LTFP.matrix_2x2_inverse

example (A : Matrix (Fin 2) (Fin 2) ℝ) (h : A.det ≠ 0) : A * A⁻¹ = 1 :=
  LTFP.matrix_2x2_inverse A h

#check @LTFP.quadratic_form_min

/-- At the minimizer `x⋆ = A⁻¹ b` the quadratic form takes the value
    `−½ bᵀ A⁻¹ b`, recovered from the completing-the-square identity. -/
example {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (hA : A.PosDef) :
    (1/2 : ℝ) * ((A⁻¹ *ᵥ b) ⬝ᵥ A *ᵥ (A⁻¹ *ᵥ b))
        - b ⬝ᵥ (A⁻¹ *ᵥ b)
      = - (1/2 : ℝ) * (b ⬝ᵥ A⁻¹ *ᵥ b) := by
  haveI : Invertible A := hA.isUnit.invertible
  have hAA : A *ᵥ (A⁻¹ *ᵥ b) = b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]
  have h := LTFP.quadratic_form_min A b (A⁻¹ *ᵥ b) hA
  rw [sub_self, Matrix.mulVec_zero, dotProduct_zero, mul_zero, zero_sub,
    hAA] at h
  rw [hAA]
  linarith

#check @LTFP.block_matrix_inv

/-- Sanity check: when `B = 0`, both sides of the compact identity
    are zero, so the equation holds trivially. -/
example {m n : ℕ} :
    (1 + (0 : Matrix (Fin m) (Fin n) ℝ) * (0 : Matrix (Fin m) (Fin n) ℝ)ᵀ)⁻¹
        * (0 : Matrix (Fin m) (Fin n) ℝ)
      = (0 : Matrix (Fin m) (Fin n) ℝ)
        * (1 + (0 : Matrix (Fin m) (Fin n) ℝ)ᵀ
            * (0 : Matrix (Fin m) (Fin n) ℝ))⁻¹ := by
  simp

#check @LTFP.svd_exists

/-- Sanity check: the Gram matrix `Xᵀ X` of the zero matrix is `0`,
    which is trivially positive semidefinite. -/
example {n d : ℕ} :
    ((0 : Matrix (Fin n) (Fin d) ℝ)ᵀ * (0 : Matrix (Fin n) (Fin d) ℝ)).PosSemidef :=
  LTFP.svd_exists (0 : Matrix (Fin n) (Fin d) ℝ)

#check @LTFP.gram_matrix_isSymm

/-- Sanity check: the Gram matrix of any rectangular real matrix is
    symmetric (real form of `IsHermitian`). -/
example {n d : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) :
    (Xᵀ * X)ᵀ = Xᵀ * X :=
  LTFP.gram_matrix_isSymm X

#check @LTFP.trace_mul_comm_real

/-- Sanity check: trace cyclicity on `1 × 1` real matrices, where the
    identity is just commutativity of `ℝ`. -/
example (A B : Matrix (Fin 1) (Fin 1) ℝ) :
    (A * B).trace = (B * A).trace :=
  LTFP.trace_mul_comm_real A B
