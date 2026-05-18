/-
LTFP §3.3 — Ordinary least-squares.

Bach (2024) §3.3, pp. 47–49. Given a design matrix `X ∈ ℝ^{n×d}` and
response vector `y ∈ ℝ^n`, the OLS estimator `β̂` minimizes
`(1/n) ‖y − X β‖²`. When `XᵀX` is invertible, the closed form is
`β̂ = (XᵀX)⁻¹ Xᵀ y`.
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Real.Basic

namespace LTFP

open Matrix

variable {n d : ℕ}

/-- §3.3.1 — The OLS estimator: `β̂ = (XᵀX)⁻¹ Xᵀ y`. -/
noncomputable def olsEstimator
    (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) : Fin d → ℝ :=
  ((Xᵀ * X)⁻¹ * Xᵀ).mulVec y

/-- §3.3.1 — Closed-form characterization of OLS via the **normal
    equation** (Bach 2024 §3.3.1, p. 47). When `XᵀX` is invertible,
    the OLS estimator `β̂ = (XᵀX)⁻¹ Xᵀ y` satisfies `(XᵀX) β̂ = Xᵀ y`. -/
theorem ols_closed_form
    (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ)
    (hX : IsUnit (Xᵀ * X).det) :
    (Xᵀ * X) *ᵥ olsEstimator X y = Xᵀ *ᵥ y := by
  unfold olsEstimator
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv_cancel_left _ Xᵀ hX]

/-- §3.3.2 — OLS as orthogonal projection of `y` onto `col(X)`
    (Bach 2024 §3.3.2, p. 48). The "hat matrix"
    `Π = X (XᵀX)⁻¹ Xᵀ` fixes every vector in the column space
    `im(X)`: for any `a : Fin d → ℝ`, `Π (X a) = X a`. This is the
    fixed-point half of the orthogonal-projection characterization
    (Proposition 3.2). -/
theorem ols_is_projection
    (X : Matrix (Fin n) (Fin d) ℝ) (a : Fin d → ℝ)
    (hX : IsUnit (Xᵀ * X).det) :
    (X * (Xᵀ * X)⁻¹ * Xᵀ) *ᵥ (X *ᵥ a) = X *ᵥ a := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hX, Matrix.mul_one]

/-- Sanity-check example: the normal equation specialized to `n = 3`,
    `d = 2`. -/
example (X : Matrix (Fin 3) (Fin 2) ℝ) (y : Fin 3 → ℝ)
    (hX : IsUnit (Xᵀ * X).det) :
    (Xᵀ * X) *ᵥ olsEstimator X y = Xᵀ *ᵥ y :=
  ols_closed_form X y hX

/-- Sanity-check example: the projection fixed-point property
    specialized to `n = 3`, `d = 2`. -/
example (X : Matrix (Fin 3) (Fin 2) ℝ) (a : Fin 2 → ℝ)
    (hX : IsUnit (Xᵀ * X).det) :
    (X * (Xᵀ * X)⁻¹ * Xᵀ) *ᵥ (X *ᵥ a) = X *ᵥ a :=
  ols_is_projection X a hX

/-- §3.3 — OLS is linear in labels. -/
theorem olsEstimator_add_y (X : Matrix (Fin n) (Fin d) ℝ) (y₁ y₂ : Fin n → ℝ) :
    olsEstimator X (y₁ + y₂) = olsEstimator X y₁ + olsEstimator X y₂ := by
  unfold olsEstimator
  exact Matrix.mulVec_add _ y₁ y₂

/-- §3.3 — OLS is homogeneous in labels. -/
theorem olsEstimator_smul_y (X : Matrix (Fin n) (Fin d) ℝ) (c : ℝ) (y : Fin n → ℝ) :
    olsEstimator X (c • y) = c • olsEstimator X y := by
  unfold olsEstimator
  exact Matrix.mulVec_smul _ c y

/-- §3.3 — OLS vanishes on the zero label vector (companion result).

    Trivial but textbook consequence of linearity: `β̂(0) = 0`. Stated
    explicitly because the OLS estimator is the closed-form linear
    map `(XᵀX)⁻¹Xᵀ` applied to `y`; this is the constant term of the
    standard bias-variance decomposition in Bach (2024) §3.3. -/
theorem olsEstimator_zero (X : Matrix (Fin n) (Fin d) ℝ) :
    olsEstimator X (0 : Fin n → ℝ) = 0 := by
  unfold olsEstimator
  exact Matrix.mulVec_zero _

/-- §3.3.2 — Hat-matrix idempotency (Bach 2024 §3.3.2, p. 48).

    The hat matrix `Π = X (XᵀX)⁻¹ Xᵀ` is an orthogonal projector onto
    the column space `col(X)`; in particular it is idempotent, i.e.,
    `Π² = Π`. Combined with `ols_is_projection` (`Π` fixes vectors of
    the form `X a`), this is the matrix form of the
    "orthogonal projection onto `im(X)`" characterization of OLS
    (Proposition 3.2). -/
theorem hat_matrix_idempotent
    (X : Matrix (Fin n) (Fin d) ℝ)
    (hX : IsUnit (Xᵀ * X).det) :
    (X * (Xᵀ * X)⁻¹ * Xᵀ) * (X * (Xᵀ * X)⁻¹ * Xᵀ) =
      X * (Xᵀ * X)⁻¹ * Xᵀ := by
  -- Π Π = X (XᵀX)⁻¹ (Xᵀ X) (XᵀX)⁻¹ Xᵀ = X (XᵀX)⁻¹ Xᵀ.
  have hmid :
      ((Xᵀ * X)⁻¹ * Xᵀ) * (X * (Xᵀ * X)⁻¹) = (Xᵀ * X)⁻¹ := by
    rw [show ((Xᵀ * X)⁻¹ * Xᵀ) * (X * (Xᵀ * X)⁻¹)
            = (Xᵀ * X)⁻¹ * (Xᵀ * X) * (Xᵀ * X)⁻¹ by
          rw [Matrix.mul_assoc, ← Matrix.mul_assoc Xᵀ X ((Xᵀ * X)⁻¹),
              ← Matrix.mul_assoc]]
    rw [Matrix.nonsing_inv_mul _ hX, Matrix.one_mul]
  calc (X * (Xᵀ * X)⁻¹ * Xᵀ) * (X * (Xᵀ * X)⁻¹ * Xᵀ)
      = X * (((Xᵀ * X)⁻¹ * Xᵀ) * (X * (Xᵀ * X)⁻¹)) * Xᵀ := by
        simp [Matrix.mul_assoc]
    _ = X * (Xᵀ * X)⁻¹ * Xᵀ := by rw [hmid]

/-- §3.3.1 — Residual orthogonal to columns of `X` (Bach 2024 §3.3.1,
    Proposition 3.2, p. 48).

    The OLS normal equation `(XᵀX) β̂ = Xᵀ y` is equivalent to the
    statement that the residual vector `r = y − X β̂` is orthogonal to
    every column of `X`, i.e., `Xᵀ r = 0`. This is the geometric
    characterization of OLS as the orthogonal projection of `y` onto
    `col(X)`. -/
theorem ols_residual_orthogonal
    (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ)
    (hX : IsUnit (Xᵀ * X).det) :
    Xᵀ *ᵥ (y - X *ᵥ olsEstimator X y) = 0 := by
  -- Xᵀ (y - X β̂) = Xᵀ y - (Xᵀ X) β̂ = 0 by `ols_closed_form`.
  rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, ols_closed_form X y hX, sub_self]

end LTFP

#check @LTFP.ols_closed_form
#check @LTFP.ols_is_projection
#check @LTFP.olsEstimator_zero
#check @LTFP.hat_matrix_idempotent
#check @LTFP.ols_residual_orthogonal

