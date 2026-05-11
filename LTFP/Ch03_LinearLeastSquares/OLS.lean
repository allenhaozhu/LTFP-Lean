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

end LTFP

#check @LTFP.ols_closed_form
#check @LTFP.ols_is_projection

