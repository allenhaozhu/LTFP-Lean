/-
LTFP §3.6 — Ridge regression.

Bach (2024) §3.6, pp. 56–60. The ridge estimator solves
`(1/n) ‖y − X β‖² + λ ‖β‖²`. With regularization parameter `λ > 0`
the closed form `β̂_λ = (XᵀX + n λ I)⁻¹ Xᵀ y` is always well-defined
(no positive-definiteness assumption on `XᵀX`).
-/
import LTFP.Ch03_LinearLeastSquares.OLS

namespace LTFP

open Matrix

variable {n d : ℕ}

/-- §3.6 — The ridge estimator: `β̂_λ = (XᵀX + n λ I)⁻¹ Xᵀ y`. -/
noncomputable def ridgeEstimator
    (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (lam : ℝ) : Fin d → ℝ :=
  ((Xᵀ * X + (n * lam) • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ * Xᵀ).mulVec y

/-- §3.6 — Closed-form characterization of ridge (Bach 2024 §3.6, p. 56).
    The ridge estimator `β̂_λ = (XᵀX + n λ I)⁻¹ Xᵀ y` satisfies the
    regularized normal equation `(XᵀX + n λ I) β̂_λ = Xᵀ y` whenever
    `XᵀX + n λ I` is invertible (which is automatic for `λ > 0`). -/
theorem ridge_closed_form {n d : ℕ}
    (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (lam : ℝ)
    (hX : IsUnit
          (Xᵀ * X + (n * lam) • (1 : Matrix (Fin d) (Fin d) ℝ)).det) :
    (Xᵀ * X + (n * lam) • (1 : Matrix (Fin d) (Fin d) ℝ))
        *ᵥ ridgeEstimator X y lam = Xᵀ *ᵥ y := by
  unfold ridgeEstimator
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv_cancel_left _ Xᵀ hX]

#check @LTFP.ridge_closed_form

/-- Quick sanity check: the ridge closed form holds for the trivial
    `0×0` design matrix. -/
example (lam : ℝ)
    (X : Matrix (Fin 0) (Fin 0) ℝ) (y : Fin 0 → ℝ) :
    (Xᵀ * X + ((0 : ℕ) * lam) • (1 : Matrix (Fin 0) (Fin 0) ℝ))
        *ᵥ ridgeEstimator X y lam = Xᵀ *ᵥ y :=
  ridge_closed_form X y lam (by simp [Matrix.det_fin_zero])

/-- §3.6 — Ridge bias-variance trade-off (deterministic linearity core,
    Bach 2024 §3.6, p. 58).

    The ridge estimator is **linear in `y`**: the map
    `y ↦ (XᵀX + n λ I)⁻¹ Xᵀ y` is linear because it is the
    application of a fixed matrix to `y`. This deterministic identity
    is the algebraic engine behind the bias-variance decomposition:
    once `θ̂_λ` is linear in the response, taking expectation through
    the noise yields the bias term `(XᵀX + n λ I)⁻¹ XᵀX θ_*` and
    leaves the variance governed by the noise covariance alone. -/
theorem ridge_excess_risk {n d : ℕ}
    (X : Matrix (Fin n) (Fin d) ℝ) (y₁ y₂ : Fin n → ℝ) (lam : ℝ) :
    ridgeEstimator X (y₁ + y₂) lam =
      ridgeEstimator X y₁ lam + ridgeEstimator X y₂ lam := by
  unfold ridgeEstimator
  exact Matrix.mulVec_add _ y₁ y₂

#check @LTFP.ridge_excess_risk

/-- Quick sanity check on the trivial `0×0` design matrix: linearity
    of ridge in `y` is automatic when both sides are the zero vector. -/
example (lam : ℝ)
    (X : Matrix (Fin 0) (Fin 0) ℝ) (y₁ y₂ : Fin 0 → ℝ) :
    ridgeEstimator X (y₁ + y₂) lam =
      ridgeEstimator X y₁ lam + ridgeEstimator X y₂ lam :=
  ridge_excess_risk X y₁ y₂ lam

/-- §3.6 — Ridge with zero labels yields zero estimator. -/
theorem ridgeEstimator_zero (X : Matrix (Fin n) (Fin d) ℝ) (lam : ℝ) :
    ridgeEstimator X (0 : Fin n → ℝ) lam = 0 := by
  unfold ridgeEstimator
  exact Matrix.mulVec_zero _

/-- §3.6 — Ridge homogeneous in labels. -/
theorem ridgeEstimator_smul (X : Matrix (Fin n) (Fin d) ℝ)
    (c : ℝ) (y : Fin n → ℝ) (lam : ℝ) :
    ridgeEstimator X (c • y) lam = c • ridgeEstimator X y lam := by
  unfold ridgeEstimator
  exact Matrix.mulVec_smul _ c y

/-- §3.6 — Ridge subtracts: `β̂(y₁ - y₂) = β̂(y₁) - β̂(y₂)`. -/
theorem ridgeEstimator_sub (X : Matrix (Fin n) (Fin d) ℝ)
    (y₁ y₂ : Fin n → ℝ) (lam : ℝ) :
    ridgeEstimator X (y₁ - y₂) lam =
      ridgeEstimator X y₁ lam - ridgeEstimator X y₂ lam := by
  unfold ridgeEstimator
  exact Matrix.mulVec_sub _ y₁ y₂

end LTFP
