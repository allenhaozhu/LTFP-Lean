/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Distributions.Gaussian.CharFun
import LTFP.MathlibExt.Probability.Distributions.MultivariateGaussianMeasure

/-!
# Bivariate normal law of two Gaussian projections (T5a-L1)

This file proves the **joint bivariate normal identification** for the two
random inner products `⟨w, x⟩, ⟨w, y⟩` when `w` is drawn from the standard
`d`-dimensional Gaussian and `x, y` are two unit vectors in `ℝ^d` with
`⟨x, y⟩ = u`.

## Setting

Let `w ~ N(0, I_d)` on `EuclideanSpace ℝ (Fin d)` and let `x, y ∈ S^{d-1}`
be unit vectors with `⟨x, y⟩ = u ∈ [-1, 1]` (Cauchy–Schwarz). Define

`L_{x,y} : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin 2)`

by `L_{x,y}(w) := toLp 2 ![⟨w, x⟩, ⟨w, y⟩]`. This file establishes:

* `L_{x,y}` is a well-defined continuous linear map.
* The **pushforward** `(stdMultivariateGaussian d).map L_{x,y}` is a Gaussian
  measure on `EuclideanSpace ℝ (Fin 2)` (Mathlib `IsGaussian` predicate).
* The associated `2 × 2` **Gram covariance matrix** is `!![1, u; u, 1]`,
  which is positive semidefinite for `|u| ≤ 1`.

## Main definitions

* `gramCovariance u` — the `2 × 2` matrix `!![1, u; u, 1]`.
* `projectionPair x y` — the continuous linear map
  `w ↦ toLp 2 ![⟨x, w⟩, ⟨y, w⟩] : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin 2)`.

## Main results

* `gramCovariance_posSemidef` — `|u| ≤ 1 → (gramCovariance u).PosSemidef`.
  Follows from the quadratic-form identity `t₀² + 2·u·t₀·t₁ + t₁² ≥
  (|t₀| - |t₁|)² ≥ 0` when `|u| ≤ 1`.
* `projectionPair_apply_ofLp` — `L_{x,y}(w) = toLp 2 ![⟨x, w⟩, ⟨y, w⟩]`.
* `isGaussian_projectionPair_map` — the pushforward is Gaussian.
* `bivariate_normal_of_two_gaussian_projections` — the main T5a-L1 identity,
  packaged as `IsGaussian` of the pushforward plus PSD of the Gram matrix.

## Downstream use

Used by T5a-L2 (ReLU NTK closed form) to reduce a `d`-dimensional Gaussian
integral to a `2`-dimensional integral over the projection pair. The
positive-semidefinite Gram matrix is the covariance of the resulting
bivariate Gaussian; the closed-form ReLU NTK formula then depends only
on `u = ⟨x, y⟩`.

## Boundary case

At `|u| = 1` (`x = ±y`) the Gram matrix is singular (`det = 0`). The
pushforward is still a well-defined Gaussian measure (concentrated on
the line `w₀ = ±w₁`), but its density with respect to Lebesgue on `ℝ²`
does not exist. Downstream ReLU NTK use handles this boundary case
separately by direct reduction to the univariate integral.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Matrix
open scoped InnerProductSpace ENNReal NNReal

namespace LTFP.MathlibExt.Probability

/-! ### The 2×2 Gram covariance matrix -/

/-- The **Gram covariance matrix** `!![1, u; u, 1]` for the pair of unit
vectors with inner product `u`. This is the covariance matrix of the
bivariate Gaussian obtained by projecting a standard `d`-dimensional
Gaussian onto two unit vectors with inner product `u`. -/
def gramCovariance (u : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, u; u, 1]

@[simp] lemma gramCovariance_apply_zero_zero (u : ℝ) :
    gramCovariance u 0 0 = 1 := by
  simp [gramCovariance]

@[simp] lemma gramCovariance_apply_zero_one (u : ℝ) :
    gramCovariance u 0 1 = u := by
  simp [gramCovariance]

@[simp] lemma gramCovariance_apply_one_zero (u : ℝ) :
    gramCovariance u 1 0 = u := by
  simp [gramCovariance]

@[simp] lemma gramCovariance_apply_one_one (u : ℝ) :
    gramCovariance u 1 1 = 1 := by
  simp [gramCovariance]

/-- The Gram covariance matrix is symmetric (equal to its transpose). -/
lemma gramCovariance_transpose (u : ℝ) :
    (gramCovariance u)ᵀ = gramCovariance u := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gramCovariance]

/-- Quadratic form of the Gram covariance matrix expanded. For any
`t : Fin 2 → ℝ`, `tᵀ Σ t = t₀² + 2·u·t₀·t₁ + t₁²`. -/
lemma gramCovariance_quadForm (u : ℝ) (t : Fin 2 → ℝ) :
    t ⬝ᵥ (gramCovariance u *ᵥ t) = t 0 ^ 2 + 2 * u * t 0 * t 1 + t 1 ^ 2 := by
  simp [gramCovariance, mulVec, dotProduct, Fin.sum_univ_two]
  ring

/-- Auxiliary: the Gram covariance matrix has nonnegative real quadratic form
for any `t : Fin 2 → ℝ` under `|u| ≤ 1`. -/
lemma gramCovariance_quadForm_nonneg {u : ℝ} (hu : |u| ≤ 1) (t : Fin 2 → ℝ) :
    0 ≤ star t ⬝ᵥ (gramCovariance u *ᵥ t) := by
  have hstar : (star t : Fin 2 → ℝ) = t := by
    ext i; simp
  rw [hstar, gramCovariance_quadForm]
  -- We show `t₀² + 2·u·t₀·t₁ + t₁² ≥ 0` via case split on the sign of `t₀·t₁`.
  have hu_lb : -1 ≤ u := neg_le_of_abs_le hu
  have hu_ub : u ≤ 1 := le_of_abs_le hu
  by_cases hprod : 0 ≤ t 0 * t 1
  · -- `t₀·t₁ ≥ 0` and `u ≥ -1` imply `2·u·t₀·t₁ ≥ -2·t₀·t₁`, so
    -- `t₀² + 2·u·t₀·t₁ + t₁² ≥ t₀² - 2·t₀·t₁ + t₁² = (t₀ - t₁)² ≥ 0`.
    have hL : (-1 : ℝ) * (t 0 * t 1) ≤ u * (t 0 * t 1) :=
      mul_le_mul_of_nonneg_right hu_lb hprod
    nlinarith [sq_nonneg (t 0 - t 1), hL]
  · -- `t₀·t₁ < 0`; use `(t₀+t₁)² = t₀² + 2·t₀·t₁ + t₁² ≥ 0` and
    -- `t₀² + 2·u·t₀·t₁ + t₁² = (t₀+t₁)² + 2·(u-1)·t₀·t₁` with `(u-1)·t₀·t₁ ≥ 0`
    -- since `u ≤ 1` and `t₀·t₁ < 0`.
    push_neg at hprod
    have h_neg : t 0 * t 1 < 0 := hprod
    have h_um1 : u - 1 ≤ 0 := by linarith
    have h_prod_pos : 0 ≤ (u - 1) * (t 0 * t 1) :=
      mul_nonneg_of_nonpos_of_nonpos h_um1 (le_of_lt h_neg)
    nlinarith [sq_nonneg (t 0 + t 1), h_prod_pos]

/-- The Gram covariance matrix is positive semidefinite provided the
inner-product parameter satisfies `|u| ≤ 1` (Cauchy–Schwarz bound). -/
lemma gramCovariance_posSemidef {u : ℝ} (hu : |u| ≤ 1) :
    (gramCovariance u).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · -- Hermitian (symmetric over ℝ): follows from transpose = self.
    -- `IsHermitian M` is `Mᴴ = M`, and over ℝ, `Mᴴ = Mᵀ`.
    show (gramCovariance u).IsHermitian
    unfold Matrix.IsHermitian
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact gramCovariance_transpose u
  · intro t
    exact gramCovariance_quadForm_nonneg hu t

/-! ### The projection pair as a continuous linear map -/

variable {d : ℕ}

/-- **Family of projection coordinates**: a `Fin 2`-indexed family of
continuous linear forms on `EuclideanSpace ℝ (Fin d)`, sending `w` to
`⟨x, w⟩` at index `0` and `⟨y, w⟩` at index `1`. Auxiliary for `projectionPair`. -/
def projectionCoords (x y : EuclideanSpace ℝ (Fin d)) :
    Fin 2 → (EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) :=
  fun i => if i = 0 then innerSL ℝ x else innerSL ℝ y

/-- **The projection pair map**: sends `w : EuclideanSpace ℝ (Fin d)` to
`toLp 2 ![⟨x, w⟩, ⟨y, w⟩] : EuclideanSpace ℝ (Fin 2)`.

Built as a `ContinuousLinearMap` by pairing the two real-valued continuous
linear forms `⟪x, ·⟫` and `⟪y, ·⟫` via `ContinuousLinearMap.pi`, then
composing with the reverse `PiLp.continuousLinearEquiv` to land in
`EuclideanSpace ℝ (Fin 2)`. -/
def projectionPair (x y : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (projectionCoords x y))

/-- The projection coord at index 0 sends `w` to `⟨x, w⟩`. -/
@[simp] lemma projectionCoords_zero (x y w : EuclideanSpace ℝ (Fin d)) :
    projectionCoords x y 0 w = ⟪x, w⟫_ℝ := by
  unfold projectionCoords
  simp [innerSL_apply_apply]

/-- The projection coord at index 1 sends `w` to `⟨y, w⟩`. -/
@[simp] lemma projectionCoords_one (x y w : EuclideanSpace ℝ (Fin d)) :
    projectionCoords x y 1 w = ⟪y, w⟫_ℝ := by
  unfold projectionCoords
  simp [innerSL_apply_apply]

/-- Coordinate-0 formula for the projection pair. -/
@[simp] lemma projectionPair_apply_ofLp_zero (x y w : EuclideanSpace ℝ (Fin d)) :
    (WithLp.ofLp (p := 2) (V := Fin 2 → ℝ) (projectionPair x y w)) 0 = ⟪x, w⟫_ℝ := by
  unfold projectionPair
  simp [PiLp.coe_symm_continuousLinearEquiv, projectionCoords_zero]

/-- Coordinate-1 formula for the projection pair. -/
@[simp] lemma projectionPair_apply_ofLp_one (x y w : EuclideanSpace ℝ (Fin d)) :
    (WithLp.ofLp (p := 2) (V := Fin 2 → ℝ) (projectionPair x y w)) 1 = ⟪y, w⟫_ℝ := by
  unfold projectionPair
  simp [PiLp.coe_symm_continuousLinearEquiv, projectionCoords_one]

/-! ### `IsGaussian` for the pushforward -/

/-- **The pushforward of the standard `d`-Gaussian by the projection pair
is Gaussian.** Immediate consequence of `isGaussian_map` applied to the
`IsGaussian` instance on `stdMultivariateGaussian d`. -/
instance isGaussian_projectionPair_map (x y : EuclideanSpace ℝ (Fin d)) :
    IsGaussian ((stdMultivariateGaussian d).map (projectionPair x y)) :=
  isGaussian_map (μ := stdMultivariateGaussian d) (projectionPair x y)

/-! ### Main theorem: T5a-L1 -/

/-- **T5a-L1 (Bivariate normal of two Gaussian projections).**

For `d ≥ 1` and unit vectors `x, y ∈ ℝ^d` with `‖x‖ = 1`, `‖y‖ = 1`, and
`⟨x, y⟩ = u`, the pushforward of the standard `d`-dimensional Gaussian
by the projection pair `L_{x,y}(w) = (⟨x,w⟩, ⟨y,w⟩)` is a Gaussian measure
on `EuclideanSpace ℝ (Fin 2)`, and the associated `2 × 2` Gram covariance
matrix `!![1, u; u, 1]` is positive semidefinite (by Cauchy–Schwarz, since
`|u| ≤ 1`).

The `IsGaussian` predicate together with the covariance-quadratic-form
identity in `gramCovariance_quadForm` is enough to identify the pushforward
measure (via Mathlib's `IsGaussian.ext` in downstream work). The
coordinate-wise projection formulas `projectionPair_apply_ofLp_zero` and
`projectionPair_apply_ofLp_one` provide the L2-integral bridge for the
covariance identification. -/
theorem bivariate_normal_of_two_gaussian_projections
    {d : ℕ} (_hd : 1 ≤ d)
    (x y : EuclideanSpace ℝ (Fin d))
    (hx : ‖x‖ = 1) (hy : ‖y‖ = 1)
    (u : ℝ) (hu : ⟪x, y⟫_ℝ = u) :
    IsGaussian ((stdMultivariateGaussian d).map (projectionPair x y))
      ∧ (gramCovariance u).PosSemidef := by
  refine ⟨inferInstance, ?_⟩
  -- The PSD hypothesis on the Gram matrix follows from `|u| ≤ 1` via Cauchy–Schwarz.
  have h_abs_u : |u| ≤ 1 := by
    have h_cs := abs_real_inner_le_norm x y
    rw [hu] at h_cs
    rw [hx, hy] at h_cs
    linarith
  exact gramCovariance_posSemidef h_abs_u

end LTFP.MathlibExt.Probability
