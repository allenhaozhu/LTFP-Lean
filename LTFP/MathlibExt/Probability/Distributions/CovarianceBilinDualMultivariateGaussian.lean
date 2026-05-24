/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.Distributions.MultivariateGaussianMeasure
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Moments.CovarianceBilinDual

/-!
# `covarianceBilinDual` of the multivariate Gaussian as a matrix bilinear form

For the multivariate Gaussian `multivariateGaussian 0 S hS` on
`EuclideanSpace ℝ (Fin n)`, the continuous bilinear form
`covarianceBilinDual` evaluated on two continuous linear functionals
`L₁ L₂ : StrongDual ℝ (EuclideanSpace ℝ (Fin n))` equals the
coordinate-matrix sum

```
∑ i, ∑ j, v₁ i * v₂ j * S i j
```

where `v₁ := (InnerProductSpace.toDual _ _).symm L₁` is the Riesz
representative of `L₁` (and likewise for `v₂`). This is the Riesz bridge
between the abstract dual covariance form and the concrete matrix
characterization; downstream sub-step toward Sub-I4.D.
-/

open MeasureTheory ProbabilityTheory
open scoped Matrix RealInnerProductSpace InnerProductSpace

namespace ProbabilityTheory

/-- **`covarianceBilinDual` of the multivariate Gaussian, as a matrix bilinear form.**

Let `S : Matrix (Fin n) (Fin n) ℝ` be positive semidefinite and write
`μ := multivariateGaussian 0 S hS`. For two continuous linear functionals
`L₁ L₂ : StrongDual ℝ (EuclideanSpace ℝ (Fin n))` with Riesz representatives
`v₁, v₂ := (InnerProductSpace.toDual ℝ _).symm L_k`, the dual covariance
bilinear form evaluates to

  `covarianceBilinDual μ L₁ L₂ = ∑ i, ∑ j, v₁ i * v₂ j * S i j`.

This is the Riesz bridge from the abstract dual covariance to the concrete
coordinate-matrix sum. -/
theorem covarianceBilinDual_multivariateGaussian
    {n : ℕ}
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef)
    (L₁ L₂ : StrongDual ℝ (EuclideanSpace ℝ (Fin n))) :
    let v₁ := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm L₁
    let v₂ := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm L₂
    covarianceBilinDual
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S hS) L₁ L₂ =
      ∑ i, ∑ j, v₁ i * v₂ j * S i j := by
  classical
  -- Abbreviations.
  set μ : Measure (EuclideanSpace ℝ (Fin n)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S hS with hμ
  set v₁ : EuclideanSpace ℝ (Fin n) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm L₁ with hv₁
  set v₂ : EuclideanSpace ℝ (Fin n) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm L₂ with hv₂
  -- The measure is Gaussian, hence `MemLp id 2 μ`.
  have hMuGauss : IsGaussian μ := by
    show IsGaussian (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S hS)
    infer_instance
  have hId : MemLp (id : EuclideanSpace ℝ (Fin n) → _) 2 μ :=
    ProbabilityTheory.IsGaussian.memLp_two_id (μ := μ)
  have hCoord : ∀ a : Fin n, MemLp
      (fun θ : EuclideanSpace ℝ (Fin n) =>
        (WithLp.ofLp (p := 2) (V := Fin n → ℝ) θ) a) 2 μ := by
    intro a
    exact MemLp.eval_piLp hId a
  -- Pointwise expansion: each functional becomes a coordinate sum via Riesz.
  have hExpand : ∀ (L : StrongDual ℝ (EuclideanSpace ℝ (Fin n)))
      (v : EuclideanSpace ℝ (Fin n))
      (hv : v = (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm L)
      (x : EuclideanSpace ℝ (Fin n)),
        L x = ∑ i, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) v) i *
                    (WithLp.ofLp (p := 2) (V := Fin n → ℝ) x) i := by
    intro L v hv x
    -- `L x = ⟪v, x⟫` by Riesz.
    have hRiesz : L x = ⟪v, x⟫_ℝ := by
      have hkey : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) v x = ⟪v, x⟫_ℝ :=
        InnerProductSpace.toDual_apply_apply
      have hLv : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))) v = L := by
        rw [hv]; exact LinearIsometryEquiv.apply_symm_apply _ _
      rw [← hkey, hLv]
    -- `⟪v, x⟫ = ∑ i, v i * x i` on Euclidean space (real inner product).
    have hInner : (⟪v, x⟫_ℝ : ℝ) =
        ∑ i, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) v) i *
              (WithLp.ofLp (p := 2) (V := Fin n → ℝ) x) i := by
      rw [PiLp.inner_apply]
      refine Finset.sum_congr rfl ?_
      intro i _
      -- For real scalars, `⟪a, b⟫_ℝ = a * b`.
      show (⟪v i, x i⟫_ℝ : ℝ) = _
      simp [RCLike.inner_apply, mul_comm]
    rw [hRiesz, hInner]
  -- We may rewrite both functionals into coordinate sums under the integral.
  -- First reduce the dual bilinear form to a scalar covariance.
  rw [covarianceBilinDual_eq_covariance hId L₁ L₂]
  -- Recast the covariance into the coordinate-sum form using `hExpand`.
  -- `cov[L₁, L₂; μ] = cov[fun ω ↦ ∑ i, v₁ i * (ofLp ω) i,
  --                       fun ω ↦ ∑ j, v₂ j * (ofLp ω) j; μ]`.
  have hL₁ : ∀ x : EuclideanSpace ℝ (Fin n),
      L₁ x = ∑ i, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) v₁) i *
                  (WithLp.ofLp (p := 2) (V := Fin n → ℝ) x) i :=
    hExpand L₁ v₁ hv₁
  have hL₂ : ∀ x : EuclideanSpace ℝ (Fin n),
      L₂ x = ∑ j, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) v₂) j *
                  (WithLp.ofLp (p := 2) (V := Fin n → ℝ) x) j :=
    hExpand L₂ v₂ hv₂
  have hCovRewrite :
      cov[(L₁ : EuclideanSpace ℝ (Fin n) → ℝ), (L₂ : EuclideanSpace ℝ (Fin n) → ℝ); μ]
        = cov[fun ω ↦ ∑ i, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) v₁) i *
                            (WithLp.ofLp (p := 2) (V := Fin n → ℝ) ω) i,
              fun ω ↦ ∑ j, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) v₂) j *
                            (WithLp.ofLp (p := 2) (V := Fin n → ℝ) ω) j; μ] := by
    congr 1
    · funext ω; exact hL₁ ω
    · funext ω; exact hL₂ ω
  rw [hCovRewrite]
  -- Apply `covariance_fun_sum_fun_sum`: pointwise summands are `MemLp 2`
  -- because each is a constant times an `ofLp` coordinate.
  have hScaled : ∀ k : Fin n, ∀ (c : ℝ),
      MemLp (fun ω : EuclideanSpace ℝ (Fin n) =>
        c * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) ω) k) 2 μ := by
    intro k c
    exact (hCoord k).const_mul c
  rw [covariance_fun_sum_fun_sum
        (fun i => hScaled i _) (fun j => hScaled j _)]
  -- Pull constants out of each inner covariance.
  -- `cov[c * X, d * Y; μ] = c * (d * cov[X, Y; μ])`.
  have hPull : ∀ i j : Fin n,
      cov[fun ω : EuclideanSpace ℝ (Fin n) =>
            (WithLp.ofLp (p := 2) (V := Fin n → ℝ) v₁) i *
              (WithLp.ofLp (p := 2) (V := Fin n → ℝ) ω) i,
          fun ω : EuclideanSpace ℝ (Fin n) =>
            (WithLp.ofLp (p := 2) (V := Fin n → ℝ) v₂) j *
              (WithLp.ofLp (p := 2) (V := Fin n → ℝ) ω) j; μ]
        = (WithLp.ofLp (p := 2) (V := Fin n → ℝ) v₁) i
            * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) v₂) j
            * cov[fun ω : EuclideanSpace ℝ (Fin n) =>
                    (WithLp.ofLp (p := 2) (V := Fin n → ℝ) ω) i,
                  fun ω : EuclideanSpace ℝ (Fin n) =>
                    (WithLp.ofLp (p := 2) (V := Fin n → ℝ) ω) j; μ] := by
    intro i j
    rw [covariance_const_mul_left, covariance_const_mul_right]
    ring
  simp_rw [hPull]
  -- Final step: identify each inner scalar covariance with the matrix entry
  -- `S i j` using `covariance_multivariateGaussian` at `m = 0`.
  have hCovEntry : ∀ i j : Fin n,
      cov[fun ω : EuclideanSpace ℝ (Fin n) =>
            (WithLp.ofLp (p := 2) (V := Fin n → ℝ) ω) i,
          fun ω : EuclideanSpace ℝ (Fin n) =>
            (WithLp.ofLp (p := 2) (V := Fin n → ℝ) ω) j; μ]
        = S i j := by
    intro i j
    -- Unfold `covariance` and apply `covariance_multivariateGaussian` at `m = 0`.
    -- For `m = 0`, `(ofLp m) i = 0`, so the centered integral is the raw integral.
    -- `cov[X, Y; μ] = ∫ ω, (X ω - μ[X]) * (Y ω - μ[Y]) ∂μ`.
    -- We show both sides equal `∫ ω, (ofLp ω) i * (ofLp ω) j ∂μ`, using that the
    -- means of `(ofLp ω) i` and `(ofLp ω) j` under `μ = multivariateGaussian 0 S hS`
    -- are zero.
    have hMeanZero : ∀ k : Fin n,
        μ[fun ω : EuclideanSpace ℝ (Fin n) =>
          (WithLp.ofLp (p := 2) (V := Fin n → ℝ) ω) k] = 0 := by
      intro k
      -- `μ[ofLp · k] = (ofLp 0) k = 0` via `integral_eval_multivariateGaussian` at `m = 0`.
      have h := integral_eval_multivariateGaussian
        (m := (0 : EuclideanSpace ℝ (Fin n))) (S := S) (hS := hS) k
      rw [hμ]
      simp at h
      exact h
    -- Apply `covariance` definition and simplify the centering.
    rw [covariance]
    simp_rw [hMeanZero, sub_zero]
    -- Now goal: `∫ ω, (ofLp ω) i * (ofLp ω) j ∂μ = S i j`.
    have h := covariance_multivariateGaussian (m := (0 : EuclideanSpace ℝ (Fin n)))
      (S := S) (hS := hS) i j
    -- `h : ∫ x, ((ofLp x) i - (ofLp 0) i) * ((ofLp x) j - (ofLp 0) j) ∂μ = S i j`.
    -- `(ofLp 0) k = 0`.
    have hZero : ∀ k : Fin n,
        (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (0 : EuclideanSpace ℝ (Fin n))) k = 0 := by
      intro k; simp
    simp_rw [hZero, sub_zero] at h
    rw [hμ]
    exact h
  -- Substitute `hCovEntry` and we are done.
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [hCovEntry i j]

end ProbabilityTheory
