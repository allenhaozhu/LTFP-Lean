/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.Distributions.JointPriorObservationSndMean
import LTFP.MathlibExt.Probability.Distributions.JointPriorObservationSndCovariance
import LTFP.MathlibExt.Probability.Distributions.GaussianConjugatePosteriorSchur
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Moments.CovarianceBilin

/-!
# The observation marginal of the joint prior-observation measure is multivariate Gaussian

Identifies `joint.snd` with the zero-mean multivariate Gaussian whose
covariance is the observation covariance `X · priorCov · Xᵀ + ν²·I`,
via `ProbabilityTheory.IsGaussian.ext`. Bridge step toward the B4 N2
carrier closure (gaussianPosteriorMean_ridge_form).

The proof proceeds by checking the two hypotheses of `IsGaussian.ext`:

* **Mean equality.** Both measures have integral `0`, via
  `jointPriorObservation_snd_integral_vector` and
  `integral_id_multivariateGaussian_zero`.
* **Covariance bilinear form equality.** Reduce both measures to the
  `μ.map (fun ω ↦ toLp 2 (X · ω))` form (which holds via the identity
  `toLp 2 ∘ WithLp.ofLp = id` and `Measure.map_id`), then apply
  `covarianceBilin_apply_pi` to expand the bilinear form as a double
  sum over coordinate covariances, which are identified by
  `jointPriorObservation_snd_covariance_eval` and
  `covariance_multivariateGaussian`.
-/

open MeasureTheory ProbabilityTheory WithLp
open scoped Matrix ProbabilityTheory RealInnerProductSpace

namespace ProbabilityTheory

/-- Auxiliary identity. The measure `μ` on `EuclideanSpace ℝ (Fin n)`
equals its pushforward under
`fun ω ↦ toLp 2 (fun i ↦ (WithLp.ofLp ω) i)`, because that function
is definitionally `id`. -/
private lemma map_toLp_ofLp_eq_self
    {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) :
    μ.map (fun ω : EuclideanSpace ℝ (Fin n) =>
        toLp 2 (fun i : Fin n => (WithLp.ofLp (p := 2) (V := Fin n → ℝ) ω) i))
      = μ := by
  have hfun :
      (fun ω : EuclideanSpace ℝ (Fin n) =>
          toLp 2 (fun i : Fin n => (WithLp.ofLp (p := 2) (V := Fin n → ℝ) ω) i))
        = id := by
    funext ω
    -- `fun i ↦ (ofLp ω) i = ofLp ω` by eta; `toLp 2 (ofLp ω) = ω` by `toLp_ofLp`.
    rfl
  rw [hfun, Measure.map_id]

/-- The observation marginal of the joint prior-observation law is the zero-mean
multivariate Gaussian with the observation covariance. -/
theorem jointPriorObservation_snd_eq_multivariateGaussian
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ) (hPrior : priorCov.PosSemidef)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ)
    (hObs : (Matrix.obsCov priorCov X (ν ^ 2)).PosSemidef) :
    (jointPriorObservation priorCov hPrior X ν).snd =
      multivariateGaussian 0 (Matrix.obsCov priorCov X (ν ^ 2)) hObs := by
  classical
  -- Abbreviations.
  set μ : Measure (EuclideanSpace ℝ (Fin n)) :=
    (jointPriorObservation priorCov hPrior X ν).snd with hμ
  set S : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.obsCov priorCov X (ν ^ 2) with hS
  set μG : Measure (EuclideanSpace ℝ (Fin n)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S hObs with hμG
  -- Gaussianity of both measures (required by `IsGaussian.ext`).
  have hμGauss : IsGaussian μ := by
    show IsGaussian (jointPriorObservation priorCov hPrior X ν).snd
    infer_instance
  have hμGGauss : IsGaussian μG := by
    show IsGaussian (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S hObs)
    infer_instance
  -- Mean equality: both means are `0`.
  have hMeanμ : μ[id] = (0 : EuclideanSpace ℝ (Fin n)) := by
    show ∫ y, y ∂μ = (0 : EuclideanSpace ℝ (Fin n))
    exact jointPriorObservation_snd_integral_vector priorCov hPrior X ν
  have hMeanμG : μG[id] = (0 : EuclideanSpace ℝ (Fin n)) := by
    show ∫ y, y ∂μG = (0 : EuclideanSpace ℝ (Fin n))
    exact integral_id_multivariateGaussian_zero (d := n) S hObs
  -- Per-coordinate integrability (MemLp at p = 2) for both measures.
  have hCoordμ : ∀ i : Fin n, MemLp
      (fun y : EuclideanSpace ℝ (Fin n) =>
        (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i) 2 μ := by
    intro i
    have h : MemLp (id : EuclideanSpace ℝ (Fin n) → _) 2 μ :=
      IsGaussian.memLp_two_id (μ := μ)
    exact MemLp.eval_piLp (p := 2) (q := 2) (E := fun _ : Fin n => ℝ)
      (f := fun ω => ω) h i
  have hCoordμG : ∀ i : Fin n, MemLp
      (fun y : EuclideanSpace ℝ (Fin n) =>
        (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i) 2 μG := by
    intro i
    have h : MemLp (id : EuclideanSpace ℝ (Fin n) → _) 2 μG :=
      IsGaussian.memLp_two_id (μ := μG)
    exact MemLp.eval_piLp (p := 2) (q := 2) (E := fun _ : Fin n => ℝ)
      (f := fun ω => ω) h i
  -- Coordinate-wise covariance under `μ`: equals `S i j`.
  have hCovμ : ∀ i j : Fin n,
      cov[(fun y : EuclideanSpace ℝ (Fin n) =>
              (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i),
          (fun y : EuclideanSpace ℝ (Fin n) =>
              (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j); μ] = S i j := by
    intro i j
    -- The per-coordinate means are zero.
    have hMi := jointPriorObservation_snd_integral_eval_coord
      priorCov hPrior X ν i
    have hMj := jointPriorObservation_snd_integral_eval_coord
      priorCov hPrior X ν j
    -- Per-coordinate means under `μ` are zero (with the right syntactic shape).
    have hMi' : μ[fun y : EuclideanSpace ℝ (Fin n) =>
        (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i] = 0 := hMi
    have hMj' : μ[fun y : EuclideanSpace ℝ (Fin n) =>
        (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j] = 0 := hMj
    rw [covariance, hMi', hMj']
    simp only [sub_zero]
    -- Goal: `∫ y, (ofLp y) i * (ofLp y) j ∂μ = S i j`.
    have h := jointPriorObservation_snd_covariance_eval
      priorCov hPrior X ν i j
    -- `h : ∫ y, ... ∂.snd = (X * priorCov * Xᵀ) i j + (ν^2 • 1) i j`
    -- `μ = .snd` is the same measure, and
    -- `S i j = (X * priorCov * Xᵀ + ν^2 • 1) i j = (X * priorCov * Xᵀ) i j + (ν^2 • 1) i j`
    -- via the definition of `obsCov`.
    show ∫ y, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
            * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j ∂μ = S i j
    rw [h]
    -- Now: `(X * priorCov * Xᵀ) i j + (ν^2 • 1) i j = S i j`.
    -- `S = Matrix.obsCov priorCov X (ν^2) = X * priorCov * Xᵀ + ν^2 • 1`.
    show (X * priorCov * Xᵀ) i j + (ν ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) i j =
        (Matrix.obsCov priorCov X (ν ^ 2)) i j
    unfold Matrix.obsCov
    simp [Matrix.add_apply]
  -- Coordinate-wise covariance under `μG`: also equals `S i j`.
  have hCovμG : ∀ i j : Fin n,
      cov[(fun y : EuclideanSpace ℝ (Fin n) =>
              (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i),
          (fun y : EuclideanSpace ℝ (Fin n) =>
              (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j); μG] = S i j := by
    intro i j
    have hMi := integral_eval_multivariateGaussian
      (m := (0 : EuclideanSpace ℝ (Fin n))) (S := S) (hS := hObs) i
    have hMj := integral_eval_multivariateGaussian
      (m := (0 : EuclideanSpace ℝ (Fin n))) (S := S) (hS := hObs) j
    -- `(WithLp.ofLp 0) i = 0` for the zero element.
    have h0i : (WithLp.ofLp (p := 2) (V := Fin n → ℝ)
        (0 : EuclideanSpace ℝ (Fin n))) i = 0 := by simp
    have h0j : (WithLp.ofLp (p := 2) (V := Fin n → ℝ)
        (0 : EuclideanSpace ℝ (Fin n))) j = 0 := by simp
    have hMi' : μG[fun y : EuclideanSpace ℝ (Fin n) =>
        (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i] = 0 := by
      show ∫ y, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i ∂μG = 0
      rw [hMi, h0i]
    have hMj' : μG[fun y : EuclideanSpace ℝ (Fin n) =>
        (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j] = 0 := by
      show ∫ y, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j ∂μG = 0
      rw [hMj, h0j]
    rw [covariance, hMi', hMj']
    simp only [sub_zero]
    -- Apply `covariance_multivariateGaussian` at `m = 0`.
    have hCov := covariance_multivariateGaussian
      (m := (0 : EuclideanSpace ℝ (Fin n))) (S := S) (hS := hObs) i j
    -- `hCov : ∫ x, ((ofLp x) i - (ofLp 0) i) * ((ofLp x) j - (ofLp 0) j) ∂μG = S i j`.
    show ∫ y, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
            * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j ∂μG = S i j
    have := hCov
    simp only [h0i, h0j, sub_zero] at this
    exact this
  -- Reduce `covarianceBilin μ` (resp. `μG`) to the `pi` form via the
  -- `μ.map (fun ω ↦ toLp 2 (fun i ↦ (ofLp ω) i)) = μ` identity.
  have hBilin : covarianceBilin μ = covarianceBilin μG := by
    ext x y
    -- Rewrite `μ` as `μ.map (toLp ∘ ofLp)` to apply `covarianceBilin_apply_pi`.
    have hμRewrite : covarianceBilin μ x y =
        ∑ i, ∑ j, x i * y j *
          cov[(fun ω : EuclideanSpace ℝ (Fin n) =>
              (WithLp.ofLp (p := 2) (V := Fin n → ℝ) ω) i),
            (fun ω : EuclideanSpace ℝ (Fin n) =>
              (WithLp.ofLp (p := 2) (V := Fin n → ℝ) ω) j); μ] := by
      conv_lhs => rw [← map_toLp_ofLp_eq_self μ]
      exact covarianceBilin_apply_pi
        (μ := μ) (ι := Fin n)
        (X := fun i ω => (WithLp.ofLp (p := 2) (V := Fin n → ℝ) ω) i)
        hCoordμ x y
    have hμGRewrite : covarianceBilin μG x y =
        ∑ i, ∑ j, x i * y j *
          cov[(fun ω : EuclideanSpace ℝ (Fin n) =>
              (WithLp.ofLp (p := 2) (V := Fin n → ℝ) ω) i),
            (fun ω : EuclideanSpace ℝ (Fin n) =>
              (WithLp.ofLp (p := 2) (V := Fin n → ℝ) ω) j); μG] := by
      conv_lhs => rw [← map_toLp_ofLp_eq_self μG]
      exact covarianceBilin_apply_pi
        (μ := μG) (ι := Fin n)
        (X := fun i ω => (WithLp.ofLp (p := 2) (V := Fin n → ℝ) ω) i)
        hCoordμG x y
    rw [hμRewrite, hμGRewrite]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hCovμ i j, hCovμG i j]
  -- Apply `IsGaussian.ext`.
  exact IsGaussian.ext (hMeanμ.trans hMeanμG.symm) hBilin

end ProbabilityTheory
