/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.Distributions.GaussianPosteriorCompProdIsGaussian
import LTFP.MathlibExt.Probability.Distributions.JointPriorObservationCrossCovariance
import LTFP.MathlibExt.Probability.Distributions.JointPriorObservationSndCovariance
import LTFP.MathlibExt.Probability.Moments.CovarianceBilinProdPi

/-!
# Wrapped covariance equality for the Gaussian posterior compProd

The composition-product `joint.snd ⊗ₘ gaussianPosteriorKernel` and the
swapped joint `joint.map Prod.swap` are both centered Gaussians on the
plain product `EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)`. Since
the plain product has no `InnerProductSpace ℝ` instance, we cannot apply
`IsGaussian.ext` directly. Instead we wrap both measures through the
canonical continuous linear map `wrap : E_n × E_d →L[ℝ] WithLp 2 (E_n × E_d)`
and prove that on the wrapped side both Gaussians have the same
`covarianceBilin`.

This is the load-bearing math content of B4 N2 Sub-I4.D. The thin
unwrap-to-plain-product step (the final Sub-I4.D measure equality) is
supplied by `GaussianPosteriorCompProdEqSwappedJoint.lean`.

## Strategy

1. Apply `covarianceBilin_apply_prod_pi` (Sub-I4.C) to both wrapped
   measures, with `Ω := E_n × E_d` and coordinate families
   `Y i ω := (WithLp.ofLp ω.1) i`, `T a ω := (WithLp.ofLp ω.2) a`.
2. Identify each of the four pairwise scalar covariances as equal on
   both sides by tracking them back through Sub-I4.A
   (`gaussianPosteriorKernel_compProd_eq_map_prod`) and
   `jointPriorObservation_eq_map_prod`, then applying `covariance_map_fun`
   and the matrix bridge `K_S_Ktrans_eq_priorCov_Xtrans_Sinv_X_priorCov`
   together with the Schur identity
   `Matrix.schurPosteriorCov_eq_schur_complement`.
3. Conclude the bilinear forms agree.
-/

open MeasureTheory ProbabilityTheory WithLp
open scoped Matrix ENNReal

namespace ProbabilityTheory

/-- `cov[θ_i, θ_j]` against a centered multivariate Gaussian equals
`S i j`. This is the `covariance` shape (auto-subtracts the zero means)
of `covariance_multivariateGaussian`. -/
lemma covariance_coord_multivariateGaussian_zero
    {m : ℕ} (S : Matrix (Fin m) (Fin m) ℝ) (hS : S.PosSemidef)
    (i j : Fin m) :
    cov[
      fun x : EuclideanSpace ℝ (Fin m) =>
        (WithLp.ofLp (p := 2) (V := Fin m → ℝ) x) i,
      fun x : EuclideanSpace ℝ (Fin m) =>
        (WithLp.ofLp (p := 2) (V := Fin m → ℝ) x) j;
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin m)) S hS]
      = S i j := by
  rw [covariance]
  rw [integral_eval_multivariateGaussian_zero S hS i,
      integral_eval_multivariateGaussian_zero S hS j]
  simp only [sub_zero]
  have h := covariance_multivariateGaussian
    (m := (0 : EuclideanSpace ℝ (Fin m))) (S := S) (hS := hS) i j
  simpa using h

/-- The canonical wrap continuous linear map
`E_n × E_d →L[ℝ] WithLp 2 (E_n × E_d)`. -/
noncomputable def wrapEnEd (n d : ℕ) :
    EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) →L[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℝ (Fin d))).symm.toContinuousLinearMap

@[simp] lemma wrapEnEd_apply (n d : ℕ)
    (p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)) :
    wrapEnEd n d p = WithLp.toLp 2 p := rfl

/-- **Sub-I4.D wrapped covariance equality.**
The `WithLp 2`-wrapped composition-product `joint.snd ⊗ₘ posteriorKernel`
and the wrapped swapped joint `joint.map Prod.swap` have the same
`covarianceBilin`. -/
theorem gaussianPosteriorKernel_compProd_covarianceBilin_wrapped_eq_swapped_joint
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ) (hPrior : priorCov.PosDef)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) (hν : ν ≠ 0) :
    covarianceBilin
        (((jointPriorObservation priorCov hPrior.posSemidef X ν).snd ⊗ₘ
            gaussianPosteriorKernel priorCov X ν
              (gaussianPosterior_covariances_pos priorCov hPrior X ν hν).2).map
          (wrapEnEd n d)) =
      covarianceBilin
        (((jointPriorObservation priorCov hPrior.posSemidef X ν).map Prod.swap).map
          (wrapEnEd n d)) := by
  classical
  obtain ⟨hObsPD, hPost⟩ :=
    gaussianPosterior_covariances_pos priorCov hPrior X ν hν
  have hObs : (Matrix.obsCov priorCov X (ν ^ 2)).PosSemidef := hObsPD.posSemidef
  -- The two underlying measures.
  set μL : Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)) :=
    (jointPriorObservation priorCov hPrior.posSemidef X ν).snd ⊗ₘ
      gaussianPosteriorKernel priorCov X ν hPost with hμL_def
  set μR : Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)) :=
    (jointPriorObservation priorCov hPrior.posSemidef X ν).map Prod.swap with hμR_def
  set wrap : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) →L[ℝ]
      WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)) :=
    wrapEnEd n d with hwrap
  -- Gaussian instances.
  have hμLGauss : IsGaussian μL := by
    show IsGaussian
      ((jointPriorObservation priorCov hPrior.posSemidef X ν).snd ⊗ₘ
        gaussianPosteriorKernel priorCov X ν hPost)
    rw [jointPriorObservation_snd_eq_multivariateGaussian
        priorCov hPrior.posSemidef X ν hObs]
    infer_instance
  have hμRGauss : IsGaussian μR := by
    show IsGaussian
      ((jointPriorObservation priorCov hPrior.posSemidef X ν).map Prod.swap)
    have hJoint : IsGaussian (jointPriorObservation priorCov hPrior.posSemidef X ν) :=
      inferInstance
    set swapCLM :
        EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) →L[ℝ]
          EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) :=
      (ContinuousLinearEquiv.prodComm ℝ
        (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin n))).toContinuousLinearMap
      with hswapCLM
    have hSwap_fun :
        (Prod.swap : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) →
          EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)) =
          (swapCLM : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) →
            EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)) := by
      funext p; simp [swapCLM]
    rw [hSwap_fun]
    infer_instance
  -- Coordinate families.
  set Y : Fin n → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) → ℝ :=
    fun i ω => (WithLp.ofLp (p := 2) (V := Fin n → ℝ) ω.1) i with hY_def
  set T : Fin d → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) → ℝ :=
    fun a ω => (WithLp.ofLp (p := 2) (V := Fin d → ℝ) ω.2) a with hT_def
  -- L² of `Y i` and `T a` against any Gaussian measure on `E_n × E_d`.
  have hY_memLp_of_gauss :
      ∀ (μ : Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)))
        [IsGaussian μ] (i : Fin n), MemLp (Y i) 2 μ := by
    intro μ _ i
    have hMemLpId : MemLp (id : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) → _)
        2 μ := IsGaussian.memLp_two_id (μ := μ)
    have hMemLpFst : MemLp
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) => p.1) 2 μ := by
      have := hMemLpId.continuousLinearMap_comp
        (ContinuousLinearMap.fst ℝ
          (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin d)))
      simpa using this
    exact MemLp.eval_piLp hMemLpFst i
  have hT_memLp_of_gauss :
      ∀ (μ : Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)))
        [IsGaussian μ] (a : Fin d), MemLp (T a) 2 μ := by
    intro μ _ a
    have hMemLpId : MemLp (id : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) → _)
        2 μ := IsGaussian.memLp_two_id (μ := μ)
    have hMemLpSnd : MemLp
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) => p.2) 2 μ := by
      have := hMemLpId.continuousLinearMap_comp
        (ContinuousLinearMap.snd ℝ
          (EuclideanSpace ℝ (Fin n)) (EuclideanSpace ℝ (Fin d)))
      simpa using this
    exact MemLp.eval_piLp hMemLpSnd a
  -- `wrap ω = WithLp.toLp 2 ((WithLp.toLp 2 (Y · ω), WithLp.toLp 2 (T · ω)))`.
  have hWrapEq :
      (fun ω : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) => wrap ω) =
        fun ω => WithLp.toLp 2
          ((WithLp.toLp 2 (Y · ω), WithLp.toLp 2 (T · ω)) :
            EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)) := by
    funext ω
    show WithLp.toLp 2 ω = WithLp.toLp 2 ((ω.1, ω.2) :
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d))
    rfl
  -- ===== Reduce each side via Sub-I4.C =====
  ext u v
  have hLHS :
      covarianceBilin (μL.map wrap) u v =
        (∑ i, ∑ j, u.fst i * v.fst j * cov[Y i, Y j; μL]) +
        (∑ i, ∑ b, u.fst i * v.snd b * cov[Y i, T b; μL]) +
        (∑ a, ∑ j, u.snd a * v.fst j * cov[T a, Y j; μL]) +
        (∑ a, ∑ b, u.snd a * v.snd b * cov[T a, T b; μL]) := by
    rw [show μL.map wrap = μL.map (fun ω => WithLp.toLp 2
        ((WithLp.toLp 2 (Y · ω), WithLp.toLp 2 (T · ω)) :
          EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d))) from by rw [← hWrapEq]]
    exact covarianceBilin_apply_prod_pi
      (μ := μL) (Y := Y) (T := T)
      (fun i => hY_memLp_of_gauss μL i)
      (fun a => hT_memLp_of_gauss μL a)
      u v
  have hRHS :
      covarianceBilin (μR.map wrap) u v =
        (∑ i, ∑ j, u.fst i * v.fst j * cov[Y i, Y j; μR]) +
        (∑ i, ∑ b, u.fst i * v.snd b * cov[Y i, T b; μR]) +
        (∑ a, ∑ j, u.snd a * v.fst j * cov[T a, Y j; μR]) +
        (∑ a, ∑ b, u.snd a * v.snd b * cov[T a, T b; μR]) := by
    rw [show μR.map wrap = μR.map (fun ω => WithLp.toLp 2
        ((WithLp.toLp 2 (Y · ω), WithLp.toLp 2 (T · ω)) :
          EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d))) from by rw [← hWrapEq]]
    exact covarianceBilin_apply_prod_pi
      (μ := μR) (Y := Y) (T := T)
      (fun i => hY_memLp_of_gauss μR i)
      (fun a => hT_memLp_of_gauss μR a)
      u v
  rw [hLHS, hRHS]
  -- ===== Block-by-block covariance identification =====
  -- The common reduced measure: `joint.snd = obsGauss`.
  set obsMeas : Measure (EuclideanSpace ℝ (Fin n)) :=
    (jointPriorObservation priorCov hPrior.posSemidef X ν).snd with hobsMeas_def
  set priorMeas : Measure (EuclideanSpace ℝ (Fin d)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) priorCov hPrior.posSemidef
    with hpriorMeas_def
  -- BLOCK (Y, Y): both equal a cov over `joint.snd`.
  have hYY : ∀ i j, cov[Y i, Y j; μL] = cov[Y i, Y j; μR] := by
    intro i j
    -- LHS first marginal.
    have hL_fst : μL.map (fun p => p.1) = obsMeas := by
      show ((jointPriorObservation priorCov hPrior.posSemidef X ν).snd ⊗ₘ
            gaussianPosteriorKernel priorCov X ν hPost).map (fun p => p.1)
        = obsMeas
      exact Measure.fst_compProd _ _
    -- RHS first marginal: μR.fst = joint.snd via swap.
    have hR_fst : μR.map (fun p => p.1) = obsMeas := by
      show ((jointPriorObservation priorCov hPrior.posSemidef X ν).map Prod.swap).map
              (fun p => p.1) = obsMeas
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      show (jointPriorObservation priorCov hPrior.posSemidef X ν).map
              ((fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) => p.1) ∘
                Prod.swap) = obsMeas
      have hcomp : ((fun p : EuclideanSpace ℝ (Fin n) ×
            EuclideanSpace ℝ (Fin d) => p.1) ∘
            (Prod.swap : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) →
              EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)))
          = (fun p => p.2) := by
        funext p; rfl
      rw [hcomp]
      rfl
    -- Now `Y i ω = (ofLp ω.1) i`, so `cov[Y i, Y j; μL] = cov[(ofLp ·) i, (ofLp ·) j; μL.fst]`.
    -- We use `covariance_map_fun` in the reverse direction.
    have hL_red : cov[Y i, Y j; μL] = cov[
        fun y : EuclideanSpace ℝ (Fin n) =>
          (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i,
        fun y : EuclideanSpace ℝ (Fin n) =>
          (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j; obsMeas] := by
      conv_lhs => rw [show (Y i : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) → ℝ) =
        (fun y : EuclideanSpace ℝ (Fin n) => (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i) ∘
          (fun p => p.1) from rfl,
        show (Y j : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) → ℝ) =
        (fun y : EuclideanSpace ℝ (Fin n) => (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j) ∘
          (fun p => p.1) from rfl]
      rw [show cov[(fun y : EuclideanSpace ℝ (Fin n) =>
            (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i) ∘ (fun p => p.1),
          (fun y : EuclideanSpace ℝ (Fin n) =>
            (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j) ∘ (fun p => p.1); μL] =
          cov[(fun y : EuclideanSpace ℝ (Fin n) =>
              (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i),
            (fun y : EuclideanSpace ℝ (Fin n) =>
              (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j); μL.map (fun p => p.1)] from ?_]
      · rw [hL_fst]
      · symm
        rw [covariance_map (Z := (fun p : EuclideanSpace ℝ (Fin n) ×
              EuclideanSpace ℝ (Fin d) => p.1))
            (by fun_prop) (by fun_prop) (by fun_prop)]
    have hR_red : cov[Y i, Y j; μR] = cov[
        fun y : EuclideanSpace ℝ (Fin n) =>
          (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i,
        fun y : EuclideanSpace ℝ (Fin n) =>
          (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j; obsMeas] := by
      conv_lhs => rw [show (Y i : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) → ℝ) =
        (fun y : EuclideanSpace ℝ (Fin n) => (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i) ∘
          (fun p => p.1) from rfl,
        show (Y j : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) → ℝ) =
        (fun y : EuclideanSpace ℝ (Fin n) => (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j) ∘
          (fun p => p.1) from rfl]
      rw [show cov[(fun y : EuclideanSpace ℝ (Fin n) =>
            (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i) ∘ (fun p => p.1),
          (fun y : EuclideanSpace ℝ (Fin n) =>
            (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j) ∘ (fun p => p.1); μR] =
          cov[(fun y : EuclideanSpace ℝ (Fin n) =>
              (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i),
            (fun y : EuclideanSpace ℝ (Fin n) =>
              (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j); μR.map (fun p => p.1)] from ?_]
      · rw [hR_fst]
      · symm
        rw [covariance_map (Z := (fun p : EuclideanSpace ℝ (Fin n) ×
              EuclideanSpace ℝ (Fin d) => p.1))
            (by fun_prop) (by fun_prop) (by fun_prop)]
    rw [hL_red, hR_red]
  -- BLOCK (T, T): both equal `priorCov a b`.
  -- LHS uses Sub-I4.A; RHS uses snd of jointPriorObservation.swap = joint.fst = priorGauss.
  have hTT : ∀ a b, cov[T a, T b; μL] = cov[T a, T b; μR] := by
    intro a b
    -- For RHS: μR.map snd = joint.fst = priorGauss.
    have hR_snd : μR.map (fun p => p.2) = priorMeas := by
      show ((jointPriorObservation priorCov hPrior.posSemidef X ν).map Prod.swap).map
              (fun p => p.2) = priorMeas
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      show (jointPriorObservation priorCov hPrior.posSemidef X ν).map
              ((fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) => p.2) ∘
                (Prod.swap : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) →
                  EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d))) = priorMeas
      have hcomp : ((fun p : EuclideanSpace ℝ (Fin n) ×
            EuclideanSpace ℝ (Fin d) => p.2) ∘
            (Prod.swap : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) →
              EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)))
          = (fun p => p.1) := by
        funext p; rfl
      rw [hcomp]
      show (jointPriorObservation priorCov hPrior.posSemidef X ν).fst = priorMeas
      unfold jointPriorObservation
      exact Measure.fst_compProd _ _
    have hR_red : cov[T a, T b; μR] = cov[
        fun θ : EuclideanSpace ℝ (Fin d) =>
          (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) a,
        fun θ : EuclideanSpace ℝ (Fin d) =>
          (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) b; priorMeas] := by
      conv_lhs => rw [show (T a : EuclideanSpace ℝ (Fin n) ×
          EuclideanSpace ℝ (Fin d) → ℝ) =
        (fun θ : EuclideanSpace ℝ (Fin d) => (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) a) ∘
          (fun p => p.2) from rfl,
        show (T b : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) → ℝ) =
        (fun θ : EuclideanSpace ℝ (Fin d) => (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) b) ∘
          (fun p => p.2) from rfl]
      rw [show cov[(fun θ : EuclideanSpace ℝ (Fin d) =>
            (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) a) ∘ (fun p => p.2),
          (fun θ : EuclideanSpace ℝ (Fin d) =>
            (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) b) ∘ (fun p => p.2); μR] =
          cov[(fun θ : EuclideanSpace ℝ (Fin d) =>
              (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) a),
            (fun θ : EuclideanSpace ℝ (Fin d) =>
              (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) b); μR.map (fun p => p.2)] from ?_]
      · rw [hR_snd]
      · symm
        rw [covariance_map (Z := (fun p : EuclideanSpace ℝ (Fin n) ×
              EuclideanSpace ℝ (Fin d) => p.2))
            (by fun_prop) (by fun_prop) (by fun_prop)]
    -- For LHS: use Sub-I4.A.
    have hL_eq : μL =
        ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
              (Matrix.obsCov priorCov X (ν ^ 2)) hObs).prod
            (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
              (Matrix.schurPosteriorCov priorCov X (ν ^ 2)) hPost)).map
              (posteriorJointMap priorCov X ν) := by
      show ((jointPriorObservation priorCov hPrior.posSemidef X ν).snd ⊗ₘ
              gaussianPosteriorKernel priorCov X ν hPost) = _
      rw [jointPriorObservation_snd_eq_multivariateGaussian
          priorCov hPrior.posSemidef X ν hObs]
      exact gaussianPosteriorKernel_compProd_eq_map_prod priorCov X ν hObs hPost
    -- Now `cov[T a, T b; μL]` after `covariance_map_fun` becomes a cov on the product.
    have hL_red : cov[T a, T b; μL] = cov[
        fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) =>
          T a (posteriorJointMap priorCov X ν p),
        fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) =>
          T b (posteriorJointMap priorCov X ν p);
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
            (Matrix.obsCov priorCov X (ν ^ 2)) hObs).prod
          (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
            (Matrix.schurPosteriorCov priorCov X (ν ^ 2)) hPost)] := by
      rw [hL_eq, covariance_map_fun (by fun_prop) (by fun_prop) (by fun_prop)]
    rw [hL_red, hR_red]
    -- Goal: cov[T a ∘ posteriorJointMap, T b ∘ posteriorJointMap; obs × schur]
    --     = cov[θ_a, θ_b; priorGauss]
    -- LHS decomposes via posteriorJointMap_apply into a sum involving
    -- `regressionCLM K p.1` and `p.2`, where K = priorCov * Xᵀ * S⁻¹.
    set S' : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.obsCov priorCov X (ν ^ 2) with hS'_def
    set P : Matrix (Fin d) (Fin d) ℝ :=
      Matrix.schurPosteriorCov priorCov X (ν ^ 2) with hP_def
    set K : Matrix (Fin d) (Fin n) ℝ :=
      priorCov * Xᵀ * S'⁻¹ with hK_def
    set obsG : Measure (EuclideanSpace ℝ (Fin n)) :=
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S' hObs with hobsG_def
    set postG : Measure (EuclideanSpace ℝ (Fin d)) :=
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) P hPost with hpostG_def
    set q : Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)) :=
      obsG.prod postG with hq_def
    -- Two "marginal" random variables.
    set U : Fin d → EuclideanSpace ℝ (Fin n) → ℝ :=
      fun c y =>
        (WithLp.ofLp (p := 2) (V := Fin d → ℝ) (regressionCLM K y)) c
      with hU_def
    set E : Fin d → EuclideanSpace ℝ (Fin d) → ℝ :=
      fun c ε => (WithLp.ofLp (p := 2) (V := Fin d → ℝ) ε) c
      with hE_def
    set Up : Fin d → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) → ℝ :=
      fun c p => U c p.1 with hUp_def
    set Ep : Fin d → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) → ℝ :=
      fun c p => E c p.2 with hEp_def
    -- Identify `T c ∘ posteriorJointMap = Up c + Ep c`.
    have hT_decomp : ∀ c,
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) =>
          T c (posteriorJointMap priorCov X ν p)) = Up c + Ep c := by
      intro c
      funext p
      simp [hT_def, hUp_def, hEp_def, hU_def, hE_def, hK_def, hS'_def,
        posteriorJointMap_apply, Pi.add_apply]
    -- L²/MemLp facts.
    have hObsG_Gauss : IsGaussian obsG := by
      show IsGaussian (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S' hObs)
      infer_instance
    have hPostG_Gauss : IsGaussian postG := by
      show IsGaussian (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) P hPost)
      infer_instance
    have hObsG_Prob : IsProbabilityMeasure obsG := by
      show IsProbabilityMeasure
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S' hObs)
      infer_instance
    have hPostG_Prob : IsProbabilityMeasure postG := by
      show IsProbabilityMeasure
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) P hPost)
      infer_instance
    have hObsId : MemLp (id : EuclideanSpace ℝ (Fin n) → _) 2 obsG :=
      ProbabilityTheory.IsGaussian.memLp_two_id (μ := obsG)
    have hPostId : MemLp (id : EuclideanSpace ℝ (Fin d) → _) 2 postG :=
      ProbabilityTheory.IsGaussian.memLp_two_id (μ := postG)
    have hU_mem : ∀ c, MemLp (U c) 2 obsG := by
      intro c
      have hReg : MemLp (fun y : EuclideanSpace ℝ (Fin n) => regressionCLM K y) 2 obsG := by
        have := hObsId.continuousLinearMap_comp (regressionCLM K)
        simpa using this
      exact MemLp.eval_piLp hReg c
    have hE_mem : ∀ c, MemLp (E c) 2 postG := by
      intro c
      exact MemLp.eval_piLp hPostId c
    have hUp_mem : ∀ c, MemLp (Up c) 2 q := by
      intro c
      have := (hU_mem c).comp_fst postG
      simpa [hq_def, hUp_def, hU_def] using this
    have hEp_mem : ∀ c, MemLp (Ep c) 2 q := by
      intro c
      have := (hE_mem c).comp_snd obsG
      simpa [hq_def, hEp_def, hE_def] using this
    -- Now split the covariance via bilinearity.
    rw [hT_decomp a, hT_decomp b]
    rw [covariance_add_left (hUp_mem a) (hEp_mem a)
        ((hUp_mem b).add (hEp_mem b))]
    rw [covariance_add_right (hUp_mem a) (hUp_mem b) (hEp_mem b),
        covariance_add_right (hEp_mem a) (hUp_mem b) (hEp_mem b)]
    -- Cross terms vanish by independence (q = obsG.prod postG).
    have hUE : cov[Up a, Ep b; q] = 0 := by
      have := covariance_fst_snd_prod (μ := obsG) (ν := postG)
        (hU_mem a) (hE_mem b)
      simpa [hq_def, hUp_def, hEp_def] using this
    have hEU : cov[Ep a, Up b; q] = 0 := by
      rw [covariance_comm]
      have := covariance_fst_snd_prod (μ := obsG) (ν := postG)
        (hU_mem b) (hE_mem a)
      simpa [hq_def, hUp_def, hEp_def] using this
    -- Reduce diagonal terms to single-factor measures.
    have hUU : cov[Up a, Up b; q] = cov[U a, U b; obsG] := by
      have hMap : q.map (fun p : EuclideanSpace ℝ (Fin n) ×
            EuclideanSpace ℝ (Fin d) => p.1) = obsG := by
        rw [hq_def]
        exact Measure.fst_prod
      have := covariance_map_fun
        (μ := q) (Z := fun p : EuclideanSpace ℝ (Fin n) ×
          EuclideanSpace ℝ (Fin d) => p.1)
        (X := U a) (Y := U b)
        (by rw [hMap]; exact (hU_mem a).aestronglyMeasurable)
        (by rw [hMap]; exact (hU_mem b).aestronglyMeasurable)
        measurable_fst.aemeasurable
      rw [hMap] at this
      exact this.symm
    have hEE : cov[Ep a, Ep b; q] = cov[E a, E b; postG] := by
      have hMap : q.map (fun p : EuclideanSpace ℝ (Fin n) ×
            EuclideanSpace ℝ (Fin d) => p.2) = postG := by
        rw [hq_def]
        exact Measure.snd_prod
      have := covariance_map_fun
        (μ := q) (Z := fun p : EuclideanSpace ℝ (Fin n) ×
          EuclideanSpace ℝ (Fin d) => p.2)
        (X := E a) (Y := E b)
        (by rw [hMap]; exact (hE_mem a).aestronglyMeasurable)
        (by rw [hMap]; exact (hE_mem b).aestronglyMeasurable)
        measurable_snd.aemeasurable
      rw [hMap] at this
      exact this.symm
    -- Compute cov[U a, U b; obsG] = (K * S' * Kᵀ) a b.
    have hU_zero : ∀ c, ∫ y, U c y ∂obsG = 0 := by
      intro c
      set Lc : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
        EuclideanSpace.proj (𝕜 := ℝ) c with hLc_def
      set Ltot : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
        Lc.comp (regressionCLM K) with hLtot_def
      have hfun : (fun y : EuclideanSpace ℝ (Fin n) => U c y) = Ltot := by
        funext y
        simp [hU_def, hLtot_def, hLc_def]
      rw [hfun]
      rw [Ltot.integral_comp_id_comm (ProbabilityTheory.IsGaussian.integrable_id
          (μ := obsG))]
      rw [hobsG_def, integral_id_multivariateGaussian_zero S' hObs]
      simp
    have hUU_eval : cov[U a, U b; obsG] = (K * S' * Kᵀ) a b := by
      rw [covariance]
      rw [hU_zero a, hU_zero b]
      simp only [sub_zero]
      have hreg := regressionCLM_covariance_under_prior
        (priorCov := S') (hPrior := hObs) (X := K) a b
      show ∫ y, U a y * U b y ∂obsG = (K * S' * Kᵀ) a b
      simpa [hU_def, hobsG_def] using hreg
    -- Compute cov[E a, E b; postG] = P a b.
    have hEE_eval : cov[E a, E b; postG] = P a b := by
      have := covariance_coord_multivariateGaussian_zero P hPost a b
      simpa [hpostG_def, hE_def] using this
    -- Compute RHS = priorCov a b.
    have hPrior_eval :
        cov[fun θ : EuclideanSpace ℝ (Fin d) =>
              (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) a,
            fun θ : EuclideanSpace ℝ (Fin d) =>
              (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) b; priorMeas]
          = priorCov a b := by
      simpa [hpriorMeas_def] using
        covariance_coord_multivariateGaussian_zero priorCov hPrior.posSemidef a b
    -- Combine matrix identities: K * S' * Kᵀ + P = priorCov.
    have hMatrix : K * S' * Kᵀ + P = priorCov := by
      have hKS := K_S_Ktrans_eq_priorCov_Xtrans_Sinv_X_priorCov
        priorCov hPrior X ν hν
      -- `hKS : K * S' * Kᵀ = priorCov * Xᵀ * S'⁻¹ * (X * priorCov)`.
      show K * S' * Kᵀ + P = priorCov
      have hSchur := Matrix.schurPosteriorCov_eq_schur_complement
        priorCov X (ν ^ 2)
      have hP_unfold : P = priorCov -
          priorCov * Xᵀ * (Matrix.obsCov priorCov X (ν ^ 2))⁻¹ * (X * priorCov) :=
        hSchur
      rw [hP_unfold, hKS]
      abel
    rw [hUE, hEU, hUU, hEE, hUU_eval, hEE_eval, hPrior_eval]
    simp only [add_zero, zero_add]
    exact congrFun (congrFun hMatrix a) b
  -- A symmetry helper used in the (Y,T) and (T,Y) blocks: priorCov is symmetric.
  have hPriorSymm : priorCovᵀ = priorCov := by
    have h := hPrior.isHermitian.eq
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h
  -- Another symmetry helper for `S' = obsCov`.
  have hObsSymm : (Matrix.obsCov priorCov X (ν ^ 2))ᵀ =
      Matrix.obsCov priorCov X (ν ^ 2) := by
    have h := hObsPD.isHermitian.eq
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h
  -- BLOCK (Y, T): both equal `(X * priorCov) i b`.
  have hYT : ∀ i b, cov[Y i, T b; μL] = cov[Y i, T b; μR] := by
    intro i b
    -- LHS via Sub-I4.A pushforward.
    have hL_eq : μL =
        ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
              (Matrix.obsCov priorCov X (ν ^ 2)) hObs).prod
            (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
              (Matrix.schurPosteriorCov priorCov X (ν ^ 2)) hPost)).map
              (posteriorJointMap priorCov X ν) := by
      show ((jointPriorObservation priorCov hPrior.posSemidef X ν).snd ⊗ₘ
              gaussianPosteriorKernel priorCov X ν hPost) = _
      rw [jointPriorObservation_snd_eq_multivariateGaussian
          priorCov hPrior.posSemidef X ν hObs]
      exact gaussianPosteriorKernel_compProd_eq_map_prod priorCov X ν hObs hPost
    have hL_red : cov[Y i, T b; μL] = cov[
        fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) =>
          Y i (posteriorJointMap priorCov X ν p),
        fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) =>
          T b (posteriorJointMap priorCov X ν p);
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
            (Matrix.obsCov priorCov X (ν ^ 2)) hObs).prod
          (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
            (Matrix.schurPosteriorCov priorCov X (ν ^ 2)) hPost)] := by
      rw [hL_eq, covariance_map_fun (by fun_prop) (by fun_prop) (by fun_prop)]
    -- RHS via joint.map Prod.swap.
    have hR_red : cov[Y i, T b; μR] = cov[
        fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) =>
          Y i (Prod.swap p),
        fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) =>
          T b (Prod.swap p);
        jointPriorObservation priorCov hPrior.posSemidef X ν] := by
      show cov[Y i, T b; (jointPriorObservation priorCov hPrior.posSemidef X ν).map
          Prod.swap] = _
      rw [covariance_map_fun (by fun_prop) (by fun_prop) (by fun_prop)]
    rw [hL_red, hR_red]
    -- Goal: cov on (obsG × postG) under posteriorJointMap = cov on joint under swap.
    -- Both reduce to `(X * priorCov) i b`.
    -- ===== LHS computation =====
    set S' : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.obsCov priorCov X (ν ^ 2) with hS'_def
    set P : Matrix (Fin d) (Fin d) ℝ :=
      Matrix.schurPosteriorCov priorCov X (ν ^ 2) with hP_def
    set K : Matrix (Fin d) (Fin n) ℝ :=
      priorCov * Xᵀ * S'⁻¹ with hK_def
    set obsG : Measure (EuclideanSpace ℝ (Fin n)) :=
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S' hObs with hobsG_def
    set postG : Measure (EuclideanSpace ℝ (Fin d)) :=
      multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) P hPost with hpostG_def
    set q : Measure (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)) :=
      obsG.prod postG with hq_def
    -- "Y i" reduces to fst-projection coord.
    set Vp : Fin n → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) → ℝ :=
      fun k p => (WithLp.ofLp (p := 2) (V := Fin n → ℝ) p.1) k with hVp_def
    -- "T b ∘ Φ = Up b + Ep b" (as in hTT).
    set U : Fin d → EuclideanSpace ℝ (Fin n) → ℝ :=
      fun c y => (WithLp.ofLp (p := 2) (V := Fin d → ℝ) (regressionCLM K y)) c
      with hU_def
    set E : Fin d → EuclideanSpace ℝ (Fin d) → ℝ :=
      fun c ε => (WithLp.ofLp (p := 2) (V := Fin d → ℝ) ε) c with hE_def
    set Up : Fin d → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) → ℝ :=
      fun c p => U c p.1 with hUp_def
    set Ep : Fin d → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) → ℝ :=
      fun c p => E c p.2 with hEp_def
    -- Identifications.
    have hY_id : (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) =>
        Y i (posteriorJointMap priorCov X ν p)) = Vp i := by
      funext p
      simp [hY_def, hVp_def, posteriorJointMap_apply]
    have hT_decomp :
        (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d) =>
          T b (posteriorJointMap priorCov X ν p)) = Up b + Ep b := by
      funext p
      simp [hT_def, hUp_def, hEp_def, hU_def, hE_def, hK_def, hS'_def,
        posteriorJointMap_apply, Pi.add_apply]
    -- MemLp facts.
    have hObsG_Prob : IsProbabilityMeasure obsG := by
      show IsProbabilityMeasure
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) S' hObs)
      infer_instance
    have hPostG_Prob : IsProbabilityMeasure postG := by
      show IsProbabilityMeasure
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) P hPost)
      infer_instance
    have hObsId : MemLp (id : EuclideanSpace ℝ (Fin n) → _) 2 obsG :=
      ProbabilityTheory.IsGaussian.memLp_two_id (μ := obsG)
    have hPostId : MemLp (id : EuclideanSpace ℝ (Fin d) → _) 2 postG :=
      ProbabilityTheory.IsGaussian.memLp_two_id (μ := postG)
    have hV_mem : ∀ k, MemLp
        (fun y : EuclideanSpace ℝ (Fin n) =>
          (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) k) 2 obsG := by
      intro k; exact MemLp.eval_piLp hObsId k
    have hU_mem : ∀ c, MemLp (U c) 2 obsG := by
      intro c
      have hReg : MemLp (fun y : EuclideanSpace ℝ (Fin n) => regressionCLM K y) 2 obsG := by
        have := hObsId.continuousLinearMap_comp (regressionCLM K)
        simpa using this
      exact MemLp.eval_piLp hReg c
    have hE_mem : ∀ c, MemLp (E c) 2 postG := by
      intro c; exact MemLp.eval_piLp hPostId c
    have hVp_mem : ∀ k, MemLp (Vp k) 2 q := by
      intro k
      have := (hV_mem k).comp_fst postG
      simpa [hq_def, hVp_def] using this
    have hUp_mem : ∀ c, MemLp (Up c) 2 q := by
      intro c
      have := (hU_mem c).comp_fst postG
      simpa [hq_def, hUp_def, hU_def] using this
    have hEp_mem : ∀ c, MemLp (Ep c) 2 q := by
      intro c
      have := (hE_mem c).comp_snd obsG
      simpa [hq_def, hEp_def, hE_def] using this
    -- Split LHS via bilinearity.
    rw [hY_id, hT_decomp]
    rw [covariance_add_right (hVp_mem i) (hUp_mem b) (hEp_mem b)]
    -- Cross term cov[Vp i, Ep b; q] = 0.
    have hVE : cov[Vp i, Ep b; q] = 0 := by
      have := covariance_fst_snd_prod (μ := obsG) (ν := postG)
        (hV_mem i) (hE_mem b)
      simpa [hq_def, hVp_def, hEp_def] using this
    -- cov[Vp i, Up b; q] = cov[(ofLp ·)_i, U b; obsG].
    have hVU : cov[Vp i, Up b; q] =
        cov[fun y : EuclideanSpace ℝ (Fin n) =>
              (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i,
            U b; obsG] := by
      have hMap : q.map (fun p : EuclideanSpace ℝ (Fin n) ×
            EuclideanSpace ℝ (Fin d) => p.1) = obsG := by
        rw [hq_def]; exact Measure.fst_prod
      have := covariance_map_fun
        (μ := q) (Z := fun p : EuclideanSpace ℝ (Fin n) ×
          EuclideanSpace ℝ (Fin d) => p.1)
        (X := fun y : EuclideanSpace ℝ (Fin n) =>
          (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i)
        (Y := U b)
        (by rw [hMap]; exact (hV_mem i).aestronglyMeasurable)
        (by rw [hMap]; exact (hU_mem b).aestronglyMeasurable)
        measurable_fst.aemeasurable
      rw [hMap] at this
      exact this.symm
    -- Mean-zero properties for cov→integral reduction.
    have hV_zero : ∀ k, ∫ y, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) k ∂obsG = 0 := by
      intro k
      simpa [hobsG_def] using integral_eval_multivariateGaussian_zero S' hObs k
    have hU_zero : ∀ c, ∫ y, U c y ∂obsG = 0 := by
      intro c
      set Lc : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
        EuclideanSpace.proj (𝕜 := ℝ) c with hLc_def
      set Ltot : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
        Lc.comp (regressionCLM K) with hLtot_def
      have hfun : (fun y : EuclideanSpace ℝ (Fin n) => U c y) = Ltot := by
        funext y; simp [hU_def, hLtot_def, hLc_def]
      rw [hfun]
      rw [Ltot.integral_comp_id_comm (ProbabilityTheory.IsGaussian.integrable_id
          (μ := obsG))]
      rw [hobsG_def, integral_id_multivariateGaussian_zero S' hObs]
      simp
    -- Evaluate cov[(ofLp ·)_i, U b; obsG] = (S' * Kᵀ) i b = (X * priorCov) i b.
    have hVU_eval :
        cov[fun y : EuclideanSpace ℝ (Fin n) =>
              (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i,
            U b; obsG] = (X * priorCov) i b := by
      rw [covariance]
      rw [hV_zero i, hU_zero b]
      simp only [sub_zero]
      -- ∫ y (ofLp y)_i * (K *ᵥ ofLp y)_b ∂obsG
      --   = ∑_c K_{b,c} obsCov_{i,c} = (S' * Kᵀ)_{i,b} = (X * priorCov)_{i,b}
      have hExpand : ∀ y : EuclideanSpace ℝ (Fin n),
          (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i * U b y
            = ∑ c, K b c * ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
                  * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) c) := by
        intro y
        show (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
              * (WithLp.ofLp (p := 2) (V := Fin d → ℝ) (regressionCLM K y)) b
            = _
        rw [ofLp_regressionCLM]
        have hKy : (K *ᵥ WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) b
                    = ∑ c, K b c * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) c := by
          simp [Matrix.mulVec, dotProduct]
        rw [hKy, Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intros c _; ring
      have hMemLpCoord : ∀ k, MemLp
          (fun y : EuclideanSpace ℝ (Fin n) =>
            (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) k) 2 obsG := hV_mem
      have hIntCoord : ∀ k l, Integrable
          (fun y : EuclideanSpace ℝ (Fin n) =>
            (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) k
              * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) l) obsG := by
        intros k l
        have := MemLp.integrable_mul (hMemLpCoord k) (hMemLpCoord l)
        simpa [Pi.mul_apply] using this
      have hIntSummand : ∀ c ∈ (Finset.univ : Finset (Fin n)),
          Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
            K b c * ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
              * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) c)) obsG := by
        intros c _; exact (hIntCoord i c).const_mul _
      have hCoord : ∀ k l : Fin n,
          ∫ y, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) k
             * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) l ∂obsG = S' k l := by
        intros k l
        have := covariance_coord_multivariateGaussian_zero S' hObs k l
        rw [covariance] at this
        rw [hV_zero k, hV_zero l] at this
        simpa using this
      have hStep : ∫ y, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i * U b y ∂obsG
          = ∑ c, K b c * S' i c := by
        simp_rw [hExpand]
        rw [integral_finset_sum (Finset.univ : Finset (Fin n)) hIntSummand]
        refine Finset.sum_congr rfl ?_
        intros c _
        rw [integral_const_mul]
        rw [hCoord i c]
      rw [hStep]
      -- (X * priorCov) i b = ∑ c, K b c * S' i c (where K = priorCov*Xᵀ*S'⁻¹).
      -- (S' * Kᵀ) i b = ∑ c, S' i c * (Kᵀ) c b = ∑ c, S' i c * K b c.
      -- And S' * Kᵀ = X * priorCov by matrix bridge.
      have hMul : S' * Kᵀ = X * priorCov := by
        rw [hK_def]
        -- Kᵀ = (S'⁻¹)ᵀ * (Xᵀ)ᵀ * priorCovᵀ = S'⁻¹ * X * priorCov.
        rw [Matrix.transpose_mul, Matrix.transpose_mul,
            Matrix.transpose_transpose, hPriorSymm]
        have hSinvT : (S'⁻¹)ᵀ = S'⁻¹ := by
          rw [Matrix.transpose_nonsing_inv]
          show (S'ᵀ)⁻¹ = S'⁻¹
          rw [show S'ᵀ = S' from hObsSymm]
        rw [hSinvT]
        -- Goal: S' * (S'⁻¹ * X * priorCov) = X * priorCov.
        have hSdet : IsUnit S'.det :=
          (Matrix.isUnit_iff_isUnit_det _).1 hObsPD.isUnit
        rw [← Matrix.mul_assoc S' S'⁻¹ (X * priorCov),
            Matrix.mul_nonsing_inv S' hSdet, Matrix.one_mul]
      have hExpandRHS : (X * priorCov) i b = ∑ c, K b c * S' i c := by
        have hentry : (X * priorCov) i b = (S' * Kᵀ) i b := by
          rw [← hMul]
        rw [hentry, Matrix.mul_apply]
        refine Finset.sum_congr rfl ?_
        intros c _
        rw [Matrix.transpose_apply]; ring
      rw [hExpandRHS]
    -- ===== RHS computation: use jointPriorObservation_cross_covariance_eval. =====
    have hR_eval : cov[
        fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) =>
          Y i (Prod.swap p),
        fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) =>
          T b (Prod.swap p);
        jointPriorObservation priorCov hPrior.posSemidef X ν]
        = (X * priorCov) i b := by
      -- After swap: Y i (Prod.swap p) = (ofLp p.2) i; T b (Prod.swap p) = (ofLp p.1) b.
      have hYsw : (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) =>
          Y i (Prod.swap p)) =
          (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) =>
            (WithLp.ofLp (p := 2) (V := Fin n → ℝ) p.2) i) := by
        funext p; rfl
      have hTsw : (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) =>
          T b (Prod.swap p)) =
          (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) =>
            (WithLp.ofLp (p := 2) (V := Fin d → ℝ) p.1) b) := by
        funext p; rfl
      rw [hYsw, hTsw]
      rw [covariance]
      -- Means under joint are zero.
      have hM1 : (jointPriorObservation priorCov hPrior.posSemidef X ν)[
          fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) =>
            (WithLp.ofLp (p := 2) (V := Fin n → ℝ) p.2) i] = 0 := by
        show ∫ p, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) p.2) i
              ∂(jointPriorObservation priorCov hPrior.posSemidef X ν) = 0
        rw [← MeasureTheory.integral_map measurable_snd.aemeasurable
            (by fun_prop : AEStronglyMeasurable
              (fun y : EuclideanSpace ℝ (Fin n) =>
                (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i)
              ((jointPriorObservation priorCov hPrior.posSemidef X ν).map Prod.snd))]
        show ∫ y, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
              ∂(jointPriorObservation priorCov hPrior.posSemidef X ν).snd = 0
        exact jointPriorObservation_snd_integral_eval_coord
          priorCov hPrior.posSemidef X ν i
      have hM2 : (jointPriorObservation priorCov hPrior.posSemidef X ν)[
          fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) =>
            (WithLp.ofLp (p := 2) (V := Fin d → ℝ) p.1) b] = 0 := by
        show ∫ p, (WithLp.ofLp (p := 2) (V := Fin d → ℝ) p.1) b
              ∂(jointPriorObservation priorCov hPrior.posSemidef X ν) = 0
        rw [← MeasureTheory.integral_map measurable_fst.aemeasurable
            (by fun_prop : AEStronglyMeasurable
              (fun θ : EuclideanSpace ℝ (Fin d) =>
                (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) b)
              ((jointPriorObservation priorCov hPrior.posSemidef X ν).map Prod.fst))]
        show ∫ θ, (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) b
              ∂(jointPriorObservation priorCov hPrior.posSemidef X ν).fst = 0
        exact jointPriorObservation_fst_integral_eval_coord
          priorCov hPrior.posSemidef X ν b
      rw [hM1, hM2]
      simp only [sub_zero]
      have hcross := jointPriorObservation_cross_covariance_eval
        priorCov hPrior.posSemidef X ν b i
      -- hcross: ∫ p, (ofLp p.1)_b * (ofLp p.2)_i ∂joint = (priorCov * Xᵀ) b i.
      -- We need: ∫ p, (ofLp p.2)_i * (ofLp p.1)_b ∂joint = (X * priorCov) i b.
      have hcomm : ∫ p, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) p.2) i
                     * (WithLp.ofLp (p := 2) (V := Fin d → ℝ) p.1) b
                     ∂(jointPriorObservation priorCov hPrior.posSemidef X ν)
              = ∫ p, (WithLp.ofLp (p := 2) (V := Fin d → ℝ) p.1) b
                     * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) p.2) i
                     ∂(jointPriorObservation priorCov hPrior.posSemidef X ν) := by
        refine integral_congr_ae ?_
        filter_upwards with p
        ring
      rw [hcomm, hcross]
      -- (priorCov * Xᵀ) b i = (X * priorCov) i b via priorCov symmetry.
      rw [Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl ?_
      intros c _
      rw [Matrix.transpose_apply]
      have : priorCov b c = priorCov c b := by
        have h := congrFun (congrFun hPriorSymm c) b
        rw [Matrix.transpose_apply] at h
        exact h
      rw [this]; ring
    rw [hVE]
    simp only [add_zero]
    rw [hVU, hVU_eval, hR_eval]
  have hTY : ∀ a j, cov[T a, Y j; μL] = cov[T a, Y j; μR] := by
    intro a j
    rw [covariance_comm, covariance_comm (μ := μR)]
    exact hYT j a
  simp_rw [hYY, hYT, hTY, hTT]

end ProbabilityTheory
