/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.Distributions.JointPriorObservationSnd
import LTFP.MathlibExt.Probability.Distributions.GaussianObservationKernelMean
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-!
# Coordinate mean of the joint prior-observation second marginal

For the joint Gaussian prior-observation measure
`jointPriorObservation priorCov hPrior X ν` (defined in
`MultivariateGaussianMeasure.lean`), the integral of each coordinate of
the observation component is zero, because the prior is zero-mean
Gaussian and the observation kernel is a linear-in-`θ` Gaussian shift.

This is the B4 Node 2 carrier-progress milestone toward the conjugate
Gaussian posterior-mean identity: once we know each observation
coordinate has zero unconditional mean, the centered second-moment
structure of the joint measure (the prior-times-`X`-times-noise
calculation) becomes well-typed.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

/-- The second marginal of the joint prior-observation measure is Gaussian.

This is the pushforward of the Gaussian joint measure
`jointPriorObservation priorCov hPrior X ν` (whose Gaussianity is
provided by `instIsGaussianJointPriorObservation`) under the continuous
linear projection `ContinuousLinearMap.snd`. Pushforwards of Gaussian
measures under continuous linear maps are Gaussian (`isGaussian_map`). -/
instance jointPriorObservation_snd_isGaussian
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ) (hPrior : priorCov.PosSemidef)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) :
    IsGaussian (jointPriorObservation priorCov hPrior X ν).snd := by
  show IsGaussian ((jointPriorObservation priorCov hPrior X ν).map Prod.snd)
  exact isGaussian_map
    (ContinuousLinearMap.snd ℝ
      (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin n)))

/-- Per-coordinate mean of the zero-mean multivariate Gaussian prior:
`∫ θ, θ_i ∂prior = 0`. This is `integral_eval_multivariateGaussian`
specialised to mean zero, restated without the `ofLp 0` simp rewrite. -/
lemma integral_eval_multivariateGaussian_zero
    {d : ℕ} (priorCov : Matrix (Fin d) (Fin d) ℝ) (hPrior : priorCov.PosSemidef)
    (i : Fin d) :
    ∫ θ, (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) i
      ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) priorCov hPrior) = 0 := by
  have h := integral_eval_multivariateGaussian
    (m := (0 : EuclideanSpace ℝ (Fin d))) (S := priorCov) (hS := hPrior) i
  simpa using h

/-- The vector-valued mean of the zero-mean multivariate Gaussian prior:
`∫ θ, θ ∂prior = 0`. Derived from the per-coordinate identity via
`MeasureTheory.eval_integral_piLp`. -/
lemma integral_id_multivariateGaussian_zero
    {d : ℕ} (priorCov : Matrix (Fin d) (Fin d) ℝ) (hPrior : priorCov.PosSemidef) :
    ∫ θ, θ ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) priorCov hPrior)
      = (0 : EuclideanSpace ℝ (Fin d)) := by
  classical
  set μ : Measure (EuclideanSpace ℝ (Fin d)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) priorCov hPrior with hμ
  -- `μ` is Gaussian, so `id` is integrable, and so are all coordinates.
  have hIntId : Integrable (fun θ : EuclideanSpace ℝ (Fin d) => θ) μ :=
    ProbabilityTheory.IsGaussian.integrable_fun_id (μ := μ)
  have hIntCoord : ∀ i, Integrable
      (fun θ : EuclideanSpace ℝ (Fin d) =>
        (θ : EuclideanSpace ℝ (Fin d)) i) μ := by
    intro i
    have := hIntId
    -- Use `Integrable.eval_piLp` to descend to coordinates.
    exact (MeasureTheory.integrable_piLp_iff (q := 2)
        (E := fun _ : Fin d => ℝ) (f := fun θ => θ)).mp this i
  -- Show equality coordinate-by-coordinate using `PiLp.ext`.
  refine PiLp.ext (fun i => ?_)
  rw [MeasureTheory.eval_integral_piLp (q := 2) (E := fun _ : Fin d => ℝ)
      (f := fun θ : EuclideanSpace ℝ (Fin d) => θ) hIntCoord i]
  -- Now: `∫ θ, θ i ∂μ = (0 : EuclideanSpace ℝ (Fin d)) i`.
  -- The LHS equals `∫ θ, (ofLp θ) i ∂μ` (since `θ i = (ofLp θ) i` definitionally).
  -- The RHS equals `0`.
  have h0 : (0 : EuclideanSpace ℝ (Fin d)) i = (0 : ℝ) := by simp
  rw [h0]
  exact integral_eval_multivariateGaussian_zero (d := d) priorCov hPrior i

/-- The coordinate-`i` integral of the second-marginal observation
component of the joint prior-observation measure is zero.

Proof outline:
1. Rewrite the second marginal as `gaussianObservationKernel X ν ∘ₘ prior`
   via `jointPriorObservation_snd`.
2. Convert back to the second marginal of `prior ⊗ₘ κ` (since
   `(prior ⊗ₘ κ).snd = κ ∘ₘ prior`) and use `integral_map` with
   `measurable_snd` to express the integral over the joint measure.
3. Apply `Measure.integral_compProd` to factor as
   `∫ θ, ∫ y, y_i ∂(κ θ) ∂prior`.
4. Use `gaussianObservationKernel_integral_eval` on the inner integral,
   reducing to `∫ θ, (regressionCLM X θ)_i ∂prior`.
5. Pull the continuous linear coordinate map through the integral via
   `ContinuousLinearMap.integral_comp_comm`, then use
   `integral_id_multivariateGaussian_zero` to conclude `0`. -/
theorem jointPriorObservation_snd_integral_eval_coord
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ) (hPrior : priorCov.PosSemidef)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) (i : Fin n) :
    ∫ y, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
      ∂(jointPriorObservation priorCov hPrior X ν).snd
      = 0 := by
  classical
  set prior : Measure (EuclideanSpace ℝ (Fin d)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) priorCov hPrior with hprior
  set κ : Kernel (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin n)) :=
    gaussianObservationKernel X ν with hκ
  -- The continuous linear coordinate map (used at step 5).
  set Lcoord : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ :=
    EuclideanSpace.proj (𝕜 := ℝ) (ι := Fin n) i with hLcoord
  -- Step 1: rewrite the second marginal.
  have hSnd :
      (jointPriorObservation priorCov hPrior X ν).snd = κ ∘ₘ prior := by
    show (jointPriorObservation priorCov hPrior X ν).snd =
      gaussianObservationKernel X ν ∘ₘ
        multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) priorCov hPrior
    exact jointPriorObservation_snd priorCov hPrior X ν
  rw [hSnd]
  -- Step 2: express the integral over `κ ∘ₘ prior` as integral over `prior ⊗ₘ κ`
  -- composed with `snd`.
  have hSndCompProd : κ ∘ₘ prior = (prior ⊗ₘ κ).snd :=
    (Measure.snd_compProd prior κ).symm
  rw [hSndCompProd]
  rw [Measure.snd]
  rw [MeasureTheory.integral_map measurable_snd.aemeasurable
      (by fun_prop : AEStronglyMeasurable
        (fun y => (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i)
        ((prior ⊗ₘ κ).map Prod.snd))]
  -- Goal now: `∫ p, (ofLp p.2) i ∂(prior ⊗ₘ κ) = 0`.
  -- Step 3: factor through `integral_compProd`. Need integrability.
  have hIntegrable :
      Integrable (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) =>
        (WithLp.ofLp (p := 2) (V := Fin n → ℝ) p.2) i)
        (prior ⊗ₘ κ) := by
    -- The joint measure is Gaussian, hence `id` is integrable.
    have hJointGauss : IsGaussian (prior ⊗ₘ κ) := by
      show IsGaussian (jointPriorObservation priorCov hPrior X ν)
      infer_instance
    have hIntJoint : Integrable
        (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) => p)
        (prior ⊗ₘ κ) :=
      ProbabilityTheory.IsGaussian.integrable_fun_id (μ := prior ⊗ₘ κ)
    -- Apply `Lcoord ∘ snd` continuous linear map composition.
    have hAux : Integrable
        (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) => Lcoord p.2)
        (prior ⊗ₘ κ) := by
      have hSndCLM : Integrable
          (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) => p.2)
          (prior ⊗ₘ κ) :=
        (ContinuousLinearMap.integrable_comp
          (ContinuousLinearMap.snd ℝ
            (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin n))) hIntJoint)
      exact ContinuousLinearMap.integrable_comp Lcoord hSndCLM
    simpa [Lcoord, EuclideanSpace.proj, PiLp.proj_apply] using hAux
  rw [MeasureTheory.Measure.integral_compProd hIntegrable]
  -- Goal: `∫ θ, ∫ y, (ofLp y) i ∂(κ θ) ∂prior = 0`.
  -- Step 4: apply gaussianObservationKernel_integral_eval.
  have hInner : ∀ θ : EuclideanSpace ℝ (Fin d),
      ∫ y, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i ∂(κ θ)
        = (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) i := by
    intro θ
    show ∫ y, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
            ∂(gaussianObservationKernel X ν θ) = _
    exact gaussianObservationKernel_integral_eval X ν θ i
  simp_rw [hInner]
  -- Goal: `∫ θ, (ofLp (regressionCLM X θ)) i ∂prior = 0`.
  -- Step 5: write integrand as `Lcoord (regressionCLM X θ)`, then pull through.
  have hAsLin : ∀ θ : EuclideanSpace ℝ (Fin d),
      (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) i
        = Lcoord (regressionCLM X θ) := by
    intro θ
    simp [Lcoord, PiLp.proj_apply]
  simp_rw [hAsLin]
  -- Combine the two continuous linear maps into one: `Lcoord ∘L regressionCLM X`.
  set Ltot : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
    Lcoord.comp (regressionCLM X) with hLtot
  have hLtotApp : ∀ θ, Ltot θ = Lcoord (regressionCLM X θ) := fun _ => rfl
  simp_rw [← hLtotApp]
  -- Pull `Ltot` through the integral.
  have hIntPrior : Integrable (fun θ : EuclideanSpace ℝ (Fin d) => θ) prior :=
    ProbabilityTheory.IsGaussian.integrable_fun_id (μ := prior)
  rw [Ltot.integral_comp_comm hIntPrior]
  -- Goal: `Ltot (∫ θ, θ ∂prior) = 0`.
  rw [integral_id_multivariateGaussian_zero priorCov hPrior]
  -- `Ltot 0 = 0`.
  exact map_zero Ltot

/-- **Vector form of the joint prior-observation second-marginal mean.**
The integral of `y` against the second marginal of the joint Gaussian
prior-observation measure is zero: `∫ y, y ∂joint.snd = 0`.

Aggregates the coordinate-wise identity
`jointPriorObservation_snd_integral_eval_coord` over all `i : Fin n`,
using `PiLp.ext` and `MeasureTheory.eval_integral_piLp` to reduce
vector equality to per-coordinate equality. Integrability of the
identity function against `joint.snd` is supplied by Mathlib's
`IsGaussian.integrable_fun_id`, since `joint.snd` is the pushforward
of the Gaussian joint measure under the continuous linear `Prod.snd`,
hence Gaussian (`isGaussian_map` instance). -/
theorem jointPriorObservation_snd_integral_vector
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ) (hPrior : priorCov.PosSemidef)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) :
    ∫ y, y ∂(jointPriorObservation priorCov hPrior X ν).snd
      = (0 : EuclideanSpace ℝ (Fin n)) := by
  classical
  set μ : Measure (EuclideanSpace ℝ (Fin n)) :=
    (jointPriorObservation priorCov hPrior X ν).snd with hμ
  -- `μ` is Gaussian: it is the pushforward of the Gaussian joint measure
  -- under the continuous linear `Prod.snd`, which preserves Gaussianity
  -- via `isGaussian_map`.
  have hJointG : IsGaussian (jointPriorObservation priorCov hPrior X ν) :=
    inferInstance
  have hμG : IsGaussian μ := by
    show IsGaussian ((jointPriorObservation priorCov hPrior X ν).map Prod.snd)
    exact isGaussian_map
      (ContinuousLinearMap.snd ℝ (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin n)))
  -- Identity is integrable against `μ`, hence so are all coordinates.
  have hIntId : Integrable (fun y : EuclideanSpace ℝ (Fin n) => y) μ :=
    ProbabilityTheory.IsGaussian.integrable_fun_id (μ := μ)
  have hIntCoord : ∀ i, Integrable
      (fun y : EuclideanSpace ℝ (Fin n) =>
        (y : EuclideanSpace ℝ (Fin n)) i) μ := by
    intro i
    exact (MeasureTheory.integrable_piLp_iff (q := 2)
        (E := fun _ : Fin n => ℝ) (f := fun y => y)).mp hIntId i
  -- Reduce vector equality to coordinate-wise equality via `PiLp.ext`.
  refine PiLp.ext (fun i => ?_)
  rw [MeasureTheory.eval_integral_piLp (q := 2) (E := fun _ : Fin n => ℝ)
      (f := fun y : EuclideanSpace ℝ (Fin n) => y) hIntCoord i]
  -- Goal: `∫ y, y i ∂μ = (0 : EuclideanSpace ℝ (Fin n)) i`.
  -- The RHS is `0`.
  have h0 : (0 : EuclideanSpace ℝ (Fin n)) i = (0 : ℝ) := by simp
  rw [h0]
  -- And `y i = (WithLp.ofLp y) i` definitionally, so the scalar lemma applies.
  show ∫ y, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
          ∂(jointPriorObservation priorCov hPrior X ν).snd
        = 0
  exact jointPriorObservation_snd_integral_eval_coord priorCov hPrior X ν i

/-- **Vector form of the joint prior-observation first-marginal mean.**
The integral of `θ` against the first marginal of the joint Gaussian
prior-observation measure is zero: `∫ θ, θ ∂joint.fst = 0`.

Follows by rewriting `joint.fst` as the zero-mean multivariate Gaussian
prior (via `jointPriorObservation_fst`) and applying
`integral_id_multivariateGaussian_zero`. -/
theorem jointPriorObservation_fst_integral_vector
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ) (hPrior : priorCov.PosSemidef)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) :
    ∫ θ, θ ∂(jointPriorObservation priorCov hPrior X ν).fst
      = (0 : EuclideanSpace ℝ (Fin d)) := by
  rw [jointPriorObservation_fst]
  exact integral_id_multivariateGaussian_zero priorCov hPrior

/-- **Coordinate form of the joint prior-observation first-marginal mean.**
The integral of the `i`-th coordinate of `θ` against the first marginal
of the joint Gaussian prior-observation measure is zero:
`∫ θ, θ_i ∂joint.fst = 0`.

Follows by rewriting `joint.fst` as the zero-mean multivariate Gaussian
prior (via `jointPriorObservation_fst`) and applying
`integral_eval_multivariateGaussian_zero`. -/
theorem jointPriorObservation_fst_integral_eval_coord
    {d n : ℕ}
    (priorCov : Matrix (Fin d) (Fin d) ℝ) (hPrior : priorCov.PosSemidef)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) (i : Fin d) :
    ∫ θ, (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ) i
      ∂(jointPriorObservation priorCov hPrior X ν).fst
      = 0 := by
  rw [jointPriorObservation_fst]
  exact integral_eval_multivariateGaussian_zero (d := d) priorCov hPrior i

end ProbabilityTheory
