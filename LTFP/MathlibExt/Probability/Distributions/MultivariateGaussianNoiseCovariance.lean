/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.Distributions.MultivariateGaussianMeasure
import LTFP.MathlibExt.Probability.Distributions.GaussianObservationKernelMean
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Noise covariance coordinate identity

For the isotropic noise component `multivariateGaussian 0 (ν² · I) _`, the
coordinate-`(i,j)` covariance equals `(ν² · I)_{i,j}`. Sub-step toward
the B4 N2 carrier (full `joint.snd` covariance).
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

theorem covariance_noise_multivariateGaussian
    {n : ℕ} (ν : ℝ) (i j : Fin n) :
    ∫ y, ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
           - (WithLp.ofLp (p := 2) (V := Fin n → ℝ)
              (0 : EuclideanSpace ℝ (Fin n))) i)
         * ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j
           - (WithLp.ofLp (p := 2) (V := Fin n → ℝ)
              (0 : EuclideanSpace ℝ (Fin n))) j)
       ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin n)) (ν ^ 2 • 1)
          (posSemidef_sq_smul_one (n := n) ν))
      = (ν ^ 2 • 1 : Matrix (Fin n) (Fin n) ℝ) i j := by
  simpa using
    (covariance_multivariateGaussian
      (m := (0 : EuclideanSpace ℝ (Fin n)))
      (S := (ν ^ 2 • 1 : Matrix (Fin n) (Fin n) ℝ))
      (hS := posSemidef_sq_smul_one (n := n) ν) i j)

theorem gaussianObservationKernel_covariance_eval
    {d n : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (i j : Fin n) :
    ∫ y, ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i -
          (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) i)
       * ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j -
          (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) j)
       ∂(gaussianObservationKernel X ν θ)
      = (ν ^ 2 • 1 : Matrix (Fin n) (Fin n) ℝ) i j := by
  rw [gaussianObservationKernel_apply]
  let μ0 := multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
      ((ν ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ))
      (posSemidef_sq_smul_one (n := n) ν)
  have hmeas : Measurable (fun y : EuclideanSpace ℝ (Fin n) => regressionCLM X θ + y) := by
    fun_prop
  rw [integral_map hmeas.aemeasurable]
  · simpa [μ0, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      covariance_noise_multivariateGaussian (n := n) ν i j
  · fun_prop

/-- **Uncentered second moment of the Gaussian observation kernel.**
For the Gaussian observation kernel `Y | θ ~ N(X θ, ν² · I)`, the
coordinate-`(i,j)` uncentered second moment of `y` equals the product
of the regression means at coordinates `i, j` plus the isotropic noise
covariance entry `(ν² · I)_{i,j}`. Sub-step toward the full
`joint.snd` covariance for the B4 N2 carrier.

Proof: expand `y = (y - μ) + μ` where `μ = regressionCLM X θ`, then
distribute the product to get the four-term identity
`y_i · y_j = (y - μ)_i · (y - μ)_j + (y - μ)_i · μ_j +
            μ_i · (y - μ)_j + μ_i · μ_j`.
The two cross terms vanish since the kernel has mean `μ`
(`gaussianObservationKernel_integral_eval`). The centered term
integrates to `(ν² · I)_{i,j}` by
`gaussianObservationKernel_covariance_eval`. The constant term
integrates to itself. -/
theorem gaussianObservationKernel_second_moment_eval
    {d n : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) (i j : Fin n) :
    ∫ y, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
       * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j
       ∂(gaussianObservationKernel X ν θ)
      = (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) i
       * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) j
       + (ν ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) i j := by
  classical
  -- Abbreviation for the regression mean (as a vector in EuclideanSpace).
  set μ : EuclideanSpace ℝ (Fin n) := regressionCLM X θ with hμdef
  set κ : Measure (EuclideanSpace ℝ (Fin n)) := gaussianObservationKernel X ν θ with hκdef
  -- The kernel is Gaussian, hence the identity function is L² and each
  -- coordinate is L² as well.
  have hκG : IsGaussian κ := by
    show IsGaussian (gaussianObservationKernel X ν θ); infer_instance
  have hκP : IsProbabilityMeasure κ := by
    show IsProbabilityMeasure (gaussianObservationKernel X ν θ); infer_instance
  have hMemLpId : MemLp (id : EuclideanSpace ℝ (Fin n) → _) 2 κ :=
    ProbabilityTheory.IsGaussian.memLp_two_id (μ := κ)
  -- Per-coordinate L²: each coordinate of `y` is in MemLp 2.
  have hMemLpCoord : ∀ k : Fin n,
      MemLp (fun y : EuclideanSpace ℝ (Fin n) =>
        (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) k) 2 κ := by
    intro k
    exact MemLp.eval_piLp hMemLpId k
  -- And per-coordinate L² for the centered version `y - μ`.
  have hMemLpCenter : ∀ k : Fin n,
      MemLp (fun y : EuclideanSpace ℝ (Fin n) =>
        (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) k
          - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) k) 2 κ := by
    intro k
    have hConst : MemLp (fun _ : EuclideanSpace ℝ (Fin n) =>
        (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) k) 2 κ :=
      memLp_const _
    exact (hMemLpCoord k).sub hConst
  -- The constant `1 ≤ 2` in `ℝ≥0∞` (needed for MemLp.integrable).
  have h12 : (1 : ENNReal) ≤ 2 := by norm_num
  -- Coordinates are integrable.
  have hIntCoord : ∀ k : Fin n,
      Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
        (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) k) κ := fun k =>
    (hMemLpCoord k).integrable h12
  have hIntCenter : ∀ k : Fin n,
      Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
        (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) k
          - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) k) κ := fun k =>
    (hMemLpCenter k).integrable h12
  -- Algebraic identity: y_i · y_j = (y - μ)_i · (y - μ)_j + μ_i · (y - μ)_j
  --                                + μ_j · (y - μ)_i + μ_i · μ_j.
  have hAlg : ∀ y : EuclideanSpace ℝ (Fin n),
      (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
        * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j
        = ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
              - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i)
            * ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j
              - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j)
          + (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i
            * ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j
              - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j)
          + (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j
            * ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
              - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i)
          + (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i
            * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j := by
    intro y; ring
  -- Integrability of the centered cross-product (i,j).
  have hIntCenterIJ : Integrable
      (fun y : EuclideanSpace ℝ (Fin n) =>
        ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
            - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i)
          * ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j
            - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j)) κ := by
    have := MemLp.integrable_mul (hMemLpCenter i) (hMemLpCenter j)
    simpa [Pi.mul_apply] using this
  -- Integrability of μ_i * (y - μ)_j.
  have hIntCross1 : Integrable
      (fun y : EuclideanSpace ℝ (Fin n) =>
        (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i
          * ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j
              - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j)) κ := by
    exact (hIntCenter j).const_mul _
  -- Integrability of μ_j * (y - μ)_i.
  have hIntCross2 : Integrable
      (fun y : EuclideanSpace ℝ (Fin n) =>
        (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j
          * ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
              - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i)) κ := by
    exact (hIntCenter i).const_mul _
  -- Integrability of the constant term.
  have hIntConst : Integrable
      (fun _ : EuclideanSpace ℝ (Fin n) =>
        (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i
          * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j) κ :=
    integrable_const _
  -- Integrability of sums.
  have hIntSum1 : Integrable
      (fun y : EuclideanSpace ℝ (Fin n) =>
        ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
            - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i)
          * ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j
            - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j)
        + (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i
          * ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j
            - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j)) κ :=
    hIntCenterIJ.add hIntCross1
  have hIntSum2 : Integrable
      (fun y : EuclideanSpace ℝ (Fin n) =>
        ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
            - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i)
          * ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j
            - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j)
        + (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i
          * ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j
            - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j)
        + (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j
          * ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
            - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i)) κ :=
    hIntSum1.add hIntCross2
  -- Apply the algebraic expansion and integrate term by term.
  calc
    ∫ y, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
       * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j ∂κ
        = ∫ y,
            (((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
                - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i)
              * ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j
                - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j)
            + (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i
              * ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j
                - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j)
            + (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j
              * ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
                - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i)
            + (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i
              * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j) ∂κ := by
              refine integral_congr_ae (.of_forall ?_); intro y
              exact hAlg y
    _ = (∫ y,
            ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
                - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i)
              * ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j
                - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j)
            + (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i
              * ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j
                - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j)
            + (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j
              * ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
                - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i) ∂κ)
          + ∫ _ : EuclideanSpace ℝ (Fin n),
              (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i
                * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j ∂κ :=
              integral_add hIntSum2 hIntConst
    _ = ((∫ y,
            ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
                - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i)
              * ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j
                - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j)
            + (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i
              * ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j
                - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j) ∂κ)
          + ∫ y, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j
              * ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
                - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i) ∂κ)
          + ∫ _ : EuclideanSpace ℝ (Fin n),
              (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i
                * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j ∂κ := by
              rw [integral_add hIntSum1 hIntCross2]
    _ = (((∫ y,
            ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
                - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i)
              * ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j
                - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j) ∂κ)
          + ∫ y, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i
              * ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j
                - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j) ∂κ)
          + ∫ y, (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j
              * ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
                - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i) ∂κ)
          + ∫ _ : EuclideanSpace ℝ (Fin n),
              (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i
                * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j ∂κ := by
              rw [integral_add hIntCenterIJ hIntCross1]
    _ = (((ν ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) i j
          + (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i * 0)
          + (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j * 0)
          + (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i
            * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j := by
              -- Centered term: covariance identity.
              rw [show (∫ y,
                  ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
                      - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i)
                    * ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j
                      - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j) ∂κ)
                  = (ν ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) i j from
                (gaussianObservationKernel_covariance_eval X ν θ i j)]
              -- Cross term 1: μ_i * (y - μ)_j → μ_i * 0 = 0.
              rw [integral_const_mul]
              -- Need ∫ (y - μ)_j ∂κ = 0.
              have hCenterJ_zero : ∫ y,
                  ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) j
                    - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) j) ∂κ = 0 := by
                rw [integral_sub (hIntCoord j) (integrable_const _)]
                rw [_root_.gaussianObservationKernel_integral_eval X ν θ j,
                    integral_const, hμdef]
                simp
              rw [hCenterJ_zero]
              -- Cross term 2: μ_j * (y - μ)_i → μ_j * 0 = 0.
              rw [integral_const_mul]
              have hCenterI_zero : ∫ y,
                  ((WithLp.ofLp (p := 2) (V := Fin n → ℝ) y) i
                    - (WithLp.ofLp (p := 2) (V := Fin n → ℝ) μ) i) ∂κ = 0 := by
                rw [integral_sub (hIntCoord i) (integrable_const _)]
                rw [_root_.gaussianObservationKernel_integral_eval X ν θ i,
                    integral_const, hμdef]
                simp
              rw [hCenterI_zero]
              -- Constant term integral: κ is a probability measure so
              -- `κ.real Set.univ = 1`.
              rw [integral_const]
              rw [probReal_univ]
              simp
    _ = (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) i
        * (WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)) j
        + (ν ^ 2 • (1 : Matrix (Fin n) (Fin n) ℝ)) i j := by
              simp [μ]; ring

end ProbabilityTheory
