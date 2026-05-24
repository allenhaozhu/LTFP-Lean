/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Covariance bilinear form on a product of two Euclidean spaces

Companion to `Mathlib.Probability.Moments.CovarianceBilin.covarianceBilin_apply_pi`,
extending the single-Pi case to a product of two Euclidean spaces with the
`WithLp 2` inner-product structure.

## Main result

* `covarianceBilin_apply_prod_pi`: for a measure `μ` on `Ω`, families
  `Y : Fin n → Ω → ℝ` and `T : Fin d → Ω → ℝ` of square-integrable random
  variables, and vectors `u v : WithLp 2 (EuclideanSpace ℝ (Fin n) ×
  EuclideanSpace ℝ (Fin d))`, the covariance bilinear form of the pushforward
  measure under `fun ω ↦ WithLp.toLp 2 (WithLp.toLp 2 (Y · ω),
  WithLp.toLp 2 (T · ω))` expands into a 4-block double sum over
  `cov[Y i, Y j]`, `cov[Y i, T b]`, `cov[T a, Y j]`, and `cov[T a, T b]`.

This is an infrastructure lemma for the B4 N2 joint prior-observation
covariance characterization.
-/

open MeasureTheory ProbabilityTheory WithLp InnerProductSpace
open scoped Matrix RealInnerProductSpace ENNReal

namespace ProbabilityTheory

/-- **Covariance bilinear form on a product of two Pi spaces.**
For square-integrable families `Y : Fin n → Ω → ℝ` and `T : Fin d → Ω → ℝ`,
the covariance bilinear form of the joint pushforward decomposes into a
4-block double sum over the pairwise scalar covariances. -/
theorem covarianceBilin_apply_prod_pi
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {n d : ℕ} {Y : Fin n → Ω → ℝ} {T : Fin d → Ω → ℝ}
    (hY : ∀ i, MemLp (Y i) 2 μ) (hT : ∀ a, MemLp (T a) 2 μ)
    (u v : WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d))) :
    covarianceBilin
        (μ.map (fun ω =>
          (WithLp.toLp 2
            ((WithLp.toLp 2 (Y · ω), WithLp.toLp 2 (T · ω)) :
              EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d))))) u v =
      (∑ i, ∑ j, u.fst i * v.fst j * cov[Y i, Y j; μ]) +
      (∑ i, ∑ b, u.fst i * v.snd b * cov[Y i, T b; μ]) +
      (∑ a, ∑ j, u.snd a * v.fst j * cov[T a, Y j; μ]) +
      (∑ a, ∑ b, u.snd a * v.snd b * cov[T a, T b; μ]) := by
  classical
  -- Coordinate-wise AE-measurability.
  have hY_am : ∀ i, AEMeasurable (Y i) μ := fun i => (hY i).aemeasurable
  have hT_am : ∀ a, AEMeasurable (T a) μ := fun a => (hT a).aemeasurable
  -- The mapping under which we push forward.
  set F : Ω → WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)) :=
    fun ω => WithLp.toLp 2
      ((WithLp.toLp 2 (Y · ω), WithLp.toLp 2 (T · ω)) :
        EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)) with hF
  -- AE-measurability of `F` from coordinate-wise measurability.
  have hF_am : AEMeasurable F μ := by
    refine (WithLp.measurable_toLp _ _).comp_aemeasurable ?_
    have h1 : AEMeasurable (fun ω => (WithLp.toLp 2 (Y · ω) :
        EuclideanSpace ℝ (Fin n))) μ :=
      (WithLp.measurable_toLp _ _).comp_aemeasurable
        (aemeasurable_pi_iff.mpr hY_am)
    have h2 : AEMeasurable (fun ω => (WithLp.toLp 2 (T · ω) :
        EuclideanSpace ℝ (Fin d))) μ :=
      (WithLp.measurable_toLp _ _).comp_aemeasurable
        (aemeasurable_pi_iff.mpr hT_am)
    exact h1.prodMk h2
  -- `MemLp` for each Euclidean block of `F`.
  have hFst_memLp :
      MemLp (fun ω => (F ω).fst) 2 μ := by
    refine MemLp.of_eval_piLp (p := 2) (q := 2) (E := fun _ : Fin n => ℝ)
      (f := fun ω => (F ω).fst) ?_
    intro i
    -- `(F ω).fst i = Y i ω`.
    simpa [hF] using hY i
  have hSnd_memLp :
      MemLp (fun ω => (F ω).snd) 2 μ := by
    refine MemLp.of_eval_piLp (p := 2) (q := 2) (E := fun _ : Fin d => ℝ)
      (f := fun ω => (F ω).snd) ?_
    intro a
    simpa [hF] using hT a
  have hF_memLp : MemLp F 2 μ :=
    MemLp.of_fst_of_snd_prodLp ⟨hFst_memLp, hSnd_memLp⟩
  -- Pass to `μ.map F`.
  have hMapMemLp :
      MemLp (id : WithLp 2 (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin d)) → _) 2
        (μ.map F) :=
    (memLp_map_measure_iff aestronglyMeasurable_id hF_am).2 hF_memLp
  -- Step 1: covariance bilinear form ↦ scalar covariance, then push through `map`.
  rw [covarianceBilin_apply_eq_cov hMapMemLp,
    covariance_map_fun (Measurable.aestronglyMeasurable (by fun_prop))
      (Measurable.aestronglyMeasurable (by fun_prop)) hF_am]
  -- Step 2: expand each inner product `⟪u, F ω⟫` (resp. `⟪v, F ω⟫`) as a
  -- sum of two real finite sums (one per Euclidean block).
  set Yu : Fin n → Ω → ℝ := fun i ω => u.fst i * Y i ω with hYu
  set Tu : Fin d → Ω → ℝ := fun a ω => u.snd a * T a ω with hTu
  set Yv : Fin n → Ω → ℝ := fun j ω => v.fst j * Y j ω with hYv
  set Tv : Fin d → Ω → ℝ := fun b ω => v.snd b * T b ω with hTv
  have hInnerU : (fun ω => (⟪u, F ω⟫_ℝ : ℝ)) =
      (fun ω => ∑ i, Yu i ω) + (fun ω => ∑ a, Tu a ω) := by
    funext ω
    -- `⟪u, F ω⟫ = ⟪u.fst, (F ω).fst⟫ + ⟪u.snd, (F ω).snd⟫`
    --          = ∑ i, u.fst i * Y i ω + ∑ a, u.snd a * T a ω.
    simp [WithLp.prod_inner_apply, PiLp.inner_apply, hF, hYu, hTu, mul_comm,
      Pi.add_apply]
  have hInnerV : (fun ω => (⟪v, F ω⟫_ℝ : ℝ)) =
      (fun ω => ∑ j, Yv j ω) + (fun ω => ∑ b, Tv b ω) := by
    funext ω
    simp [WithLp.prod_inner_apply, PiLp.inner_apply, hF, hYv, hTv, mul_comm,
      Pi.add_apply]
  rw [hInnerU, hInnerV]
  -- Step 3: `MemLp` for each scalar term and each finite-sum block.
  have hYu_memLp : ∀ i, MemLp (Yu i) 2 μ := fun i => (hY i).const_mul _
  have hTu_memLp : ∀ a, MemLp (Tu a) 2 μ := fun a => (hT a).const_mul _
  have hYv_memLp : ∀ j, MemLp (Yv j) 2 μ := fun j => (hY j).const_mul _
  have hTv_memLp : ∀ b, MemLp (Tv b) 2 μ := fun b => (hT b).const_mul _
  have hSumYu : MemLp (fun ω => ∑ i, Yu i ω) 2 μ :=
    memLp_finset_sum _ (fun i _ => hYu_memLp i)
  have hSumTu : MemLp (fun ω => ∑ a, Tu a ω) 2 μ :=
    memLp_finset_sum _ (fun a _ => hTu_memLp a)
  have hSumYv : MemLp (fun ω => ∑ j, Yv j ω) 2 μ :=
    memLp_finset_sum _ (fun j _ => hYv_memLp j)
  have hSumTv : MemLp (fun ω => ∑ b, Tv b ω) 2 μ :=
    memLp_finset_sum _ (fun b _ => hTv_memLp b)
  -- Step 4: split into four covariances via `covariance_add_left/right`.
  rw [covariance_add_left hSumYu hSumTu (hSumYv.add hSumTv),
    covariance_add_right hSumYu hSumYv hSumTv,
    covariance_add_right hSumTu hSumYv hSumTv]
  -- Step 5: expand each of the four `cov[∑, ∑]` via `covariance_fun_sum_fun_sum`,
  -- then pull the constant multipliers out.
  rw [covariance_fun_sum_fun_sum hYu_memLp hYv_memLp,
    covariance_fun_sum_fun_sum hYu_memLp hTv_memLp,
    covariance_fun_sum_fun_sum hTu_memLp hYv_memLp,
    covariance_fun_sum_fun_sum hTu_memLp hTv_memLp]
  -- Step 6: pull constants out and finish.
  have hYY : ∀ i j, cov[Yu i, Yv j; μ] = u.fst i * v.fst j * cov[Y i, Y j; μ] := by
    intro i j
    show cov[fun ω => u.fst i * Y i ω, fun ω => v.fst j * Y j ω; μ] = _
    rw [covariance_const_mul_left, covariance_const_mul_right]; ring
  have hYT : ∀ i b, cov[Yu i, Tv b; μ] = u.fst i * v.snd b * cov[Y i, T b; μ] := by
    intro i b
    show cov[fun ω => u.fst i * Y i ω, fun ω => v.snd b * T b ω; μ] = _
    rw [covariance_const_mul_left, covariance_const_mul_right]; ring
  have hTY : ∀ a j, cov[Tu a, Yv j; μ] = u.snd a * v.fst j * cov[T a, Y j; μ] := by
    intro a j
    show cov[fun ω => u.snd a * T a ω, fun ω => v.fst j * Y j ω; μ] = _
    rw [covariance_const_mul_left, covariance_const_mul_right]; ring
  have hTT : ∀ a b, cov[Tu a, Tv b; μ] = u.snd a * v.snd b * cov[T a, T b; μ] := by
    intro a b
    show cov[fun ω => u.snd a * T a ω, fun ω => v.snd b * T b ω; μ] = _
    rw [covariance_const_mul_left, covariance_const_mul_right]; ring
  simp_rw [hYY, hYT, hTY, hTT]
  ring

end ProbabilityTheory
