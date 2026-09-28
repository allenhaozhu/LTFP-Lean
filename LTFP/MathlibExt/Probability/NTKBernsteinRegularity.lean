/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.FullNTKConcentration
import LTFP.MathlibExt.MatrixAnalysis.LoewnerPerturbation
import LTFP.MathlibExt.MatrixAnalysis.MatrixExpPositivity

/-!
# Regularity side conditions of the full-NTK matrix Bernstein bound

`empiricalFullNTK_matrix_bernstein_real` carries measure-theoretic side
conditions for each of its two blocks: Hermitian-ness of the sample sum,
a.e.-measurability of the largest eigenvalue of `± (sample sum)`, and
integrability of `Re tr exp (θ • ± (sample sum))`. This file discharges all
of them when the activation `σ` and its derivative proxy `σ'` are continuous
and bounded.

The largest eigenvalue is handled through the Loewner characterisation
`A ≤ λ_max(A) • 1`, which gives the Lipschitz bound
`λ_max(B) ≤ λ_max(A) + ‖B - A‖` in operator norm; hence `λ_max` of a
continuous Hermitian family is continuous, in particular measurable. The
trace exponential is continuous and takes values in the image of a compact
operator-norm ball, so it is bounded and therefore integrable.

## Main results

* `Matrix.IsHermitian.supEigenvalues_le_add_norm_sub` — Lipschitz bound for
  the largest eigenvalue.
* `continuous_supEigenvalues` — continuity of `λ_max` along a continuous
  Hermitian family.
* `integrable_re_trace_exp_smul` — integrability of `Re tr exp (c • F)` for a
  continuous bounded family `F`.
* `empiricalFullNTK_matrix_bernstein_real_of_continuous` — the full-NTK
  Bernstein tail bound with all side conditions discharged.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

open MeasureTheory Matrix BigOperators

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- A Hermitian matrix lies below its largest eigenvalue in the Loewner order. -/
theorem IsHermitian.le_supEigenvalues_smul_one {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A ≤ (Finset.univ.sup' Finset.univ_nonempty hA.eigenvalues : ℝ) • (1 : Matrix n n ℂ) := by
  rw [← Algebra.algebraMap_eq_smul_one]
  refine (le_algebraMap_iff_spectrum_le (R := ℝ) hA.isSelfAdjoint).mpr fun x hx => ?_
  rw [hA.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  exact Finset.le_sup' _ (Finset.mem_univ i)

/-- If a Hermitian matrix lies below `c • 1`, then its largest eigenvalue is at
most `c`. -/
theorem IsHermitian.supEigenvalues_le_of_le_smul_one {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {c : ℝ} (h : A ≤ c • (1 : Matrix n n ℂ)) :
    Finset.univ.sup' Finset.univ_nonempty hA.eigenvalues ≤ c := by
  rw [← Algebra.algebraMap_eq_smul_one] at h
  have hspec := (le_algebraMap_iff_spectrum_le (R := ℝ) hA.isSelfAdjoint).mp h
  refine Finset.sup'_le _ _ fun i _ => hspec _ (hA.eigenvalues_mem_spectrum_real i)

/-- **Lipschitz bound for the largest eigenvalue** in operator norm. -/
theorem IsHermitian.supEigenvalues_le_add_norm_sub {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Finset.univ.sup' Finset.univ_nonempty hB.eigenvalues ≤
      Finset.univ.sup' Finset.univ_nonempty hA.eigenvalues + ‖B - A‖ := by
  refine hB.supEigenvalues_le_of_le_smul_one ?_
  have h1 := hA.le_supEigenvalues_smul_one
  have h2 : B - A ≤ (‖B - A‖ : ℝ) • (1 : Matrix n n ℂ) := (hB.sub hA).le_norm_smul_one
  calc B = A + (B - A) := by abel
    _ ≤ (Finset.univ.sup' Finset.univ_nonempty hA.eigenvalues : ℝ) • (1 : Matrix n n ℂ) +
          (‖B - A‖ : ℝ) • (1 : Matrix n n ℂ) := add_le_add h1 h2
    _ = _ := by rw [add_smul]

end Matrix

namespace ProbabilityTheory

variable {d : ℕ}

section General

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The largest eigenvalue of a continuous Hermitian family is continuous. -/
theorem continuous_supEigenvalues [Nonempty ι] {Ω : Type*} [TopologicalSpace Ω]
    {F : Ω → Matrix ι ι ℂ} (hF : Continuous F) (hH : ∀ ω, (F ω).IsHermitian) :
    Continuous fun ω => Finset.univ.sup' Finset.univ_nonempty (hH ω).eigenvalues := by
  refine continuous_iff_continuousAt.mpr fun ω₀ => ?_
  have hlim : Filter.Tendsto (fun ω => ‖F ω - F ω₀‖) (nhds ω₀) (nhds 0) := by
    have := (hF.tendsto ω₀).sub_const (F ω₀)
    rw [sub_self] at this
    simpa using this.norm
  refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
  refine squeeze_zero (fun _ => norm_nonneg _) (fun ω => ?_) hlim
  rw [Real.norm_eq_abs, abs_le]
  have h1 := (hH ω₀).supEigenvalues_le_add_norm_sub (hH ω)
  have h2 := (hH ω).supEigenvalues_le_add_norm_sub (hH ω₀)
  rw [norm_sub_rev] at h2
  constructor <;> linarith

/-- `Re tr exp (c • F)` is integrable for a continuous family `F` that is
bounded in operator norm. -/
theorem integrable_re_trace_exp_smul {Ω : Type*} [TopologicalSpace Ω] [MeasurableSpace Ω]
    [OpensMeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {F : Ω → Matrix ι ι ℂ} (hF : Continuous F) {C : ℝ} (hC : ∀ ω, ‖F ω‖ ≤ C) (c : ℝ) :
    Integrable (fun ω => (Matrix.trace (NormedSpace.exp (c • F ω))).re) μ := by
  set g : Matrix ι ι ℂ → ℝ := fun H => (Matrix.trace (NormedSpace.exp H)).re with hg
  have hg_cont : Continuous g := Matrix.continuous_re_trace_exp
  have hcont : Continuous fun ω => g (c • F ω) := hg_cont.comp (continuous_const.smul hF)
  have hK : IsCompact (Metric.closedBall (0 : Matrix ι ι ℂ) (|c| * C)) :=
    isCompact_closedBall _ _
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hg_cont.continuousOn
  refine Integrable.of_bound hcont.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun ω => hB _ ?_)
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hC ω) (abs_nonneg c)

/-- Operator-norm bound for a finite sum of uniformly bounded matrices. -/
theorem norm_sum_le_card_mul {κ : Type*} [Fintype κ] {X : κ → Matrix ι ι ℂ} {R : ℝ}
    (hX : ∀ i, ‖X i‖ ≤ R) : ‖∑ i, X i‖ ≤ Fintype.card κ * R := by
  calc ‖∑ i, X i‖ ≤ ∑ i, ‖X i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : κ, R := Finset.sum_le_sum fun i _ => hX i
    _ = Fintype.card κ * R := by rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

omit [Fintype ι] [DecidableEq ι] in
/-- A finite sum of Hermitian matrices is Hermitian. -/
theorem isHermitian_sum' {κ : Type*} [Fintype κ] {X : κ → Matrix ι ι ℂ}
    (hX : ∀ i, (X i).IsHermitian) : (∑ i, X i).IsHermitian := by
  classical
  refine Finset.sum_induction _ (fun A : Matrix ι ι ℂ => A.IsHermitian)
    (fun _ _ ha hb => ha.add hb) isHermitian_zero fun i _ => hX i

end General

section NTK

variable {n : ℕ}

/-- Continuity of the centred σ-block summand in the sampled neuron. -/
theorem continuous_centeredNeuronNTKSummand {σ : ℝ → ℝ} (hσ : Continuous σ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) (m : ℕ) :
    Continuous (centeredNeuronNTKSummand σ xs ν m) := by
  unfold centeredNeuronNTKSummand
  refine continuous_const.smul (Continuous.sub ?_ continuous_const)
  refine continuous_matrix fun a b => ?_
  unfold neuronNTKMatrixC neuronNTK
  refine Complex.continuous_ofReal.comp ?_
  refine Continuous.mul ?_ ?_ <;>
    exact hσ.comp ((continuous_fst.inner continuous_const).add continuous_snd)

/-- Continuity of the centred σ'-block summand in the sampled neuron. -/
theorem continuous_centeredGradNeuronNTKSummand {σ' : ℝ → ℝ} (hσ' : Continuous σ')
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) (m : ℕ) :
    Continuous (centeredGradNeuronNTKSummand σ' xs ν m) := by
  unfold centeredGradNeuronNTKSummand
  refine continuous_const.smul (Continuous.sub ?_ continuous_const)
  refine continuous_matrix fun a b => ?_
  unfold gradNeuronNTKMatrixC gradNeuronNTK
  refine Complex.continuous_ofReal.comp ?_
  refine Continuous.mul (Continuous.mul ?_ ?_) continuous_const <;>
    exact hσ'.comp ((continuous_fst.inner continuous_const).add continuous_snd)

set_option maxHeartbeats 800000 in
/-- **Full-NTK matrix Bernstein bound with the side conditions discharged.**

For continuous activations `σ, σ'` bounded by `M, M'`, an iid sample of size
`m` from a probability measure `ν`, and `t > 0`,

  `P(t ≤ ‖empiricalFullNTK σ σ' xs ω - populationFullNTK σ σ' xs ν‖)`
    `≤ 2 · matrix_bernstein_bound n (t/2) (4 n² M⁴/m) (2 n M²/m)`
    `+ 2 · matrix_bernstein_bound n (t/2) (4 n² (M'²G)²/m) (2 n (M'²G)/m)`,

with no remaining regularity hypothesis. -/
theorem empiricalFullNTK_matrix_bernstein_real_of_continuous
    {m : ℕ} [Nonempty (Fin n)]
    {σ σ' : ℝ → ℝ}
    (hσ_cont : Continuous σ) {M : ℝ} (hM : 0 < M) (hσ_bdd : ∀ z, |σ z| ≤ M)
    (hσ'_cont : Continuous σ') {M' : ℝ} (hM' : 0 < M') (hσ'_bdd : ∀ z, |σ' z| ≤ M')
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    {G : ℝ} (hG_pos : 0 < G) (hG : ∀ a b : Fin n, |inner ℝ (xs a) (xs b)| ≤ G)
    (hm : 0 < m)
    {ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)} [IsProbabilityMeasure ν]
    {t : ℝ} (ht : 0 < t) :
    (Measure.pi (fun _ : Fin m => ν)).real
      {ω | t ≤ ‖empiricalFullNTK σ σ' xs ω - populationFullNTK σ σ' xs ν‖}
    ≤ 2 * LTFP.matrix_bernstein_bound n (t / 2)
            (4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ))
            (2 * (n : ℝ) * M ^ 2 / (m : ℝ))
      + 2 * LTFP.matrix_bernstein_bound n (t / 2)
            (4 * (n : ℝ) ^ 2 * (M' ^ 2 * G) ^ 2 / (m : ℝ))
            (2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ)) := by
  classical
  set μ := Measure.pi (fun _ : Fin m => ν)
  -- The two sample-sum families, their continuity and uniform bounds.
  set Sσ : (Fin m → EuclideanSpace ℝ (Fin d) × ℝ) → Matrix (Fin n) (Fin n) ℂ :=
    fun ω => ∑ i, centeredNeuronNTKSummand σ xs ν m (ω i) with hSσ
  set Sσ' : (Fin m → EuclideanSpace ℝ (Fin d) × ℝ) → Matrix (Fin n) (Fin n) ℂ :=
    fun ω => ∑ i, centeredGradNeuronNTKSummand σ' xs ν m (ω i) with hSσ'
  have hcσ : Continuous Sσ := continuous_finset_sum _ fun i _ =>
    (continuous_centeredNeuronNTKSummand hσ_cont xs ν m).comp (continuous_apply i)
  have hcσ' : Continuous Sσ' := continuous_finset_sum _ fun i _ =>
    (continuous_centeredGradNeuronNTKSummand hσ'_cont xs ν m).comp (continuous_apply i)
  have hbσ : ∀ ω, ‖Sσ ω‖ ≤ Fintype.card (Fin m) * (2 * (n : ℝ) * M ^ 2 / (m : ℝ)) :=
    fun ω => norm_sum_le_card_mul fun i =>
      centeredNeuronNTKSummand_opNorm_le hM.le hσ_bdd xs ν hm (ω i)
  have hbσ' : ∀ ω, ‖Sσ' ω‖ ≤
      Fintype.card (Fin m) * (2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ)) :=
    fun ω => norm_sum_le_card_mul fun i =>
      centeredGradNeuronNTKSummand_opNorm_le hM'.le hG_pos.le hσ'_bdd xs hG ν hm (ω i)
  have hbσn : ∀ ω, ‖-Sσ ω‖ ≤ Fintype.card (Fin m) * (2 * (n : ℝ) * M ^ 2 / (m : ℝ)) :=
    fun ω => (norm_neg _).le.trans (hbσ ω)
  have hbσ'n : ∀ ω, ‖-Sσ' ω‖ ≤
      Fintype.card (Fin m) * (2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ)) :=
    fun ω => (norm_neg _).le.trans (hbσ' ω)
  have hHσ : ∀ ω, (Sσ ω).IsHermitian := fun ω =>
    isHermitian_sum' fun i => centeredNeuronNTKSummand_isHermitian σ xs ν (ω i)
  have hHσ' : ∀ ω, (Sσ' ω).IsHermitian := fun ω =>
    isHermitian_sum' fun i => centeredGradNeuronNTKSummand_isHermitian σ' xs ν (ω i)
  have hneg : ∀ (X : Fin m → Matrix (Fin n) (Fin n) ℂ), ∑ i, -X i = -∑ i, X i :=
    fun X => Finset.sum_neg_distrib _
  refine empiricalFullNTK_matrix_bernstein_real hσ_cont.measurable hM hσ_bdd
    hσ'_cont.measurable hM' hσ'_bdd xs hG_pos hG hm ht hHσ
    (continuous_supEigenvalues hcσ hHσ).measurable.aemeasurable
    (continuous_supEigenvalues hcσ.neg fun ω => (hHσ ω).neg).measurable.aemeasurable
    (integrable_re_trace_exp_smul hcσ hbσ _) ?_ hHσ'
    (continuous_supEigenvalues hcσ' hHσ').measurable.aemeasurable
    (continuous_supEigenvalues hcσ'.neg fun ω => (hHσ' ω).neg).measurable.aemeasurable
    (integrable_re_trace_exp_smul hcσ' hbσ' _) ?_
  · simp_rw [hneg]
    exact integrable_re_trace_exp_smul hcσ.neg hbσn _
  · simp_rw [hneg]
    exact integrable_re_trace_exp_smul hcσ'.neg hbσ'n _

end NTK

end ProbabilityTheory
