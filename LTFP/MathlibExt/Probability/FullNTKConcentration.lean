/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.NTKConcentrationMatrixBernstein
import LTFP.MathlibExt.Probability.GradNTKConcentrationMatrixBernstein

/-!
# Full empirical NTK matrix Bernstein concentration

**R4 NTK Part E2 — full NTK concentration via σ + σ' union bound.**

The full empirical NTK at initialization decomposes as the sum of the
weight-block (σ) and gradient-block (σ') contributions:

    `empiricalFullNTK σ σ' xs ω = empiricalNTK σ xs ω + empiricalGradNTK σ' xs ω`.

Concentration of `‖empiricalFullNTK - populationFullNTK‖` follows from
the triangle inequality at level `t/2` together with the matrix
Bernstein bounds for the two blocks established in Parts D and E1c.

## Main results

* `ProbabilityTheory.empiricalFullNTK` — full empirical NTK definition.
* `ProbabilityTheory.populationFullNTK` — full population NTK definition.
* `ProbabilityTheory.empiricalFullNTK_matrix_bernstein_real` — the
  combined Bernstein-style tail bound,

    `P(t ≤ ‖empiricalFullNTK σ σ' xs ω - populationFullNTK σ σ' xs ν‖)`
      `≤ 2 · matrix_bernstein_bound n (t/2) (4 n² M⁴/m) (2 n M²/m)`
      `+ 2 · matrix_bernstein_bound n (t/2) (4 n² (M'²G)²/m) (2 n (M'²G)/m)`.

## Proof outline

By the triangle inequality on operator norms,

    `‖(empiricalFullNTK - populationFullNTK) ω‖`
      `≤ ‖(empiricalNTK - populationNTK) ω‖ + ‖(empiricalGradNTK - populationGradNTK) ω‖`,

so the event `{ω | t ≤ ‖total deviation‖}` is contained in the union
of the two half-events `{ω | t/2 ≤ ‖σ-block‖}` and
`{ω | t/2 ≤ ‖σ'-block‖}`. Apply `measureReal_union_le` together with
the Part D / Part E1c tail bounds.
-/

open scoped Matrix.Norms.L2Operator

namespace ProbabilityTheory

open MeasureTheory BigOperators Matrix

variable {d : ℕ}

/-! ### Definitions -/

/-- **Full empirical NTK at initialization.**

The full NTK is the sum of the weight-block contribution
`empiricalNTK σ` and the gradient-block contribution
`empiricalGradNTK σ'`. -/
noncomputable def empiricalFullNTK
    {n m : ℕ}
    (σ σ' : ℝ → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  empiricalNTK σ xs ω + empiricalGradNTK σ' xs ω

/-- **Full population NTK.**

The population analogue of `empiricalFullNTK`, summing the weight-block
population NTK `populationNTK σ` and the gradient-block population NTK
`populationGradNTK σ'`. -/
noncomputable def populationFullNTK
    {n : ℕ}
    (σ σ' : ℝ → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d) × ℝ)) :
    Matrix (Fin n) (Fin n) ℝ :=
  populationNTK σ xs ν + populationGradNTK σ' xs ν

/-! ### Main theorem: full NTK concentration via union bound -/

set_option maxHeartbeats 800000 in
/-- **Sharp empirical full-NTK matrix Bernstein concentration (real form).**

For a bounded measurable activation `|σ z| ≤ M` and a bounded measurable
activation derivative `|σ' z| ≤ M'`, given an iid sample of size `m`
from a probability measure `ν`, and any radius `t > 0`,

    `P(t ≤ ‖empiricalFullNTK σ σ' xs ω - populationFullNTK σ σ' xs ν‖)`
      `≤ 2 · matrix_bernstein_bound n (t/2) (4 n² M⁴/m) (2 n M²/m)`
      `+ 2 · matrix_bernstein_bound n (t/2) (4 n² (M'²·G)²/m) (2 n (M'²·G)/m)`.

The bound is obtained from the triangle inequality at level `t/2`
combined with the σ-block Bernstein bound from Part D and the σ'-block
Bernstein bound from Part E1c, via a measure-theoretic union bound.

The regularity hypotheses `hSum_σ`, `hLamMeasPos_σ`, ..., `htrIntNeg_σ'`
are the standard matrix-Bernstein side conditions for the two blocks;
they are passed through verbatim to
`empiricalNTK_matrix_bernstein_real` and
`empiricalGradNTK_matrix_bernstein_real`. -/
theorem empiricalFullNTK_matrix_bernstein_real
    {n m : ℕ} [Nonempty (Fin n)]
    {σ σ' : ℝ → ℝ}
    (hσ_meas : Measurable σ) {M : ℝ} (hM : 0 < M)
    (hσ_bdd : ∀ z, |σ z| ≤ M)
    (hσ'_meas : Measurable σ') {M' : ℝ} (hM' : 0 < M')
    (hσ'_bdd : ∀ z, |σ' z| ≤ M')
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    {G : ℝ} (hG_pos : 0 < G)
    (hG : ∀ a b : Fin n, |inner ℝ (xs a) (xs b)| ≤ G)
    (hm : 0 < m)
    {ν : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d) × ℝ)}
    [MeasureTheory.IsProbabilityMeasure ν]
    {t : ℝ} (ht : 0 < t)
    -- σ-block side conditions for the Part D Bernstein bound at radius `t/2`.
    (hSum_σ : ∀ ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ,
      (∑ i, centeredNeuronNTKSummand σ xs ν m (ω i)).IsHermitian)
    (hLamMeasPos_σ : AEMeasurable
      (fun ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ =>
        Finset.sup' Finset.univ Finset.univ_nonempty (hSum_σ ω).eigenvalues)
      (MeasureTheory.Measure.pi (fun _ : Fin m => ν)))
    (hLamMeasNeg_σ : AEMeasurable
      (fun ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ =>
        Finset.sup' Finset.univ Finset.univ_nonempty (hSum_σ ω).neg.eigenvalues)
      (MeasureTheory.Measure.pi (fun _ : Fin m => ν)))
    (htrIntPos_σ : MeasureTheory.Integrable
      (fun ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ =>
        (Matrix.trace (NormedSpace.exp
          (LTFP.matrix_bernstein_theta (t / 2)
              (4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ))
              (2 * (n : ℝ) * M ^ 2 / (m : ℝ)) •
            (∑ i, centeredNeuronNTKSummand σ xs ν m (ω i))))).re)
      (MeasureTheory.Measure.pi (fun _ : Fin m => ν)))
    (htrIntNeg_σ : MeasureTheory.Integrable
      (fun ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ =>
        (Matrix.trace (NormedSpace.exp
          (LTFP.matrix_bernstein_theta (t / 2)
              (4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ))
              (2 * (n : ℝ) * M ^ 2 / (m : ℝ)) •
            (∑ i, -(centeredNeuronNTKSummand σ xs ν m (ω i)))))).re)
      (MeasureTheory.Measure.pi (fun _ : Fin m => ν)))
    -- σ'-block side conditions for the Part E1c Bernstein bound at radius `t/2`.
    (hSum_σ' : ∀ ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ,
      (∑ i, centeredGradNeuronNTKSummand σ' xs ν m (ω i)).IsHermitian)
    (hLamMeasPos_σ' : AEMeasurable
      (fun ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ =>
        Finset.sup' Finset.univ Finset.univ_nonempty (hSum_σ' ω).eigenvalues)
      (MeasureTheory.Measure.pi (fun _ : Fin m => ν)))
    (hLamMeasNeg_σ' : AEMeasurable
      (fun ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ =>
        Finset.sup' Finset.univ Finset.univ_nonempty (hSum_σ' ω).neg.eigenvalues)
      (MeasureTheory.Measure.pi (fun _ : Fin m => ν)))
    (htrIntPos_σ' : MeasureTheory.Integrable
      (fun ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ =>
        (Matrix.trace (NormedSpace.exp
          (LTFP.matrix_bernstein_theta (t / 2)
              (4 * (n : ℝ) ^ 2 * (M' ^ 2 * G) ^ 2 / (m : ℝ))
              (2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ)) •
            (∑ i, centeredGradNeuronNTKSummand σ' xs ν m (ω i))))).re)
      (MeasureTheory.Measure.pi (fun _ : Fin m => ν)))
    (htrIntNeg_σ' : MeasureTheory.Integrable
      (fun ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ =>
        (Matrix.trace (NormedSpace.exp
          (LTFP.matrix_bernstein_theta (t / 2)
              (4 * (n : ℝ) ^ 2 * (M' ^ 2 * G) ^ 2 / (m : ℝ))
              (2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ)) •
            (∑ i, -(centeredGradNeuronNTKSummand σ' xs ν m (ω i)))))).re)
      (MeasureTheory.Measure.pi (fun _ : Fin m => ν))) :
    (MeasureTheory.Measure.pi (fun _ : Fin m => ν)).real
      {ω | t ≤ ‖empiricalFullNTK σ σ' xs ω - populationFullNTK σ σ' xs ν‖}
    ≤ 2 * LTFP.matrix_bernstein_bound n (t / 2)
            (4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ))
            (2 * (n : ℝ) * M ^ 2 / (m : ℝ))
      + 2 * LTFP.matrix_bernstein_bound n (t / 2)
            (4 * (n : ℝ) ^ 2 * (M' ^ 2 * G) ^ 2 / (m : ℝ))
            (2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ)) := by
  classical
  -- Abbreviations for the deviation matrices.
  set Dσ : (Fin m → EuclideanSpace ℝ (Fin d) × ℝ) → Matrix (Fin n) (Fin n) ℝ :=
    fun ω => empiricalNTK σ xs ω - populationNTK σ xs ν with hDσ_def
  set Dσ' : (Fin m → EuclideanSpace ℝ (Fin d) × ℝ) → Matrix (Fin n) (Fin n) ℝ :=
    fun ω => empiricalGradNTK σ' xs ω - populationGradNTK σ' xs ν with hDσ'_def
  -- The full deviation rearranges as the sum of the two block deviations.
  have h_decomp : ∀ ω,
      empiricalFullNTK σ σ' xs ω - populationFullNTK σ σ' xs ν
        = Dσ ω + Dσ' ω := by
    intro ω
    simp only [empiricalFullNTK, populationFullNTK, hDσ_def, hDσ'_def]
    abel
  -- Triangle-inequality event inclusion.
  have ht_half : 0 < t / 2 := by linarith
  have h_subset :
      {ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ |
          t ≤ ‖empiricalFullNTK σ σ' xs ω - populationFullNTK σ σ' xs ν‖}
        ⊆ {ω | t / 2 ≤ ‖Dσ ω‖} ∪ {ω | t / 2 ≤ ‖Dσ' ω‖} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    rw [h_decomp ω] at hω
    have h_tri : ‖Dσ ω + Dσ' ω‖ ≤ ‖Dσ ω‖ + ‖Dσ' ω‖ := norm_add_le _ _
    have h_t_le : t ≤ ‖Dσ ω‖ + ‖Dσ' ω‖ := le_trans hω h_tri
    -- If both `‖Dσ ω‖ < t/2` and `‖Dσ' ω‖ < t/2`, then their sum is `< t`,
    -- contradicting `h_t_le`.
    by_contra hnot
    rw [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq, not_or] at hnot
    obtain ⟨h_not_σ, h_not_σ'⟩ := hnot
    have h_σ_lt : ‖Dσ ω‖ < t / 2 := lt_of_not_ge h_not_σ
    have h_σ'_lt : ‖Dσ' ω‖ < t / 2 := lt_of_not_ge h_not_σ'
    have h_sum_lt : ‖Dσ ω‖ + ‖Dσ' ω‖ < t := by
      have : ‖Dσ ω‖ + ‖Dσ' ω‖ < t / 2 + t / 2 := add_lt_add h_σ_lt h_σ'_lt
      linarith
    exact (not_le_of_gt h_sum_lt) h_t_le
  -- Measure-monotonicity + union bound on the real probability.
  set μ := MeasureTheory.Measure.pi (fun _ : Fin m => ν)
  have h_prob_top : μ Set.univ ≠ ⊤ := by
    have : μ Set.univ = 1 := by
      simp [μ, MeasureTheory.measure_univ]
    rw [this]; exact ENNReal.one_ne_top
  have h_union_top :
      μ ({ω | t / 2 ≤ ‖Dσ ω‖} ∪ {ω | t / 2 ≤ ‖Dσ' ω‖}) ≠ ⊤ :=
    ne_top_of_le_ne_top h_prob_top (MeasureTheory.measure_mono (Set.subset_univ _))
  have h_mono :
      μ.real {ω | t ≤ ‖empiricalFullNTK σ σ' xs ω - populationFullNTK σ σ' xs ν‖}
        ≤ μ.real ({ω | t / 2 ≤ ‖Dσ ω‖} ∪ {ω | t / 2 ≤ ‖Dσ' ω‖}) :=
    MeasureTheory.measureReal_mono h_subset h_union_top
  have h_union_le :
      μ.real ({ω | t / 2 ≤ ‖Dσ ω‖} ∪ {ω | t / 2 ≤ ‖Dσ' ω‖})
        ≤ μ.real {ω | t / 2 ≤ ‖Dσ ω‖} + μ.real {ω | t / 2 ≤ ‖Dσ' ω‖} :=
    MeasureTheory.measureReal_union_le _ _
  -- Apply Part D and Part E1c at radius `t / 2`.
  have h_σ_bound :
      μ.real {ω | t / 2 ≤ ‖empiricalNTK σ xs ω - populationNTK σ xs ν‖}
        ≤ 2 * LTFP.matrix_bernstein_bound n (t / 2)
              (4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ))
              (2 * (n : ℝ) * M ^ 2 / (m : ℝ)) :=
    empiricalNTK_matrix_bernstein_real hσ_meas hM hσ_bdd xs hm ht_half
      hSum_σ hLamMeasPos_σ hLamMeasNeg_σ htrIntPos_σ htrIntNeg_σ
  have h_σ'_bound :
      μ.real {ω | t / 2 ≤ ‖empiricalGradNTK σ' xs ω - populationGradNTK σ' xs ν‖}
        ≤ 2 * LTFP.matrix_bernstein_bound n (t / 2)
              (4 * (n : ℝ) ^ 2 * (M' ^ 2 * G) ^ 2 / (m : ℝ))
              (2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ)) :=
    empiricalGradNTK_matrix_bernstein_real hσ'_meas hM' hσ'_bdd xs hG_pos hG hm ht_half
      hSum_σ' hLamMeasPos_σ' hLamMeasNeg_σ' htrIntPos_σ' htrIntNeg_σ'
  -- Chain the inequalities.
  calc μ.real {ω | t ≤ ‖empiricalFullNTK σ σ' xs ω - populationFullNTK σ σ' xs ν‖}
      ≤ μ.real ({ω | t / 2 ≤ ‖Dσ ω‖} ∪ {ω | t / 2 ≤ ‖Dσ' ω‖}) := h_mono
    _ ≤ μ.real {ω | t / 2 ≤ ‖Dσ ω‖} + μ.real {ω | t / 2 ≤ ‖Dσ' ω‖} := h_union_le
    _ ≤ 2 * LTFP.matrix_bernstein_bound n (t / 2)
              (4 * (n : ℝ) ^ 2 * M ^ 4 / (m : ℝ))
              (2 * (n : ℝ) * M ^ 2 / (m : ℝ))
        + 2 * LTFP.matrix_bernstein_bound n (t / 2)
              (4 * (n : ℝ) ^ 2 * (M' ^ 2 * G) ^ 2 / (m : ℝ))
              (2 * (n : ℝ) * (M' ^ 2 * G) / (m : ℝ)) := by
          exact add_le_add h_σ_bound h_σ'_bound

end ProbabilityTheory
