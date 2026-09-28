/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.NTKBernsteinRegularity
import LTFP.MathlibExt.Probability.NTKAntisymmetricInit
import LTFP.MathlibExt.Probability.NTKLazyTrainingEndToEnd

/-!
# Initial coercivity of the training kernel with high probability

If the population full NTK is Loewner-coercive, `lam₀ • 1 ≤ K_pop`, then the
empirical full NTK of an iid `k`-sample is `(lam₀ / 2)`-coercive with
probability at least `1 - δ`, as soon as the width `k` exceeds an explicit
Bernstein threshold. Through the antisymmetric initialisation, the same
holds for the training kernel of the doubled width-`k + k` network.

## Main definitions

* `ntkBernsteinWidth n A s δ` — the width making one matrix-Bernstein block
  with envelope `A` at deviation `s` have tail at most `δ / 2`:
  `2 (4 n² A² + 2 n A s / 3) / s² · log (8 n / δ)`.

## Main results

* `two_mul_matrix_bernstein_bound_le` — Bernstein inversion.
* `empiricalFullNTK_coercive_whp` — `(lam₀/2) • 1 ≤ K_emp(ω)` with probability
  at least `1 - δ`.
* `fullTrainingKernel_antisymInit_coercive_whp` — the same statement for the
  training kernel of the antisymmetric initialisation.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator

open MeasureTheory Matrix BigOperators

namespace ProbabilityTheory

variable {d : ℕ}

/-- Width making one matrix-Bernstein block with envelope `A` at deviation
`s` have tail at most `δ / 2`. -/
noncomputable def ntkBernsteinWidth (n : ℕ) (A s δ : ℝ) : ℝ :=
  2 * (4 * (n : ℝ) ^ 2 * A ^ 2 + 2 * (n : ℝ) * A * s / 3) / s ^ 2 *
    Real.log (8 * (n : ℝ) / δ)

/-- **Bernstein inversion.** If `k ≥ ntkBernsteinWidth n A s δ`, the
(doubled) matrix-Bernstein tail with variance proxy `4 n² A² / k` and range
`2 n A / k` at deviation `s` is at most `δ / 2`. -/
theorem two_mul_matrix_bernstein_bound_le {n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    {A s δ : ℝ} (hA : 0 < A) (hs : 0 < s) (hδ : 0 < δ)
    (hW : ntkBernsteinWidth n A s δ ≤ k) :
    2 * LTFP.matrix_bernstein_bound n s
        (4 * (n : ℝ) ^ 2 * A ^ 2 / (k : ℝ)) (2 * (n : ℝ) * A / (k : ℝ)) ≤ δ / 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set c : ℝ := 4 * (n : ℝ) ^ 2 * A ^ 2 + 2 * (n : ℝ) * A * s / 3 with hc
  have hc_pos : 0 < c := by rw [hc]; positivity
  set L : ℝ := Real.log (8 * (n : ℝ) / δ) with hL
  have hden : 4 * (n : ℝ) ^ 2 * A ^ 2 / (k : ℝ) + 2 * (n : ℝ) * A / (k : ℝ) * s / 3 =
      c / k := by
    rw [hc]; field_simp
  have hWc : 2 * c / s ^ 2 * L ≤ k := hW
  -- `L ≤ (s²/2) / (c/k)`.
  have hLle : L ≤ s ^ 2 / 2 / (c / k) := by
    have h1 : s ^ 2 / 2 / (c / k) = k * s ^ 2 / (2 * c) := by
      field_simp
    rw [h1, le_div_iff₀ (by positivity)]
    have h2 : 2 * c / s ^ 2 * L * s ^ 2 = L * (2 * c) := by
      field_simp
    have h3 := mul_le_mul_of_nonneg_right hWc (sq_nonneg s)
    rw [h2] at h3
    linarith
  have hexp : Real.exp (-(s ^ 2 / 2) / (c / k)) ≤ δ / (8 * n) := by
    have h1 : Real.exp (-L) = δ / (8 * n) := by
      rw [hL, Real.exp_neg, Real.exp_log (by positivity), inv_div]
    rw [← h1, neg_div]
    exact Real.exp_le_exp.mpr (neg_le_neg hLle)
  unfold LTFP.matrix_bernstein_bound
  rw [hden]
  calc 2 * (2 * (n : ℝ) * Real.exp (-(s ^ 2 / 2) / (c / k)))
      ≤ 2 * (2 * (n : ℝ) * (δ / (8 * n))) := by gcongr
    _ = δ / 2 := by field_simp; ring

/-- The population full NTK is symmetric. -/
theorem populationFullNTK_isHermitian {n : ℕ} (σ σ' : ℝ → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)) :
    (populationFullNTK σ σ' xs ν).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [star_trivial, populationFullNTK, Matrix.add_apply]
  rw [populationNTK_symm, populationGradNTK_symm]

/-- The empirical full NTK is symmetric. -/
theorem empiricalFullNTK_isHermitian {n k : ℕ} (σ σ' : ℝ → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ω : Fin k → EuclideanSpace ℝ (Fin d) × ℝ) :
    (empiricalFullNTK σ σ' xs ω).IsHermitian := by
  rw [← fullTrainingKernel_antisymInit]
  exact fullTrainingKernel_isHermitian _ _ _ _ _

/-- **Initial coercivity with high probability.**

Let `σ, σ'` be continuous with `|σ| ≤ M`, `|σ'| ≤ M'`, let `‖xᵢ‖ ≤ X`, and
let the population full NTK satisfy `lam₀ • 1 ≤ K_pop`. If the width `k`
exceeds both Bernstein thresholds at deviation `lam₀ / 4`, then with
probability at least `1 - δ` over the iid sample, `(lam₀/2) • 1 ≤ K_emp(ω)`. -/
theorem empiricalFullNTK_coercive_whp {n k : ℕ} [Nonempty (Fin n)] (hk : 0 < k)
    {σ σ' : ℝ → ℝ}
    (hσ_cont : Continuous σ) {M : ℝ} (hM : 0 < M) (hσ_bdd : ∀ z, |σ z| ≤ M)
    (hσ'_cont : Continuous σ') {M' : ℝ} (hM' : 0 < M') (hσ'_bdd : ∀ z, |σ' z| ≤ M')
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) {X : ℝ} (hX_pos : 0 < X)
    (hX : ∀ i, ‖xs i‖ ≤ X)
    {ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)} [IsProbabilityMeasure ν]
    {lam₀ : ℝ} (hlam : 0 < lam₀)
    (hpop : lam₀ • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ populationFullNTK σ σ' xs ν)
    {δ : ℝ} (hδ : 0 < δ)
    (hWσ : ntkBernsteinWidth n (M ^ 2) (lam₀ / 4) δ ≤ k)
    (hWσ' : ntkBernsteinWidth n (M' ^ 2 * X ^ 2) (lam₀ / 4) δ ≤ k) :
    1 - δ ≤ (Measure.pi (fun _ : Fin k => ν)).real
      {ω | (lam₀ / 2) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ empiricalFullNTK σ σ' xs ω} := by
  classical
  set μ := Measure.pi (fun _ : Fin k => ν)
  have hn : 0 < n := Fin.pos_iff_nonempty.mpr inferInstance
  -- Gram entries are bounded by `X²`.
  have hG : ∀ a b : Fin n, |inner ℝ (xs a) (xs b)| ≤ X ^ 2 := by
    intro a b
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [sq]
    exact mul_le_mul (hX a) (hX b) (norm_nonneg _) hX_pos.le
  -- Tail bound at deviation `lam₀ / 2`.
  set bad := {ω : Fin k → EuclideanSpace ℝ (Fin d) × ℝ |
    lam₀ / 2 ≤ ‖empiricalFullNTK σ σ' xs ω - populationFullNTK σ σ' xs ν‖} with hbad
  have hbern := empiricalFullNTK_matrix_bernstein_real_of_continuous hσ_cont hM hσ_bdd
    hσ'_cont hM' hσ'_bdd xs (by positivity) hG hk (ν := ν) (half_pos hlam)
  rw [show lam₀ / 2 / 2 = lam₀ / 4 by ring, show M ^ 4 = (M ^ 2) ^ 2 by ring] at hbern
  have h1 := two_mul_matrix_bernstein_bound_le hn hk (by positivity) (by positivity) hδ hWσ
  have h2 := two_mul_matrix_bernstein_bound_le hn hk (by positivity) (by positivity) hδ hWσ'
  have hbad_le : μ.real bad ≤ δ := by
    have := hbern.trans (add_le_add h1 h2)
    linarith
  -- Off the bad event, the empirical kernel inherits half of the floor.
  have hsub : Set.univ ⊆
      {ω | (lam₀ / 2) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ empiricalFullNTK σ σ' xs ω} ∪ bad := by
    intro ω _
    by_cases hω : ω ∈ bad
    · exact Or.inr hω
    · left
      have hlt : ‖populationFullNTK σ σ' xs ν - empiricalFullNTK σ σ' xs ω‖ ≤ lam₀ / 2 := by
        rw [norm_sub_rev]
        exact (lt_of_not_ge hω).le
      have := LTFP.real_le_smul_one_perturb (populationFullNTK_isHermitian σ σ' xs ν)
        (empiricalFullNTK_isHermitian σ σ' xs ω) hpop hlt
      rwa [show lam₀ - lam₀ / 2 = lam₀ / 2 by ring] at this
  have hone : (1 : ℝ) ≤ μ.real
      ({ω | (lam₀ / 2) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ empiricalFullNTK σ σ' xs ω} ∪ bad) := by
    rw [← probReal_univ (μ := μ)]
    exact measureReal_mono hsub
  have hunion := measureReal_union_le (μ := μ)
    {ω | (lam₀ / 2) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ empiricalFullNTK σ σ' xs ω} bad
  linarith

/-- **Initial coercivity of the antisymmetric initialisation, with high
probability.** Same hypotheses as `empiricalFullNTK_coercive_whp`; the
conclusion is stated for the training kernel of the doubled network. -/
theorem fullTrainingKernel_antisymInit_coercive_whp {n k : ℕ} [Nonempty (Fin n)]
    (hk : 0 < k) {σ σ' : ℝ → ℝ}
    (hσ_cont : Continuous σ) {M : ℝ} (hM : 0 < M) (hσ_bdd : ∀ z, |σ z| ≤ M)
    (hσ'_cont : Continuous σ') {M' : ℝ} (hM' : 0 < M') (hσ'_bdd : ∀ z, |σ' z| ≤ M')
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) {X : ℝ} (hX_pos : 0 < X)
    (hX : ∀ i, ‖xs i‖ ≤ X)
    {ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)} [IsProbabilityMeasure ν]
    {lam₀ : ℝ} (hlam : 0 < lam₀)
    (hpop : lam₀ • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ populationFullNTK σ σ' xs ν)
    {δ : ℝ} (hδ : 0 < δ)
    (hWσ : ntkBernsteinWidth n (M ^ 2) (lam₀ / 4) δ ≤ k)
    (hWσ' : ntkBernsteinWidth n (M' ^ 2 * X ^ 2) (lam₀ / 4) δ ≤ k) :
    1 - δ ≤ (Measure.pi (fun _ : Fin k => ν)).real
      {ω | (lam₀ / 2) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤
        fullTrainingKernel σ σ' (antisymInitBias ω) (antisymInitParam ω) xs} := by
  simp_rw [fullTrainingKernel_antisymInit]
  exact empiricalFullNTK_coercive_whp hk hσ_cont hM hσ_bdd hσ'_cont hM' hσ'_bdd xs hX_pos hX
    hlam hpop hδ hWσ hWσ'

end ProbabilityTheory
