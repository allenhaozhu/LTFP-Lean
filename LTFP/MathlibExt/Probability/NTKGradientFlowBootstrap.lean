/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.NTKGradientFlowDecay
import LTFP.MathlibExt.Probability.NTKCoercivityPreservation

/-!
# Lazy training of the two-layer network along gradient flow

This file closes the bootstrap for the explicit gradient flow of
`fullNet` on a compact time interval `[0, T]` (Du et al. style
argument). As long as every neuron has moved less than a threshold
`D ≤ 1`, the output weights stay bounded by `2`, the training kernel
keeps half of its initial Loewner floor, the residual decays like
`e^{-ρ t / 2}`, and every neuron moves by at most `gfMovementBound`.
A first-exit argument (infimum of a closed set) shows the threshold is
never reached, provided the explicit width conditions hold.

## Main definitions

* `gfMovementBound` — the per-neuron movement budget
  `(2/ρ) · (1/√m) (M + 2 M' X) √n R₀`.
* `gfDriftConst` — the operator-norm Lipschitz constant of the training
  kernel with output weights bounded by `2` and `|⟪xᵢ, xⱼ⟫| ≤ X²`.

## Main result

* `fullNet_gradient_flow_lazy_training` — exponential residual decay
  `‖r t‖² ≤ ‖r 0‖² e^{-ρ t}` and the per-neuron movement bound on `[0, T]`.
-/

namespace ProbabilityTheory

open BigOperators Real Matrix LTFP Set
open scoped InnerProductSpace MatrixOrder

variable {d n m : ℕ}

/-- Per-neuron movement budget `(2/ρ) · (1/√m) (M + 2 M' X) √n R₀`. -/
noncomputable def gfMovementBound (n m : ℕ) (ρ M M' X R₀ : ℝ) : ℝ :=
  2 / ρ * (1 / Real.sqrt m * (M + 2 * M' * X) * Real.sqrt n * R₀)

/-- Operator-norm drift constant of the training kernel (output weights
bounded by `2`, Gram entries bounded by `X²`, `Lip σ ≤ M'`). -/
noncomputable def gfDriftConst (M M' Lσ' X : ℝ) : ℝ :=
  2 * M * M' * X + 2 * 2 * M' ^ 2 * X ^ 2 + 2 * 2 ^ 2 * M' * Lσ' * X * X ^ 2

/-- **Lazy training along gradient flow on `[0, T]`.**

Let `σ` be differentiable with `|σ| ≤ M`, `|σ'| ≤ M'` and `σ'`
`Lσ'`-Lipschitz, let `‖xᵢ‖ ≤ X`, and let `θ` be a gradient-flow
trajectory on `[0, T]` (continuous on `Icc 0 T`, right derivative
`gfFieldFullNet` on `Ico 0 T`) with `|a_j(θ 0)| ≤ 1`, initial Loewner
floor `ρ • 1 ≤ K(θ 0)` and `‖r(0)‖ ≤ R₀`. If the width conditions
`gfMovementBound < 1` and `n · gfDriftConst · gfMovementBound < ρ / 2`
hold, then on `[0, T]` the residual decays as `‖r t‖² ≤ ‖r 0‖² e^{-ρ t}`
and every neuron moves by at most `gfMovementBound`. -/
theorem fullNet_gradient_flow_lazy_training
    [Nonempty (Fin n)] (hm : 0 < m)
    (σ : ℝ → ℝ) (hσ : Differentiable ℝ σ)
    {M M' : ℝ} (hσ_bdd : ∀ z, |σ z| ≤ M) (hσ'_bdd : ∀ z, |deriv σ z| ≤ M')
    {Lσ' : NNReal} (hσ'_lip : LipschitzWith Lσ' (deriv σ))
    (b : Fin m → ℝ) (y : Fin n → ℝ) (xs : Fin n → EuclideanSpace ℝ (Fin d))
    {X : ℝ} (hX : ∀ i, ‖xs i‖ ≤ X)
    (θ : ℝ → Param d m) {T : ℝ}
    (hθ_cont : ContinuousOn θ (Icc 0 T))
    (hθ_der : ∀ t ∈ Ico 0 T,
      HasDerivWithinAt θ (gfFieldFullNet σ b y xs (θ t)) (Ici t) t)
    (ha₀ : ∀ j, |(θ 0).1 j| ≤ 1)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hK₀ : ρ • (1 : Matrix (Fin n) (Fin n) ℝ) ≤
      fullTrainingKernel σ (deriv σ) b (θ 0) xs)
    {R₀ : ℝ} (hR₀ : ‖residualFullNet σ b y xs (θ 0)‖ ≤ R₀)
    (hW₁ : gfMovementBound n m ρ M M' X R₀ < 1)
    (hW₂ : (n : ℝ) * gfDriftConst M M' Lσ' X * gfMovementBound n m ρ M M' X R₀ < ρ / 2) :
    ∀ t ∈ Icc 0 T,
      ‖residualFullNet σ b y xs (θ t)‖ ^ 2 ≤
          ‖residualFullNet σ b y xs (θ 0)‖ ^ 2 * Real.exp (-(ρ * t)) ∧
        ∀ j, dist ((θ t).1 j, (θ t).2 j) ((θ 0).1 j, (θ 0).2 j) ≤
          gfMovementBound n m ρ M M' X R₀ := by
  -- Basic nonnegativity facts.
  have hM : 0 ≤ M := (abs_nonneg _).trans (hσ_bdd 0)
  have hM' : 0 ≤ M' := (abs_nonneg _).trans (hσ'_bdd 0)
  have hX0 : 0 ≤ X := (norm_nonneg _).trans (hX (Classical.arbitrary _))
  have hR₀nn : 0 ≤ R₀ := (norm_nonneg _).trans hR₀
  -- `σ` is `M'`-Lipschitz.
  have hσ_lip : LipschitzWith (Real.toNNReal M') σ := by
    refine lipschitzWith_of_nnnorm_deriv_le hσ fun z => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hM', Real.norm_eq_abs]
    exact hσ'_bdd z
  have hLσ : ((Real.toNNReal M' : NNReal) : ℝ) = M' := Real.coe_toNNReal _ hM'
  -- Gram entries are bounded by `X²`.
  have hG : ∀ a c, |⟪xs a, xs c⟫_ℝ| ≤ X ^ 2 := by
    intro a c
    refine (abs_real_inner_le_norm _ _).trans ?_
    rw [sq]
    exact mul_le_mul (hX a) (hX c) (norm_nonneg _) hX0
  -- Constants.
  set Mmov := gfMovementBound n m ρ M M' X R₀ with hMmov
  set C := gfDriftConst M M' (Lσ' : ℝ) X with hC
  have hCnn : 0 ≤ C := by
    have := Lσ'.coe_nonneg
    simp only [hC, gfDriftConst]
    positivity
  have hnC : 0 ≤ (n : ℝ) * C := mul_nonneg (Nat.cast_nonneg n) hCnn
  -- Bootstrap threshold `D` with `Mmov < D ≤ 1` and `n C D ≤ ρ/2`.
  set δ := ρ / 2 - (n : ℝ) * C * Mmov with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  set D := min 1 (Mmov + δ / ((n : ℝ) * C + 1)) with hD
  have hD1 : D ≤ 1 := min_le_left _ _
  have hMmovnn : 0 ≤ Mmov := by
    simp only [hMmov, gfMovementBound]; positivity
  have hMD : Mmov < D := by
    refine lt_min hW₁ ?_
    have : 0 < δ / ((n : ℝ) * C + 1) := by positivity
    linarith
  have hDnn : 0 ≤ D := hMmovnn.trans hMD.le
  have hDsmall : (n : ℝ) * C * D ≤ ρ / 2 := by
    have h1 : (n : ℝ) * C * D ≤ (n : ℝ) * C * (Mmov + δ / ((n : ℝ) * C + 1)) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) hnC
    have h2 : (n : ℝ) * C * (δ / ((n : ℝ) * C + 1)) ≤ δ := by
      rw [mul_div_assoc']
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith
  -- Shorthands.
  set r : ℝ → EuclideanSpace ℝ (Fin n) := fun t => residualFullNet σ b y xs (θ t) with hr
  set K₀ : ℝ := 1 / Real.sqrt m * (M + 2 * M' * X) * Real.sqrt n * R₀ with hK₀def
  have hK₀nn : 0 ≤ K₀ := by rw [hK₀def]; positivity
  have hMmovK : Mmov = 2 / ρ * K₀ := rfl
  -- Core estimate on `[0, s]` under the threshold hypothesis.
  have core : ∀ s ∈ Icc 0 T,
      (∀ t ∈ Ico 0 s, ∀ j, dist ((θ t).1 j, (θ t).2 j) ((θ 0).1 j, (θ 0).2 j) ≤ D) →
      ∀ t ∈ Icc 0 s, ‖r t‖ ^ 2 ≤ ‖r 0‖ ^ 2 * Real.exp (-(ρ * t)) ∧
        ∀ j, dist ((θ t).1 j, (θ t).2 j) ((θ 0).1 j, (θ 0).2 j) ≤ Mmov := by
    intro s hs hmove
    have hIco : Ico 0 s ⊆ Ico 0 T := Ico_subset_Ico_right hs.2
    have hIcc : Icc 0 s ⊆ Icc 0 T := Icc_subset_Icc_right hs.2
    -- Output weights stay bounded by `2`.
    have ha : ∀ t ∈ Ico 0 s, ∀ j, |(θ t).1 j| ≤ 2 := by
      intro t ht j
      have h1 : dist ((θ t).1 j) ((θ 0).1 j) ≤ D :=
        (le_max_left _ _).trans (hmove t ht j)
      rw [Real.dist_eq] at h1
      have := abs_sub_abs_le_abs_sub ((θ t).1 j) ((θ 0).1 j)
      linarith [ha₀ j]
    have ha₀' : ∀ j, |(θ 0).1 j| ≤ 2 := fun j => (ha₀ j).trans (by norm_num)
    -- Coercivity along the trajectory.
    have hcoer : ∀ t ∈ Ico 0 s,
        (ρ / 2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤
          fullTrainingKernel σ (deriv σ) b (θ t) xs := by
      intro t ht
      have hsmall : (n : ℝ) *
          (2 * M * ((Real.toNNReal M' : NNReal) : ℝ) * X + 2 * 2 * M' ^ 2 * X ^ 2
            + 2 * 2 ^ 2 * M' * (Lσ' : ℝ) * X * X ^ 2) * D ≤ ρ / 2 := by
        rw [hLσ]; exact hDsmall
      exact LTFP.coercivity_preserved_under_param_drift σ (deriv σ) hσ_lip hσ'_lip hM hM'
        hσ_bdd hσ'_bdd b xs (sq_nonneg X) hX0 hG hX (by norm_num) (ha t ht) ha₀' D
        hDnn
        (hmove t ht) hρ (fullTrainingKernel_isHermitian _ _ _ _ _)
        (fullTrainingKernel_isHermitian _ _ _ _ _) hK₀ hsmall
    -- Grönwall decay on `[0, s]`.
    have hsq : ∀ t ∈ Icc 0 s, ‖r t‖ ^ 2 ≤ ‖r 0‖ ^ 2 * Real.exp (-(ρ * t)) := by
      have h := sq_norm_le_of_hasDerivWithinAt_neg_coercive r
        (fun t => fullTrainingKernel σ (deriv σ) b (θ t) xs) s (ρ / 2)
        (continuousOn_residualFullNet σ hσ.continuous b y xs θ _ (hθ_cont.mono hIcc))
        (fun t ht => hasDerivWithinAt_residualFullNet σ hσ b y xs hm θ _ t
          (hθ_der t (hIco ht)))
        (fun t ht => inner_toEuclideanLin_ge_of_loewner (hcoer t ht) (r t))
      intro t ht
      have := h t ht
      rwa [show 2 * (ρ / 2) * t = ρ * t by ring] at this
    -- Norm decay with the envelope `R₀`.
    have hnorm : ∀ t ∈ Icc 0 s, ‖r t‖ ≤ R₀ * Real.exp (-(ρ / 2 * t)) := by
      intro t ht
      have h1 := hsq t ht
      have h2 : ‖r 0‖ ^ 2 * Real.exp (-(ρ * t)) ≤ (R₀ * Real.exp (-(ρ / 2 * t))) ^ 2 := by
        rw [mul_pow, ← Real.exp_nat_mul]
        rw [show ((2 : ℕ) : ℝ) * -(ρ / 2 * t) = -(ρ * t) by push_cast; ring]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hR₀ 2)
          (Real.exp_pos _).le
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1
        (h1.trans h2)
    -- Movement on `[0, s]`.
    have hmov := neuron_dist_le_of_deriv_exp_decay θ
      (fun t => gfFieldFullNet σ b y xs (θ t)) s (hθ_cont.mono hIcc)
      (fun t ht => hθ_der t (hIco ht)) hρ hK₀nn (by
        intro t ht j
        refine (gfFieldFullNet_neuron_norm_le σ b y xs (θ t) j hσ_bdd hσ'_bdd hX0 hX
          (ha t ht j)).trans ?_
        have hn := hnorm t (Ico_subset_Icc_self ht)
        have hc : 0 ≤ 1 / Real.sqrt m * (M + 2 * M' * X) := by positivity
        calc 1 / Real.sqrt m * (M + 2 * M' * X) * (Real.sqrt n * ‖r t‖)
            ≤ 1 / Real.sqrt m * (M + 2 * M' * X) *
                (Real.sqrt n * (R₀ * Real.exp (-(ρ / 2 * t)))) := by gcongr
          _ = K₀ * Real.exp (-(ρ / 2 * t)) := by rw [hK₀def]; ring)
    intro t ht
    exact ⟨hsq t ht, fun j => by rw [hMmovK]; exact hmov t ht j⟩
  -- First-exit argument.
  set f : Fin m → ℝ → ℝ :=
    fun j t => dist (neuronProj j (θ t)) (neuronProj j (θ 0)) with hf
  set A : Set ℝ := ⋃ j, Icc 0 T ∩ f j ⁻¹' Ici D with hA
  have hAclosed : IsClosed A := by
    refine isClosed_iUnion_of_finite fun j => ?_
    refine ContinuousOn.preimage_isClosed_of_isClosed ?_ isClosed_Icc isClosed_Ici
    exact continuous_dist.comp_continuousOn
      (((neuronProj j).continuous.comp_continuousOn hθ_cont).prodMk continuousOn_const)
  have hAempty : A = ∅ := by
    by_contra hne
    have hAne : A.Nonempty := Set.nonempty_iff_ne_empty.2 hne
    have hbdd : BddBelow A := ⟨0, fun t ht => by
      simp only [hA, mem_iUnion, mem_inter_iff] at ht
      obtain ⟨j, hj, _⟩ := ht
      exact hj.1⟩
    have hτ := hAclosed.csInf_mem hAne hbdd
    set τ := sInf A with hτdef
    simp only [hA, mem_iUnion, mem_inter_iff, mem_preimage, mem_Ici] at hτ
    obtain ⟨j₀, hτI, hτj⟩ := hτ
    have hbelow : ∀ t ∈ Ico 0 τ, ∀ j,
        dist ((θ t).1 j, (θ t).2 j) ((θ 0).1 j, (θ 0).2 j) ≤ D := by
      intro t ht j
      have hnot := notMem_of_lt_csInf ht.2 hbdd
      simp only [hA, mem_iUnion, mem_inter_iff, mem_preimage, mem_Ici, not_exists,
        not_and] at hnot
      have htI : t ∈ Icc 0 T := ⟨ht.1, ht.2.le.trans hτI.2⟩
      exact (not_le.1 (hnot j htI)).le
    have := (core τ hτI hbelow τ ⟨hτI.1, le_rfl⟩).2 j₀
    have hfj : f j₀ τ =
        dist ((θ τ).1 j₀, (θ τ).2 j₀) ((θ 0).1 j₀, (θ 0).2 j₀) := rfl
    linarith
  have hall : ∀ t ∈ Ico 0 T, ∀ j,
      dist ((θ t).1 j, (θ t).2 j) ((θ 0).1 j, (θ 0).2 j) ≤ D := by
    intro t ht j
    by_contra hlt
    have : t ∈ A := by
      simp only [hA, mem_iUnion, mem_inter_iff, mem_preimage, mem_Ici]
      exact ⟨j, Ico_subset_Icc_self ht, (not_le.1 hlt).le⟩
    rw [hAempty] at this
    exact this
  intro t ht
  by_cases hT : 0 ≤ T
  · exact core T ⟨hT, le_rfl⟩ hall t ht
  · exact absurd (ht.1.trans ht.2) hT

end ProbabilityTheory
