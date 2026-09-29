/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.NTKGradientFieldLipschitz
import LTFP.MathlibExt.Probability.NTKGradientFlowBootstrap
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall

/-!
# Existence and uniqueness of the gradient flow of the two-layer network

The gradient field `gfFieldFullNet` is only locally Lipschitz, so
Picard–Lindelöf does not directly give a solution on a prescribed interval
`[0, T]`. We compose the field with the radial retraction onto the closed unit
ball around the initialisation; the truncated field is globally Lipschitz and
bounded, so it has a solution on `[0, T]`. Under the width conditions of
`fullNet_gradient_flow_lazy_training`, a first-exit argument shows that this
solution never leaves the open unit ball, where the truncation is inactive.
Hence it is a genuine gradient-flow trajectory. Uniqueness follows from
Grönwall, since every trajectory stays in the unit ball.

## Main definitions

* `ballRetract x₀ R` — the radial retraction onto `closedBall x₀ R`.

## Main results

* `lipschitzWith_ballRetract` — the radial retraction is `2`-Lipschitz.
* `exists_hasDerivWithinAt_Icc_of_lipschitzWith` — global existence on
  `[0, T]` for a globally Lipschitz, bounded autonomous field.
* `exists_fullNet_gradient_flow` — existence of the gradient flow on `[0, T]`.
* `fullNet_gradient_flow_unique` — uniqueness of the gradient flow on `[0, T]`.
-/

namespace ProbabilityTheory

open BigOperators Metric Set Filter Topology LTFP
open scoped NNReal MatrixOrder

section Retract

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial retraction onto the closed ball `closedBall x₀ R`. -/
noncomputable def ballRetract (x₀ : E) (R : ℝ) (x : E) : E :=
  x₀ + min 1 (R / ‖x - x₀‖) • (x - x₀)

theorem ballRetract_of_norm_le {x₀ x : E} {R : ℝ} (h : ‖x - x₀‖ ≤ R) :
    ballRetract x₀ R x = x := by
  unfold ballRetract
  rcases (norm_nonneg (x - x₀)).eq_or_lt with h0 | h0
  · have hx : x = x₀ := sub_eq_zero.1 (norm_eq_zero.1 h0.symm)
    subst hx; simp
  · rw [min_eq_left ((one_le_div h0).2 h), one_smul, add_sub_cancel]

theorem ballRetract_mem_closedBall {x₀ : E} {R : ℝ} (hR : 0 ≤ R) (x : E) :
    ballRetract x₀ R x ∈ closedBall x₀ R := by
  rw [mem_closedBall, dist_eq_norm, ballRetract, add_sub_cancel_left, norm_smul]
  rcases (norm_nonneg (x - x₀)).eq_or_lt with h0 | h0
  · rw [← h0, mul_zero]; exact hR
  · rw [Real.norm_of_nonneg (le_min zero_le_one (by positivity))]
    calc min 1 (R / ‖x - x₀‖) * ‖x - x₀‖ ≤ R / ‖x - x₀‖ * ‖x - x₀‖ := by
          gcongr; exact min_le_right _ _
      _ = R := div_mul_cancel₀ _ h0.ne'

/-- Mixed case: `‖u‖ ≤ R < ‖v‖`. -/
private theorem radial_mixed {R : ℝ} {u v : E} (hu : ‖u‖ ≤ R) (hv : R < ‖v‖) :
    ‖u - (R / ‖v‖) • v‖ ≤ 2 * ‖u - v‖ := by
  have hv0 : 0 < ‖v‖ := (norm_nonneg u).trans_lt (hu.trans_lt hv)
  have h1 : ‖v - (R / ‖v‖) • v‖ = ‖v‖ - R := by
    rw [show v - (R / ‖v‖) • v = (1 - R / ‖v‖) • v by rw [sub_smul, one_smul], norm_smul,
      Real.norm_of_nonneg (sub_nonneg.2 ((div_le_one hv0).2 hv.le)), sub_mul, one_mul,
      div_mul_cancel₀ _ hv0.ne']
  have h2 : ‖v‖ - ‖u‖ ≤ ‖u - v‖ := by
    rw [norm_sub_rev]; exact norm_sub_norm_le v u
  calc ‖u - (R / ‖v‖) • v‖ ≤ ‖u - v‖ + ‖v - (R / ‖v‖) • v‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * ‖u - v‖ := by rw [h1]; linarith

/-- Outer case: `R < ‖u‖` and `R < ‖v‖`. -/
private theorem radial_outer {R : ℝ} (hR : 0 ≤ R) {u v : E} (hu : R < ‖u‖) (hv : R < ‖v‖) :
    ‖(R / ‖u‖) • u - (R / ‖v‖) • v‖ ≤ 2 * ‖u - v‖ := by
  have hu0 : 0 < ‖u‖ := hR.trans_lt hu
  have hv0 : 0 < ‖v‖ := hR.trans_lt hv
  have hdec : (R / ‖u‖) • u - (R / ‖v‖) • v = (R / ‖u‖) • (u - (‖u‖ / ‖v‖) • v) := by
    rw [smul_sub, smul_smul]
    congr 2
    field_simp
  have h1 : ‖v - (‖u‖ / ‖v‖) • v‖ = |‖v‖ - ‖u‖| := by
    rw [show v - (‖u‖ / ‖v‖) • v = (1 - ‖u‖ / ‖v‖) • v by rw [sub_smul, one_smul], norm_smul,
      Real.norm_eq_abs, ← abs_of_pos hv0, ← abs_mul, abs_of_pos hv0, sub_mul, one_mul,
      div_mul_cancel₀ _ hv0.ne']
  have h2 : |‖v‖ - ‖u‖| ≤ ‖u - v‖ := by
    rw [norm_sub_rev]; exact abs_norm_sub_norm_le v u
  have hc : R / ‖u‖ ≤ 1 := (div_le_one hu0).2 hu.le
  have hc0 : 0 ≤ R / ‖u‖ := by positivity
  rw [hdec, norm_smul, Real.norm_of_nonneg hc0]
  calc R / ‖u‖ * ‖u - (‖u‖ / ‖v‖) • v‖ ≤ 1 * ‖u - (‖u‖ / ‖v‖) • v‖ := by gcongr
    _ ≤ ‖u - v‖ + ‖v - (‖u‖ / ‖v‖) • v‖ := by
        rw [one_mul]; exact norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ 2 * ‖u - v‖ := by rw [h1]; linarith

/-- The radial scaling `v ↦ min 1 (R / ‖v‖) • v` in the regime `R < ‖v‖`. -/
private theorem radial_of_lt {R : ℝ} {v : E} (hv : R < ‖v‖) (hR : 0 ≤ R) :
    min 1 (R / ‖v‖) • v = (R / ‖v‖) • v := by
  rw [min_eq_right ((div_le_one (hR.trans_lt hv)).2 hv.le)]

private theorem radial_of_le {R : ℝ} {v : E} (hv : ‖v‖ ≤ R) :
    min 1 (R / ‖v‖) • v = v := by
  simpa [ballRetract] using ballRetract_of_norm_le (x₀ := (0 : E)) (x := v) (R := R)
    (by simpa using hv)

/-- **The radial retraction is `2`-Lipschitz.** -/
theorem lipschitzWith_ballRetract (x₀ : E) {R : ℝ} (hR : 0 ≤ R) :
    LipschitzWith 2 (ballRetract x₀ R) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [dist_eq_norm, dist_eq_norm, ballRetract, ballRetract, add_sub_add_left_eq_sub,
    show x - y = (x - x₀) - (y - x₀) by abel]
  set u := x - x₀
  set v := y - x₀
  push_cast
  rcases le_or_gt ‖u‖ R with hu | hu <;> rcases le_or_gt ‖v‖ R with hv | hv
  · rw [radial_of_le hu, radial_of_le hv]
    linarith [norm_nonneg (u - v)]
  · rw [radial_of_le hu, radial_of_lt hv hR]; exact radial_mixed hu hv
  · rw [radial_of_lt hu hR, radial_of_le hv, norm_sub_rev, norm_sub_rev u]
    exact radial_mixed hv hu
  · rw [radial_of_lt hu hR, radial_of_lt hv hR]; exact radial_outer hR hu hv

end Retract

section GlobalExistence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Global existence on `[0, T]`** for an autonomous field that is globally
Lipschitz and bounded (Picard–Lindelöf on a ball of radius `B T`). -/
theorem exists_hasDerivWithinAt_Icc_of_lipschitzWith {F : E → E} {K : ℝ≥0}
    (hF : LipschitzWith K F) {B : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) (x₀ : E) {T : ℝ} (hT : 0 ≤ T) :
    ∃ α : ℝ → E, α 0 = x₀ ∧
      ∀ t ∈ Icc 0 T, HasDerivWithinAt α (F (α t)) (Icc 0 T) t := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB x₀)
  have hpl : IsPicardLindelof (fun _ => F) (tmin := 0) (tmax := T)
      ⟨0, left_mem_Icc.2 hT⟩ x₀ (B * T).toNNReal 0 B.toNNReal K := by
    refine IsPicardLindelof.of_time_independent (fun x _ => ?_) hF.lipschitzOnWith ?_
    · rw [Real.coe_toNNReal _ hB0]; exact hB x
    · rw [Real.coe_toNNReal _ hB0, Real.coe_toNNReal _ (mul_nonneg hB0 hT)]
      simp [max_eq_left hT]
  obtain ⟨α, h0, hα⟩ := IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ hpl
  exact ⟨α, h0, hα⟩

end GlobalExistence

/-- A derivative within `Icc a b` at `t ∈ Ico a b` is also a derivative within
`Ici t`. -/
theorem hasDerivWithinAt_Ici_of_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {α : ℝ → E} {α' : E} {a b t : ℝ} (h : HasDerivWithinAt α α' (Icc a b) t)
    (ht : t ∈ Ico a b) : HasDerivWithinAt α α' (Ici t) t :=
  h.mono_of_mem_nhdsWithin (mem_of_superset (Icc_mem_nhdsGE ht.2)
    (Icc_subset_Icc_left ht.1))

variable {d n m : ℕ}

/-- If every neuron has moved by at most `c ≥ 0`, the sup-norm distance in
parameter space is at most `c`. -/
theorem norm_sub_le_of_neuron_dist_le {θ θ' : Param d m} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ j, dist (θ.1 j, θ.2 j) (θ'.1 j, θ'.2 j) ≤ c) : ‖θ - θ'‖ ≤ c := by
  rw [← dist_eq_norm, Prod.dist_eq]
  refine max_le ((dist_pi_le_iff hc).2 fun j => ?_) ((dist_pi_le_iff hc).2 fun j => ?_)
  · exact (le_max_left _ _).trans (by simpa [Prod.dist_eq] using h j)
  · exact (le_max_right _ _).trans (by simpa [Prod.dist_eq] using h j)

/-- Nonnegativity of the per-neuron movement budget. -/
theorem gfMovementBound_nonneg {ρ M M' X R₀ : ℝ} (hρ : 0 < ρ) (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (hX : 0 ≤ X) (hR₀ : 0 ≤ R₀) : 0 ≤ gfMovementBound n m ρ M M' X R₀ := by
  unfold gfMovementBound; positivity

/-- A bounded-derivative activation is Lipschitz. -/
theorem lipschitzWith_of_abs_deriv_le {σ : ℝ → ℝ} (hσ : Differentiable ℝ σ) {M' : ℝ}
    (hσ'_bdd : ∀ z, |deriv σ z| ≤ M') : LipschitzWith (Real.toNNReal M') σ := by
  refine lipschitzWith_of_nnnorm_deriv_le hσ fun z => ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]
  exact (hσ'_bdd z).trans (Real.le_coe_toNNReal M')

/-- **Existence of the gradient flow of the two-layer network on `[0, T]`.**

Under the hypotheses of `fullNet_gradient_flow_lazy_training` (with the
trajectory replaced by its initial point `θ₀`), for every `T` there is a
gradient-flow trajectory `θ` with `θ 0 = θ₀`, continuous on `[0, T]`, with
derivative `gfFieldFullNet (θ t)` within `[0, T]` at every `t ∈ [0, T]` (hence
right derivative on `[0, T)`), and staying in the unit ball around `θ₀`. -/
theorem exists_fullNet_gradient_flow
    [Nonempty (Fin n)] (hm : 0 < m)
    (σ : ℝ → ℝ) (hσ : Differentiable ℝ σ)
    {M M' : ℝ} (hσ_bdd : ∀ z, |σ z| ≤ M) (hσ'_bdd : ∀ z, |deriv σ z| ≤ M')
    {Lσ' : NNReal} (hσ'_lip : LipschitzWith Lσ' (deriv σ))
    (b : Fin m → ℝ) (y : Fin n → ℝ) (xs : Fin n → EuclideanSpace ℝ (Fin d))
    {X : ℝ} (hX : ∀ i, ‖xs i‖ ≤ X)
    (θ₀ : Param d m) (ha₀ : ∀ j, |θ₀.1 j| ≤ 1)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hK₀ : ρ • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ fullTrainingKernel σ (deriv σ) b θ₀ xs)
    {R₀ : ℝ} (hR₀ : ‖residualFullNet σ b y xs θ₀‖ ≤ R₀)
    (hW₁ : gfMovementBound n m ρ M M' X R₀ < 1)
    (hW₂ : (n : ℝ) * gfDriftConst M M' Lσ' X * gfMovementBound n m ρ M M' X R₀ < ρ / 2)
    (T : ℝ) :
    ∃ θ : ℝ → Param d m, θ 0 = θ₀ ∧ ContinuousOn θ (Icc 0 T) ∧
      (∀ t ∈ Icc 0 T, HasDerivWithinAt θ (gfFieldFullNet σ b y xs (θ t)) (Icc 0 T) t) ∧
      (∀ t ∈ Ico 0 T, HasDerivWithinAt θ (gfFieldFullNet σ b y xs (θ t)) (Ici t) t) ∧
      ∀ t ∈ Icc 0 T, ‖θ t - θ₀‖ < 1 := by
  rcases lt_or_ge T 0 with hT | hT
  · refine ⟨fun _ => θ₀, rfl, ?_, ?_, ?_, ?_⟩ <;> simp [Icc_eq_empty_of_lt hT,
      Ico_eq_empty_of_le hT.le]
  set G := gfFieldFullNet σ b y xs with hG
  have hM : 0 ≤ M := (abs_nonneg _).trans (hσ_bdd 0)
  have hM' : 0 ≤ M' := (abs_nonneg _).trans (hσ'_bdd 0)
  have hX0 : 0 ≤ X := (norm_nonneg _).trans (hX (Classical.arbitrary _))
  have hR₀nn : 0 ≤ R₀ := (norm_nonneg _).trans hR₀
  have hMnn := gfMovementBound_nonneg (n := n) (m := m) hρ hM hM' hX0 hR₀nn
  have hσL := lipschitzWith_of_abs_deriv_le hσ hσ'_bdd
  -- Truncated field.
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_gfFieldFullNet_closedBall hσL hσ'_lip b y xs θ₀ 1
  obtain ⟨B, hB⟩ := exists_norm_le_gfFieldFullNet_closedBall hσL hσ'_lip b y xs θ₀ 1
  set P := ballRetract θ₀ (1 : ℝ) with hP
  have hPmem : ∀ x, P x ∈ closedBall θ₀ 1 := ballRetract_mem_closedBall zero_le_one
  have hFlip : LipschitzWith (K * 2) (G ∘ P) := by
    rw [← lipschitzOnWith_univ]
    exact hK.comp (lipschitzWith_ballRetract θ₀ zero_le_one).lipschitzOnWith
      (fun x _ => hPmem x)
  obtain ⟨α, hα0, hα⟩ := exists_hasDerivWithinAt_Icc_of_lipschitzWith hFlip
    (fun x => hB _ (hPmem x)) θ₀ hT
  have hαc : ContinuousOn α (Icc 0 T) := fun t ht => (hα t ht).continuousWithinAt
  have hPid : ∀ t, ‖α t - θ₀‖ ≤ 1 → (G ∘ P) (α t) = G (α t) := fun t h => by
    simp only [Function.comp_apply, hP, ballRetract_of_norm_le h]
  -- Bootstrap on `[0, s]` while the trajectory stays in the unit ball.
  have core : ∀ s ∈ Icc 0 T, (∀ t ∈ Ico 0 s, ‖α t - θ₀‖ ≤ 1) →
      ‖α s - θ₀‖ ≤ gfMovementBound n m ρ M M' X R₀ := by
    intro s hs hin
    have hder : ∀ t ∈ Ico 0 s, HasDerivWithinAt α (G (α t)) (Ici t) t := by
      intro t ht
      have htT : t ∈ Ico 0 T := ⟨ht.1, ht.2.trans_le hs.2⟩
      rw [← hPid t (hin t ht)]
      exact hasDerivWithinAt_Ici_of_Icc (hα t (Ico_subset_Icc_self htT)) htT
    have hmain := fullNet_gradient_flow_lazy_training hm σ hσ hσ_bdd hσ'_bdd hσ'_lip b y xs hX
      α (hαc.mono (Icc_subset_Icc_right hs.2)) hder (by rw [hα0]; exact ha₀) hρ
      (by rw [hα0]; exact hK₀) (by rw [hα0]; exact hR₀) hW₁ hW₂ s ⟨hs.1, le_rfl⟩
    rw [← hα0]
    exact norm_sub_le_of_neuron_dist_le hMnn hmain.2
  -- First exit from the unit ball.
  set A : Set ℝ := Icc 0 T ∩ (fun t => ‖α t - θ₀‖) ⁻¹' Ici 1 with hA
  have hAclosed : IsClosed A :=
    (hαc.sub continuousOn_const).norm.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hAempty : A = ∅ := by
    by_contra hne
    have hAne : A.Nonempty := nonempty_iff_ne_empty.2 hne
    have hbdd : BddBelow A := ⟨0, fun t ht => ht.1.1⟩
    have hτ := hAclosed.csInf_mem hAne hbdd
    have hbelow : ∀ t ∈ Ico 0 (sInf A), ‖α t - θ₀‖ ≤ 1 := by
      intro t ht
      have hnot := notMem_of_lt_csInf ht.2 hbdd
      have htI : t ∈ Icc 0 T := ⟨ht.1, ht.2.le.trans hτ.1.2⟩
      by_contra h
      exact hnot ⟨htI, (not_le.1 h).le⟩
    have h1 := core _ hτ.1 hbelow
    have h2 : (1 : ℝ) ≤ ‖α (sInf A) - θ₀‖ := hτ.2
    linarith
  have hin : ∀ t ∈ Icc 0 T, ‖α t - θ₀‖ < 1 := by
    intro t ht
    by_contra h
    have : t ∈ A := ⟨ht, not_lt.1 h⟩
    rw [hAempty] at this
    exact this
  have hderIcc : ∀ t ∈ Icc 0 T, HasDerivWithinAt α (G (α t)) (Icc 0 T) t := by
    intro t ht
    rw [← hPid t (hin t ht).le]
    exact hα t ht
  exact ⟨α, hα0, hαc, hderIcc,
    fun t ht => hasDerivWithinAt_Ici_of_Icc (hderIcc t (Ico_subset_Icc_self ht)) ht, hin⟩

/-- **Uniqueness of the gradient flow on `[0, T]`.** Under the hypotheses of
`fullNet_gradient_flow_lazy_training`, two gradient-flow trajectories on
`[0, T]` with the same initial point coincide on `[0, T]`. -/
theorem fullNet_gradient_flow_unique
    [Nonempty (Fin n)] (hm : 0 < m)
    (σ : ℝ → ℝ) (hσ : Differentiable ℝ σ)
    {M M' : ℝ} (hσ_bdd : ∀ z, |σ z| ≤ M) (hσ'_bdd : ∀ z, |deriv σ z| ≤ M')
    {Lσ' : NNReal} (hσ'_lip : LipschitzWith Lσ' (deriv σ))
    (b : Fin m → ℝ) (y : Fin n → ℝ) (xs : Fin n → EuclideanSpace ℝ (Fin d))
    {X : ℝ} (hX : ∀ i, ‖xs i‖ ≤ X)
    (θ₀ : Param d m) (ha₀ : ∀ j, |θ₀.1 j| ≤ 1)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hK₀ : ρ • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ fullTrainingKernel σ (deriv σ) b θ₀ xs)
    {R₀ : ℝ} (hR₀ : ‖residualFullNet σ b y xs θ₀‖ ≤ R₀)
    (hW₁ : gfMovementBound n m ρ M M' X R₀ < 1)
    (hW₂ : (n : ℝ) * gfDriftConst M M' Lσ' X * gfMovementBound n m ρ M M' X R₀ < ρ / 2)
    {T : ℝ} (θ θ' : ℝ → Param d m) (h0 : θ 0 = θ₀) (h0' : θ' 0 = θ₀)
    (hc : ContinuousOn θ (Icc 0 T)) (hc' : ContinuousOn θ' (Icc 0 T))
    (hd : ∀ t ∈ Ico 0 T, HasDerivWithinAt θ (gfFieldFullNet σ b y xs (θ t)) (Ici t) t)
    (hd' : ∀ t ∈ Ico 0 T, HasDerivWithinAt θ' (gfFieldFullNet σ b y xs (θ' t)) (Ici t) t) :
    EqOn θ θ' (Icc 0 T) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hσ_bdd 0)
  have hM' : 0 ≤ M' := (abs_nonneg _).trans (hσ'_bdd 0)
  have hX0 : 0 ≤ X := (norm_nonneg _).trans (hX (Classical.arbitrary _))
  have hR₀nn : 0 ≤ R₀ := (norm_nonneg _).trans hR₀
  have hMnn := gfMovementBound_nonneg (n := n) (m := m) hρ hM hM' hX0 hR₀nn
  obtain ⟨K, hK⟩ := exists_lipschitzOnWith_gfFieldFullNet_closedBall
    (lipschitzWith_of_abs_deriv_le hσ hσ'_bdd) hσ'_lip b y xs θ₀ 1
  have hball : ∀ φ : ℝ → Param d m, φ 0 = θ₀ → ContinuousOn φ (Icc 0 T) →
      (∀ t ∈ Ico 0 T, HasDerivWithinAt φ (gfFieldFullNet σ b y xs (φ t)) (Ici t) t) →
      ∀ t ∈ Ico 0 T, φ t ∈ closedBall θ₀ 1 := by
    intro φ hφ0 hφc hφd t ht
    subst hφ0
    have hmain := fullNet_gradient_flow_lazy_training hm σ hσ hσ_bdd hσ'_bdd hσ'_lip b y xs hX
      φ hφc hφd ha₀ hρ hK₀ hR₀ hW₁ hW₂ t (Ico_subset_Icc_self ht)
    rw [mem_closedBall, dist_eq_norm]
    exact (norm_sub_le_of_neuron_dist_le hMnn hmain.2).trans hW₁.le
  subst h0
  exact ODE_solution_unique_of_mem_Icc_right (v := fun _ => gfFieldFullNet σ b y xs)
    (s := fun _ => closedBall (θ 0) 1) (fun _ _ => hK) hc hd
    (hball θ rfl hc hd) hc' hd' (hball θ' h0' hc' hd') h0'.symm

end ProbabilityTheory
