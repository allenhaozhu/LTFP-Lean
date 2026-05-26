/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Continuity

/-!
# Bootstrap closure: continuous trajectories satisfying a feedback inequality

**R4 NTK Part 1.C — clopen bootstrap closure of the lazy-training loop.**

The non-parametric NTK lazy-training carrier
(`ntk_lazy_training_carrier_from_total_movement`) consumes a uniform
*total* movement hypothesis `‖θ t - θ 0‖ ≤ Δ` for all `t ≥ 0`. The
parametric movement bound `bootstrap_radius_uniform_movement` produces
this conclusion, but it consumes an *a priori* exponential gradient
bound — which itself depends on the kernel coercivity along the
trajectory, which in turn depends on the movement bound. This circle
is the standard chicken-and-egg of NTK analysis.

The classical resolution (Du et al., Allen-Zhu et al.) is the clopen
bootstrap argument:

* The set `S = {T ≥ 0 | ∀ s ∈ [0, T], ‖θ s - θ 0‖ < r₀}` is open
  (continuity of `θ` propagates the strict inequality).
* `S` is closed under the natural ordering (the feedback inequality
  `‖θ t - θ 0‖ ≤ M < r₀` upgrades to a strict bound that survives
  passage to the supremum).
* `S` is non-empty (contains a neighborhood of `0`).
* Hence `S` equals the entire half-line `[0, ∞)`, and the trajectory
  never escapes the ball.

This module proves the abstract closure lemma — independent of the
NTK details. It is the missing piece that completes the non-parametric
NTK lazy-training pipeline.

## Main result

* `bootstrap_trajectory_movement_closure` — abstract bootstrap closure.
  Given a continuous `θ : ℝ → E`, a self-consistent feedback bound
  `M < r₀`, and the property that "movement < r₀ on `[0, t]` implies
  movement at `t` is ≤ `M`", the trajectory satisfies `‖θ t - θ 0‖ ≤ M`
  uniformly for `t ≥ 0`.

The hypothesis `θ 0 ∈ ball ∘ M` plus the feedback property is exactly
what `coercivity_preserved_under_param_drift` + `bootstrap_radius_uniform_movement`
deliver in the NTK setting once we strip away the kernel-specific
content.

## References

* Bach (2024) *Learning Theory from First Principles*, §12 (NTK lazy
  training).
* Du, Lee, Li, Wang, Zhai (2019), *Gradient Descent Finds Global Minima
  of Deep Neural Networks*.
* Allen-Zhu, Li, Song (2019), *A Convergence Theory for Deep Learning
  via Over-Parameterization*.
* `LTFP.MathlibExt.Probability.NTKBootstrapRadius` — the (parametric)
  movement bound this closure complements.
-/

namespace LTFP.MathlibExt.Probability

open Set Topology Filter

/-- **Bootstrap closure (abstract form).**

Let `θ : ℝ → E` be continuous on `[0, ∞)`. Suppose `M < r₀` are
non-negative reals such that:

* `θ 0 = 0` shift (we phrase movement as `‖θ t - θ 0‖`), and `M ≥ 0`;
* `M < r₀` (strict — the feedback gap);
* (feedback property) for every `T ≥ 0`, if `‖θ s - θ 0‖ < r₀` for
  every `s ∈ [0, T]`, then `‖θ T - θ 0‖ ≤ M`.

Then `‖θ t - θ 0‖ ≤ M` for every `t ≥ 0`.

**Proof idea.** Let `Ts := sSup {T ≥ 0 | ∀ s ∈ [0, T], ‖θ s - θ 0‖ < r₀}`.
By continuity at `0` and the strict gap `0 < r₀`, the set is non-empty
and contains a small initial interval. By continuity at `Ts`, the strict
movement bound propagates to a small open neighborhood — unless `Ts` is
already the supremum of `ℝ`, i.e., unbounded. We show by contradiction
that `Ts` *must* be unbounded: at any candidate finite `Ts`, the
feedback gives `‖θ Ts - θ 0‖ ≤ M < r₀`, contradicting that `Ts` is the
supremum past which the strict inequality fails.

Equivalently — and this is what we formalize below — we show directly
that the set `{t ≥ 0 | ‖θ t - θ 0‖ ≤ M}` equals `[0, ∞)` by ruling out
the existence of any `t₀ ≥ 0` with `‖θ t₀ - θ 0‖ > M`. -/
theorem bootstrap_trajectory_movement_closure
    {E : Type*} [NormedAddCommGroup E]
    (θ : ℝ → E)
    (hθ_cont : Continuous θ)
    {M r₀ : ℝ} (hM_nn : 0 ≤ M) (hMr : M < r₀)
    (h_feedback : ∀ T : ℝ, 0 ≤ T →
      (∀ s : ℝ, 0 ≤ s → s ≤ T → ‖θ s - θ 0‖ < r₀) → ‖θ T - θ 0‖ ≤ M) :
    ∀ t : ℝ, 0 ≤ t → ‖θ t - θ 0‖ ≤ M := by
  -- We argue by contradiction: assume there is some `t₀ ≥ 0` with `‖θ t₀ - θ 0‖ > M`.
  -- The continuous function `f(s) := ‖θ s - θ 0‖` satisfies `f 0 = 0 ≤ M`, so
  -- by the intermediate value theorem there is a smallest `t* ∈ [0, t₀]` at which
  -- `f t* = r₀`-ish — but the feedback hypothesis forces `f t* ≤ M < r₀`, a contradiction.
  -- We make this rigorous via the supremum of `{s ≤ t₀ | f s ≤ M}`.
  by_contra h_neg
  push_neg at h_neg
  obtain ⟨t₀, ht₀_nn, ht₀_lt⟩ := h_neg
  -- `f s := ‖θ s - θ 0‖` is continuous on ℝ.
  set f : ℝ → ℝ := fun s => ‖θ s - θ 0‖ with hf_def
  have hf_cont : Continuous f := by
    show Continuous (fun s => ‖θ s - θ 0‖)
    -- `‖θ s - θ 0‖ = dist (θ s) (θ 0)`, and `dist` is jointly continuous.
    have h_eq : (fun s => ‖θ s - θ 0‖) = fun s => dist (θ s) (θ 0) := by
      funext s; rw [dist_eq_norm]
    rw [h_eq]
    exact hθ_cont.dist continuous_const
  -- `f 0 = 0`.
  have hf_zero : f 0 = 0 := by simp [f]
  -- Define the downward-closed witness set
  --   `S' := {T' ∈ [0, t₀] | ∀ u ∈ [0, T'], f u ≤ M}`.
  -- This is the "good times" set. We prove `S'` is closed (sequentially) and
  -- bounded, hence has a maximum `Ts`. We then rule out `Ts < t₀` by extending
  -- `Ts` slightly using continuity + the feedback hypothesis, contradicting
  -- maximality. The remaining case `Ts = t₀` immediately contradicts `f t₀ > M`.
  let S' : Set ℝ := {T' | 0 ≤ T' ∧ T' ≤ t₀ ∧ ∀ u ∈ Icc (0 : ℝ) T', f u ≤ M}
  have hS'_zero : (0 : ℝ) ∈ S' := by
    refine ⟨le_refl 0, ht₀_nn, ?_⟩
    intro u hu
    obtain ⟨hu1, hu2⟩ := hu
    have hu_eq : u = 0 := le_antisymm hu2 hu1
    rw [hu_eq, hf_zero]
    exact hM_nn
  have hS'_bdd : BddAbove S' := ⟨t₀, fun T' hT' => hT'.2.1⟩
  have hS'_nonempty : S'.Nonempty := ⟨0, hS'_zero⟩
  -- `S'` is downward-closed (and contains `0`), so it is an interval `[0, Ts]` or `[0, Ts)`.
  have hS'_downward : ∀ a b : ℝ, a ∈ S' → 0 ≤ b → b ≤ a → b ∈ S' := by
    intro a b ha hb_nn hba
    refine ⟨hb_nn, le_trans hba ha.2.1, ?_⟩
    intro u hu
    obtain ⟨hu1, hu2⟩ := hu
    exact ha.2.2 u ⟨hu1, le_trans hu2 hba⟩
  -- `S'` is closed in ℝ: see argument below.
  -- For each `u : ℝ`, the set `{T' | u ≤ T' → f u ≤ M}` is closed (it equals
  -- the union `{T' | T' < u} ∪ {T' | f u ≤ M}` which is closed if `f u ≤ M` (whole line)
  -- or open `{T' | T' < u}` if `f u > M`).
  -- The intersection structure suggests instead:
  -- `S' = [0, t₀] ∩ ⋂ u ≥ 0, ({T' | u ≤ T'} ⇒ f u ≤ M).complement`
  -- Equivalently: `T' ∈ S' ↔ ∀ u ∈ [0, T'], f u ≤ M`.
  -- The closedness of `S'` is the standard "set of `T` for which `∀ u ≤ T, P(u)` holds" lemma:
  -- a sequence `T'ₙ → Ts` with each `T'ₙ ∈ S'` gives, for any `u < Ts`, eventually `u ≤ T'ₙ` and
  -- hence `f u ≤ M`. At `u = Ts` itself, continuity of `f` gives `f Ts = lim f T'ₙ ≤ M`.
  have hS'_closed : IsClosed S' := by
    rw [← isSeqClosed_iff_isClosed]
    intro Tn T' hTn_mem hTn_lim
    refine ⟨?_, ?_, ?_⟩
    · -- `0 ≤ T'`: limit of nonneg sequence.
      exact ge_of_tendsto' hTn_lim (fun n => (hTn_mem n).1)
    · -- `T' ≤ t₀`.
      exact le_of_tendsto' hTn_lim (fun n => (hTn_mem n).2.1)
    · -- `∀ u ∈ [0, T'], f u ≤ M`.
      intro u hu
      obtain ⟨hu1, hu2⟩ := hu
      -- If `u < T'`, then `u ≤ T'ₙ` eventually (since `T'ₙ → T'`).
      -- If `u = T'`, use continuity: `f u = f T' = lim f T'ₙ` and `f T'ₙ ≤ M`.
      rcases lt_or_eq_of_le hu2 with hu_lt | hu_eq
      · -- `u < T'`: eventually `u ≤ T'ₙ` (since `T'ₙ → T'`).
        have h_event : ∀ᶠ n in atTop, u ≤ Tn n := by
          have := hTn_lim.eventually_const_lt hu_lt
          filter_upwards [this] with n hn using hn.le
        obtain ⟨N, hN⟩ := h_event.exists
        exact (hTn_mem N).2.2 u ⟨hu1, hN⟩
      · -- `u = T'`: continuity gives `f u = lim f T'ₙ ≤ M`.
        -- `f T'ₙ` is bounded by M (each `T'ₙ ∈ S'`, so `T'ₙ ∈ [0, T'ₙ]` and feedback gives `f T'ₙ ≤ M`).
        -- By continuity, `f T'ₙ → f T'`, so `f T' ≤ M`.
        -- `f u = f T'` because `u = T'`.
        have h_fcomp : Tendsto (fun n => f (Tn n)) atTop (𝓝 (f T')) :=
          (hf_cont.tendsto T').comp hTn_lim
        have h_le : ∀ n, f (Tn n) ≤ M := fun n =>
          (hTn_mem n).2.2 (Tn n) ⟨(hTn_mem n).1, le_refl _⟩
        have h_lim_le : f T' ≤ M := le_of_tendsto' h_fcomp h_le
        rw [hu_eq]
        exact h_lim_le
  -- Let `Ts := sSup S'`. We will show `Ts = t₀`, contradicting `f t₀ > M`.
  set Ts := sSup S' with hTs_def
  have hTs_mem : Ts ∈ S' := hS'_closed.csSup_mem hS'_nonempty hS'_bdd
  have hTs_nn : 0 ≤ Ts := hTs_mem.1
  have hTs_le_t0 : Ts ≤ t₀ := hTs_mem.2.1
  have hTs_prop : ∀ u ∈ Icc (0 : ℝ) Ts, f u ≤ M := hTs_mem.2.2
  -- In particular, `f Ts ≤ M`, so `f Ts < r₀`.
  have hf_Ts_le_M : f Ts ≤ M := hTs_prop Ts ⟨hTs_nn, le_refl Ts⟩
  have hf_Ts_lt_r0 : f Ts < r₀ := lt_of_le_of_lt hf_Ts_le_M hMr
  -- Case split: `Ts < t₀` vs `Ts = t₀`.
  rcases lt_or_eq_of_le hTs_le_t0 with hTs_lt | hTs_eq
  · -- `Ts < t₀`: we use continuity of `f` at `Ts` to extend `S'` past `Ts`,
    -- contradicting the supremum property.
    -- By continuity, since `f Ts < r₀`, there exists `δ > 0` such that
    -- `f s < r₀` for all `s ∈ [Ts, Ts + δ]`. Combined with `hTs_prop`, we have
    -- `f u < r₀` for all `u ∈ [0, Ts + δ]` (subject to `Ts + δ ≤ t₀`).
    -- Then the feedback property gives `f (Ts + δ) ≤ M`, but more importantly
    -- this needs to hold for ALL `s ∈ [Ts, Ts + δ]`.
    -- For each such `s ≤ Ts + δ`, we have `f u < r₀` for all `u ∈ [0, s]`, so
    -- `f s ≤ M`. Hence `Ts + δ ∈ S'`, contradicting `Ts = sSup S'`.
    --
    -- Continuity at `Ts`: `f Ts < r₀` gives a neighborhood `U` of `Ts` with `f s < r₀` on `U`.
    have hUcont : ∀ᶠ s in 𝓝 Ts, f s < r₀ :=
      (hf_cont.continuousAt).preimage_mem_nhds (IsOpen.mem_nhds isOpen_Iio hf_Ts_lt_r0)
    obtain ⟨ε, hε_pos, hε_sub⟩ := Metric.eventually_nhds_iff.mp hUcont
    -- For each `s ∈ Ioo (Ts - ε) (Ts + ε)`, `f s < r₀`.
    -- Pick `δ := min (ε/2) (t₀ - Ts) > 0`.
    have hgap_pos : 0 < t₀ - Ts := sub_pos.mpr hTs_lt
    let δ := min (ε / 2) (t₀ - Ts)
    have hδ_pos : 0 < δ := lt_min (by linarith) hgap_pos
    have hδ_le_ε2 : δ ≤ ε / 2 := min_le_left _ _
    have hδ_le_gap : δ ≤ t₀ - Ts := min_le_right _ _
    -- Then `Ts + δ ∈ [Ts, t₀]` and for every `s ∈ [Ts, Ts + δ]`, `|s - Ts| ≤ δ < ε`, so `f s < r₀`.
    have h_extend : ∀ s ∈ Icc Ts (Ts + δ), f s < r₀ := by
      intro s hs
      apply hε_sub
      simp only [Real.dist_eq, abs_lt]
      constructor
      · linarith [hs.1]
      · have : s ≤ Ts + δ := hs.2
        linarith
    -- Now show `Ts + δ ∈ S'`.
    have hTsδ_mem : Ts + δ ∈ S' := by
      refine ⟨by linarith, by linarith, ?_⟩
      intro u hu
      obtain ⟨hu1, hu2⟩ := hu
      -- Need `f u ≤ M`.
      -- Case 1: `u ≤ Ts`. Then by `hTs_prop`, `f u ≤ M`. ✓
      -- Case 2: `Ts < u ≤ Ts + δ`. Then we use feedback at `u`:
      --   For all `v ∈ [0, u]`, `f v < r₀` (split: `v ≤ Ts` uses `hTs_prop` + `M < r₀`;
      --                                       `Ts < v ≤ u ≤ Ts + δ` uses `h_extend`).
      --   So feedback gives `f u ≤ M`.
      by_cases h_uTs : u ≤ Ts
      · exact hTs_prop u ⟨hu1, h_uTs⟩
      · push_neg at h_uTs
        -- `Ts < u ≤ Ts + δ`. Apply feedback hypothesis at `u`.
        have hu_nn : 0 ≤ u := hu1
        have h_strict : ∀ v : ℝ, 0 ≤ v → v ≤ u → f v < r₀ := by
          intro v hv_nn hv_le_u
          by_cases h_vTs : v ≤ Ts
          · -- `v ∈ [0, Ts]`, so `f v ≤ M < r₀`.
            have : f v ≤ M := hTs_prop v ⟨hv_nn, h_vTs⟩
            linarith
          · push_neg at h_vTs
            -- `Ts < v ≤ u ≤ Ts + δ`, so `v ∈ [Ts, Ts + δ]`, hence `f v < r₀`.
            apply h_extend v
            refine ⟨h_vTs.le, ?_⟩
            linarith
        exact h_feedback u hu_nn h_strict
    -- But `Ts + δ > Ts = sSup S'`, contradiction with `Ts + δ ∈ S'`.
    have : Ts + δ ≤ Ts := le_csSup hS'_bdd hTsδ_mem
    linarith
  · -- `Ts = t₀`. But `hTs_prop t₀` gives `f t₀ ≤ M`, contradicting `f t₀ > M`.
    have h_t0 : f t₀ ≤ M := by
      have h := hTs_prop t₀ ⟨ht₀_nn, by rw [hTs_eq]⟩
      exact h
    have h_ft0 : f t₀ > M := by show ‖θ t₀ - θ 0‖ > M; exact ht₀_lt
    linarith

/-- **Bootstrap closure — packaged for NTK lazy-training use.**

This is a re-phrasing of `bootstrap_trajectory_movement_closure` more
convenient for the NTK pipeline. The hypotheses are:

* a continuous parameter trajectory `θ : ℝ → E`;
* a small-residual constant `M < r₀`;
* a *trajectory-restricted* feedback bound: for every `T ≥ 0`, if the
  parameter has stayed within radius `r₀` of `θ 0` on `[0, T]`, then the
  movement at time `T` is at most `M`.

In the NTK setting, the feedback bound is precisely what
`bootstrap_radius_uniform_movement` produces, where `M = √Kmax · 2‖r(0)‖/(μ/2)`
is the conservative envelope and `r₀` is the radius required by
`coercivity_preserved_under_param_drift`. The hypothesis "movement < r₀
on `[0, T]` implies coercivity floor `(μ/2)·I ≤ K(θ(t))` on `[0, T]`"
fuels Grönwall residual decay, which feeds back into the movement bound.

This corollary uses the abstract closure to produce the unconditional
uniform bound `‖θ t - θ 0‖ ≤ M` for *every* `t ≥ 0` — the missing piece
needed by `ntk_lazy_training_carrier_from_total_movement`. -/
theorem bootstrap_uniform_movement_envelope
    {E : Type*} [NormedAddCommGroup E]
    (θ : ℝ → E) (hθ_cont : Continuous θ)
    {M r₀ : ℝ} (hM_nn : 0 ≤ M) (hMr : M < r₀)
    (h_feedback : ∀ T : ℝ, 0 ≤ T →
      (∀ s : ℝ, 0 ≤ s → s ≤ T → ‖θ s - θ 0‖ < r₀) → ‖θ T - θ 0‖ ≤ M) :
    ∀ t : ℝ, 0 ≤ t → ‖θ t - θ 0‖ ≤ M :=
  bootstrap_trajectory_movement_closure θ hθ_cont hM_nn hMr h_feedback

end LTFP.MathlibExt.Probability
