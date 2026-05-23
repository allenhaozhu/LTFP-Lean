/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.Cover
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fintype.BigOperators
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

/-!
# Explicit `(2√2 B / δ + 1)²` covering-number bound for the Euclidean 2-ball

The (external) `δ`-covering number of the closed Euclidean 2-ball
`Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) B` is bounded by
`(⌈2 * √2 * B / δ⌉₊ + 1) ^ 2`. This is the concrete `d = 2` slice of
the classical `(C * B / δ) ^ d` bound used in the B8 N6 wide-network
generalization carrier; the existing `linear_class_covering_number_lt_top`
only certifies finiteness, and `covering_number_real_interval` provides
the `d = 1` case at `b08c562`.

We use the uniform `(N+1)²`-point grid

  `g (k, j) := toLp 2 ![f k, f j]`

where `f k := -B + (k : ℝ) / N * (2 * B)` and `N := ⌈2 * √2 * B / δ⌉₊`,
so that per-coordinate spacing `2 * B / N ≤ δ / √2`. The Pythagorean
sum then yields `dist (x) (g (k, j)) ≤ √((δ/√2)² + (δ/√2)²) = δ` for
the closest grid point to any `x` in the ball. Note the bound is for
the *external* covering number (`Metric.externalCoveringNumber`) — the
grid points include corners of the bounding square that may lie
slightly outside the L²-ball.
-/

open scoped NNReal ENNReal

namespace LTFP

/-- The δ-external covering number of the closed Euclidean 2-ball of
radius `B` is at most `(⌈2 * √2 * B / δ⌉₊ + 1) ^ 2`. Concrete `d = 2`
instance of the deferred `(C * B / δ) ^ d` bound used by B8 N6
(wide-network generalization).

**Note (standalone result).** This theorem is *not* called by the final
wide-network B8 N6 closure chain in `WideNetworkDudley.lean`. That chain
threads through the general `d`-dimensional bound
`covering_number_euclidean_ball` below, which is valid for any `d ≥ 1`
and therefore subsumes both the `d = 1` (`covering_number_real_interval`
in `CoveringNumberReal.lean`) and `d = 2` cases. This `d = 2` ball
bound is kept as a standalone reference / sanity check — it is the
smallest non-trivial multi-dimensional instance and was useful for
debugging the Pythagorean spacing argument before generalizing to
arbitrary `d`. -/
theorem covering_number_euclidean_two_ball
    (B : ℝ) (δ : ℝ≥0) (hB : 0 ≤ B) (hδ : δ ≠ 0) :
    Metric.externalCoveringNumber δ
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) B) ≤
      ((⌈2 * Real.sqrt 2 * B / (δ : ℝ)⌉₊ + 1 : ℕ) ^ 2 : ℕ) := by
  classical
  set N : ℕ := ⌈2 * Real.sqrt 2 * B / (δ : ℝ)⌉₊ with hN_def
  set f : ℕ → ℝ := fun k => -B + (k : ℝ) / (N : ℝ) * (2 * B) with hf_def
  -- Grid: image of (range (N+1)) ×ˢ (range (N+1)) under the obvious
  -- product-of-1D-grids map.
  set g : ℕ × ℕ → EuclideanSpace ℝ (Fin 2) := fun p =>
    (WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then f p.1 else f p.2))
    with hg_def
  set C : Finset (EuclideanSpace ℝ (Fin 2)) :=
    ((Finset.range (N + 1)).product (Finset.range (N + 1))).image g
    with hC_def
  -- Positivity facts.
  have hδ_pos : (0 : ℝ) < (δ : ℝ) := by
    have : (0 : ℝ≥0) < δ := pos_iff_ne_zero.mpr hδ
    exact_mod_cast this
  have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsqrt2_nonneg : (0 : ℝ) ≤ Real.sqrt 2 := hsqrt2_pos.le
  have h2B_nonneg : (0 : ℝ) ≤ 2 * B := by linarith
  -- Key arithmetic: N · δ ≥ 2 · √2 · B.
  have hN_ge_ratio : (2 * Real.sqrt 2 * B) / (δ : ℝ) ≤ (N : ℝ) := by
    rw [hN_def]; exact_mod_cast Nat.le_ceil _
  -- Helper: f k ∈ [-B, B] when 0 ≤ k ≤ N.
  have hf_range : ∀ k, k ≤ N → -B ≤ f k ∧ f k ≤ B := by
    intro k hk_le
    have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
    rcases Nat.eq_zero_or_pos N with hN0 | hN_pos
    · -- N = 0 ⟹ k = 0 ⟹ f 0 = -B (and the bound forces B = 0).
      have hk0 : k = 0 := by omega
      have h_ratio_le : 2 * Real.sqrt 2 * B / (δ : ℝ) ≤ 0 := by
        have hceil_zero : ⌈2 * Real.sqrt 2 * B / (δ : ℝ)⌉₊ = 0 := by
          rw [hN_def] at hN0; exact hN0
        rw [Nat.ceil_eq_zero] at hceil_zero; exact hceil_zero
      have h2sB_le : 2 * Real.sqrt 2 * B ≤ 0 := by
        have := (div_le_iff₀ hδ_pos).mp h_ratio_le
        linarith
      have h2sqrt2_pos : (0 : ℝ) < 2 * Real.sqrt 2 := by positivity
      have hB_le_zero : B ≤ 0 := by
        by_contra hB_pos
        push_neg at hB_pos
        have : 0 < 2 * Real.sqrt 2 * B := mul_pos h2sqrt2_pos hB_pos
        linarith
      have hB0 : B = 0 := le_antisymm hB_le_zero hB
      subst hB0
      subst hk0
      simp [hf_def]
    · have hN_real_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
      have hk_div_le_one : (k : ℝ) / (N : ℝ) ≤ 1 := by
        rw [div_le_one hN_real_pos]; exact_mod_cast hk_le
      have hk_div_nonneg : (0 : ℝ) ≤ (k : ℝ) / (N : ℝ) :=
        div_nonneg hk_nonneg hN_real_pos.le
      refine ⟨?_, ?_⟩
      · simp only [hf_def]
        have : 0 ≤ (k : ℝ) / (N : ℝ) * (2 * B) :=
          mul_nonneg hk_div_nonneg h2B_nonneg
        linarith
      · simp only [hf_def]
        have : (k : ℝ) / (N : ℝ) * (2 * B) ≤ 1 * (2 * B) :=
          mul_le_mul_of_nonneg_right hk_div_le_one h2B_nonneg
        linarith
  -- Per-coordinate selection lemma: for any t ∈ [-B, B] there is k ≤ N with |t - f k| ≤ δ/√2.
  have hCoord : ∀ t : ℝ, -B ≤ t → t ≤ B →
      ∃ k, k ≤ N ∧ |t - f k| ≤ (δ : ℝ) / Real.sqrt 2 := by
    intro t htL htU
    rcases Nat.eq_zero_or_pos N with hN0 | hN_pos
    · -- N = 0 ⟹ B = 0 ⟹ t = 0 = f 0.
      have h_ratio_le : 2 * Real.sqrt 2 * B / (δ : ℝ) ≤ 0 := by
        have hceil_zero : ⌈2 * Real.sqrt 2 * B / (δ : ℝ)⌉₊ = 0 := by
          rw [hN_def] at hN0; exact hN0
        rw [Nat.ceil_eq_zero] at hceil_zero; exact hceil_zero
      have h2sB_le : 2 * Real.sqrt 2 * B ≤ 0 := by
        have := (div_le_iff₀ hδ_pos).mp h_ratio_le
        linarith
      have h2sqrt2_pos : (0 : ℝ) < 2 * Real.sqrt 2 := by positivity
      have hB_le_zero : B ≤ 0 := by
        by_contra hB_pos
        push_neg at hB_pos
        have : 0 < 2 * Real.sqrt 2 * B := mul_pos h2sqrt2_pos hB_pos
        linarith
      have hB0 : B = 0 := le_antisymm hB_le_zero hB
      have ht0 : t = 0 := by
        have : -0 ≤ t := hB0 ▸ htL
        have : t ≤ 0 := hB0 ▸ htU
        linarith
      refine ⟨0, by omega, ?_⟩
      have hf0 : f 0 = 0 := by simp [hf_def, hB0]
      rw [ht0, hf0]
      simp
      exact div_nonneg (le_of_lt hδ_pos) hsqrt2_nonneg
    · -- N > 0.
      have hN_real_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
      rcases (lt_or_eq_of_le hB) with hBpos | hB0sym
      · -- B > 0.
        have h2B_pos : (0 : ℝ) < 2 * B := by linarith
        set s : ℝ := (t + B) / (2 * B) with hs_def
        have hs_nonneg : 0 ≤ s := by
          rw [hs_def]; exact div_nonneg (by linarith) h2B_pos.le
        have hs_le_one : s ≤ 1 := by
          rw [hs_def, div_le_one h2B_pos]; linarith
        set k : ℕ := ⌊s * (N : ℝ)⌋₊ with hk_def
        have hsN_nonneg : 0 ≤ s * (N : ℝ) := mul_nonneg hs_nonneg hN_real_pos.le
        have hk_le_N : k ≤ N := by
          rw [hk_def]
          have hle : s * (N : ℝ) ≤ (N : ℝ) := by
            have := mul_le_mul_of_nonneg_right hs_le_one hN_real_pos.le
            linarith
          calc ⌊s * (N : ℝ)⌋₊ ≤ ⌊(N : ℝ)⌋₊ := Nat.floor_mono hle
            _ = N := Nat.floor_natCast N
        have h_floor_le : (k : ℝ) ≤ s * (N : ℝ) := by
          rw [hk_def]; exact Nat.floor_le hsN_nonneg
        have h_lt_floor_add_one : s * (N : ℝ) < (k : ℝ) + 1 := by
          rw [hk_def]; exact Nat.lt_floor_add_one (s * (N : ℝ))
        have h_kN_le_s : (k : ℝ) / (N : ℝ) ≤ s := by
          rw [div_le_iff₀ hN_real_pos]; linarith
        have h_s_lt_kN : s < ((k : ℝ) + 1) / (N : ℝ) := by
          rw [lt_div_iff₀ hN_real_pos]; linarith
        have hfk_eq : f k = -B + s * (2 * B) - (s - (k : ℝ) / (N : ℝ)) * (2 * B) := by
          simp only [hf_def]; ring
        have ht_eq : t = -B + s * (2 * B) := by
          rw [hs_def, div_mul_cancel₀ _ (ne_of_gt h2B_pos)]
          ring
        have h_dist_eq : t - f k = (s - (k : ℝ) / (N : ℝ)) * (2 * B) := by
          rw [hfk_eq, ht_eq]; ring
        have h_diff_nonneg : 0 ≤ s - (k : ℝ) / (N : ℝ) := by linarith
        have h_diff_lt : s - (k : ℝ) / (N : ℝ) < 1 / (N : ℝ) := by
          have := h_s_lt_kN
          have hkN : ((k : ℝ) + 1) / (N : ℝ) = (k : ℝ) / (N : ℝ) + 1 / (N : ℝ) := by
            field_simp
          linarith [hkN ▸ this]
        have h_dist_le : t - f k ≤ (1 / (N : ℝ)) * (2 * B) := by
          rw [h_dist_eq]
          exact mul_le_mul_of_nonneg_right h_diff_lt.le h2B_pos.le
        have h_dist_nonneg : 0 ≤ t - f k := by
          rw [h_dist_eq]
          exact mul_nonneg h_diff_nonneg h2B_pos.le
        -- 1/N · 2B ≤ δ/√2: since N ≥ 2√2 B/δ.
        have h_oneN_le : (1 / (N : ℝ)) * (2 * B) ≤ (δ : ℝ) / Real.sqrt 2 := by
          -- 2B / N ≤ δ/√2 ⟺ 2B * √2 ≤ N * δ ⟺ 2√2*B ≤ N * δ, true since N ≥ 2√2*B/δ.
          rw [one_div, inv_mul_eq_div]
          rw [div_le_div_iff₀ hN_real_pos hsqrt2_pos]
          have h_step : 2 * Real.sqrt 2 * B ≤ (N : ℝ) * (δ : ℝ) := by
            have := (div_le_iff₀ hδ_pos).mp hN_ge_ratio
            linarith
          nlinarith [h_step]
        have h_abs : |t - f k| ≤ (δ : ℝ) / Real.sqrt 2 := by
          rw [abs_of_nonneg h_dist_nonneg]
          exact h_dist_le.trans h_oneN_le
        exact ⟨k, hk_le_N, h_abs⟩
      · -- B = 0. But N > 0 forces ⌈0⌉₊ > 0, contradiction.
        exfalso
        have hB0 : B = 0 := hB0sym.symm
        have : N = 0 := by
          rw [hN_def]; subst hB0; simp
        omega
  -- Bound on dist via Pythagoras (the meat).
  have hDist : ∀ x : EuclideanSpace ℝ (Fin 2),
      x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) B →
      ∃ p ∈ (Finset.range (N + 1)).product (Finset.range (N + 1)),
        dist x (g p) ≤ (δ : ℝ) := by
    intro x hx
    -- Per-coordinate ranges from the L² norm.
    have hx_norm : ‖x‖ ≤ B := by
      rw [Metric.mem_closedBall, dist_zero_right] at hx; exact hx
    have hx_normSq : ‖x‖ ^ 2 ≤ B ^ 2 := by
      have hB_nn : 0 ≤ B := hB
      exact sq_le_sq' (by nlinarith [norm_nonneg x]) hx_norm
    have hx0_sq_le : (x 0) ^ 2 ≤ B ^ 2 := by
      have hsum : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        rw [show (Finset.univ : Finset (Fin 2)) =
              ({0, 1} : Finset (Fin 2)) by decide]
        rw [Finset.sum_pair (by decide : (0 : Fin 2) ≠ 1)]
        simp [Real.norm_eq_abs, sq_abs]
      have h1_sq_nonneg : 0 ≤ (x 1) ^ 2 := sq_nonneg _
      have : (x 0) ^ 2 ≤ ‖x‖ ^ 2 := by linarith
      linarith
    have hx1_sq_le : (x 1) ^ 2 ≤ B ^ 2 := by
      have hsum : ‖x‖ ^ 2 = (x 0) ^ 2 + (x 1) ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        rw [show (Finset.univ : Finset (Fin 2)) =
              ({0, 1} : Finset (Fin 2)) by decide]
        rw [Finset.sum_pair (by decide : (0 : Fin 2) ≠ 1)]
        simp [Real.norm_eq_abs, sq_abs]
      have h0_sq_nonneg : 0 ≤ (x 0) ^ 2 := sq_nonneg _
      have : (x 1) ^ 2 ≤ ‖x‖ ^ 2 := by linarith
      linarith
    have habs_le_B : ∀ a : ℝ, a ^ 2 ≤ B ^ 2 → -B ≤ a ∧ a ≤ B := fun a ha =>
      abs_le_of_sq_le_sq' ha hB
    obtain ⟨hx0L, hx0U⟩ := habs_le_B _ hx0_sq_le
    obtain ⟨hx1L, hx1U⟩ := habs_le_B _ hx1_sq_le
    obtain ⟨k0, hk0_le, hk0_abs⟩ := hCoord (x 0) hx0L hx0U
    obtain ⟨k1, hk1_le, hk1_abs⟩ := hCoord (x 1) hx1L hx1U
    refine ⟨(k0, k1), ?_, ?_⟩
    · exact Finset.mk_mem_product (Finset.mem_range.mpr (by omega))
        (Finset.mem_range.mpr (by omega))
    · -- dist x g(k0,k1) ≤ √(2 · (δ/√2)²) = δ.
      rw [EuclideanSpace.dist_eq]
      rw [show (Finset.univ : Finset (Fin 2)) =
            ({0, 1} : Finset (Fin 2)) by decide]
      rw [Finset.sum_pair (by decide : (0 : Fin 2) ≠ 1)]
      have hg0 : g (k0, k1) 0 = f k0 := by simp [hg_def, PiLp.toLp_apply]
      have hg1 : g (k0, k1) 1 = f k1 := by simp [hg_def, PiLp.toLp_apply]
      rw [hg0, hg1]
      rw [Real.dist_eq, Real.dist_eq]
      -- We need √((x 0 - f k0)² + (x 1 - f k1)²) ≤ δ.
      have hsq_bound : (x 0 - f k0) ^ 2 + (x 1 - f k1) ^ 2 ≤ (δ : ℝ) ^ 2 := by
        have h0_sq : (x 0 - f k0) ^ 2 ≤ ((δ : ℝ) / Real.sqrt 2) ^ 2 := by
          rw [show ((x 0 - f k0) : ℝ) ^ 2 = |x 0 - f k0| ^ 2 by rw [sq_abs]]
          have h_nn : 0 ≤ (δ : ℝ) / Real.sqrt 2 :=
            div_nonneg hδ_pos.le hsqrt2_nonneg
          exact sq_le_sq' (by linarith [abs_nonneg (x 0 - f k0)]) hk0_abs
        have h1_sq : (x 1 - f k1) ^ 2 ≤ ((δ : ℝ) / Real.sqrt 2) ^ 2 := by
          rw [show ((x 1 - f k1) : ℝ) ^ 2 = |x 1 - f k1| ^ 2 by rw [sq_abs]]
          have h_nn : 0 ≤ (δ : ℝ) / Real.sqrt 2 :=
            div_nonneg hδ_pos.le hsqrt2_nonneg
          exact sq_le_sq' (by linarith [abs_nonneg (x 1 - f k1)]) hk1_abs
        have h_sum : ((δ : ℝ) / Real.sqrt 2) ^ 2 + ((δ : ℝ) / Real.sqrt 2) ^ 2 =
            (δ : ℝ) ^ 2 := by
          rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
          field_simp
          ring
        linarith
      -- Square root monotonicity.
      have hδ_nn : 0 ≤ (δ : ℝ) := hδ_pos.le
      calc Real.sqrt ((|x 0 - f k0|) ^ 2 + (|x 1 - f k1|) ^ 2)
          = Real.sqrt ((x 0 - f k0) ^ 2 + (x 1 - f k1) ^ 2) := by rw [sq_abs, sq_abs]
        _ ≤ Real.sqrt ((δ : ℝ) ^ 2) := by
            apply Real.sqrt_le_sqrt; exact hsq_bound
        _ = (δ : ℝ) := Real.sqrt_sq hδ_nn
  -- Assemble IsCover and bound external covering number.
  have hCover : Metric.IsCover δ
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) B) (C : Set (EuclideanSpace ℝ (Fin 2))) := by
    rw [Metric.isCover_iff_subset_iUnion_closedBall]
    intro x hx
    obtain ⟨p, hp_mem, hp_dist⟩ := hDist x hx
    refine Set.mem_iUnion₂.mpr ⟨g p, ?_, ?_⟩
    · refine Finset.mem_coe.mpr ?_
      exact Finset.mem_image.mpr ⟨p, hp_mem, rfl⟩
    · rw [Metric.mem_closedBall]
      exact hp_dist
  have hC_card_le : (C.card : ℕ) ≤ (N + 1) ^ 2 := by
    calc C.card
        ≤ ((Finset.range (N + 1)).product (Finset.range (N + 1))).card :=
          Finset.card_image_le
      _ = (Finset.range (N + 1)).card * (Finset.range (N + 1)).card :=
          Finset.card_product _ _
      _ = (N + 1) * (N + 1) := by rw [Finset.card_range]
      _ = (N + 1) ^ 2 := by ring
  have hC_encard : (C : Set (EuclideanSpace ℝ (Fin 2))).encard ≤
      (((N + 1) ^ 2 : ℕ) : ℕ∞) := by
    rw [Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast hC_card_le
  exact (hCover.externalCoveringNumber_le_encard).trans hC_encard

/-- The δ-external covering number of the closed Euclidean d-ball of
radius `B` is at most `(⌈2 * √d * B / δ⌉₊ + 1) ^ d`. General `d ≥ 1`
version of `covering_number_euclidean_two_ball`, supplying the
`(C * B / δ) ^ d` bound used by B8 N6 (wide-network generalization)
for arbitrary finite `d`. -/
theorem covering_number_euclidean_ball
    (d : ℕ) (B : ℝ) (δ : ℝ≥0) (hd : 1 ≤ d) (hB : 0 ≤ B) (hδ : δ ≠ 0) :
    Metric.externalCoveringNumber δ
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) B) ≤
      ((⌈2 * Real.sqrt d * B / (δ : ℝ)⌉₊ + 1 : ℕ) ^ d : ℕ) := by
  classical
  set N : ℕ := ⌈2 * Real.sqrt d * B / (δ : ℝ)⌉₊ with hN_def
  set f : ℕ → ℝ := fun k => -B + (k : ℝ) / (N : ℝ) * (2 * B) with hf_def
  -- Grid index set: (Fin d → ℕ) with each coordinate in range (N+1).
  set I : Finset (Fin d → ℕ) :=
    Fintype.piFinset (fun _ : Fin d => Finset.range (N + 1)) with hI_def
  set g : (Fin d → ℕ) → EuclideanSpace ℝ (Fin d) := fun k =>
    (WithLp.toLp 2 (fun i : Fin d => f (k i))) with hg_def
  set C : Finset (EuclideanSpace ℝ (Fin d)) := I.image g with hC_def
  -- Positivity facts.
  have hδ_pos : (0 : ℝ) < (δ : ℝ) := by
    have : (0 : ℝ≥0) < δ := pos_iff_ne_zero.mpr hδ
    exact_mod_cast this
  have hδ_nn : (0 : ℝ) ≤ (δ : ℝ) := hδ_pos.le
  have hd_real_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hd_real_nn : (0 : ℝ) ≤ (d : ℝ) := hd_real_pos.le
  have hsqrtd_pos : (0 : ℝ) < Real.sqrt d := Real.sqrt_pos.mpr hd_real_pos
  have hsqrtd_nn : (0 : ℝ) ≤ Real.sqrt d := hsqrtd_pos.le
  have hsqrtd_ne : Real.sqrt d ≠ 0 := ne_of_gt hsqrtd_pos
  have h2B_nonneg : (0 : ℝ) ≤ 2 * B := by linarith
  have hN_ge_ratio : (2 * Real.sqrt d * B) / (δ : ℝ) ≤ (N : ℝ) := by
    rw [hN_def]; exact_mod_cast Nat.le_ceil _
  -- Per-coordinate selection lemma.
  have hCoord : ∀ t : ℝ, -B ≤ t → t ≤ B →
      ∃ k, k ≤ N ∧ |t - f k| ≤ (δ : ℝ) / Real.sqrt d := by
    intro t htL htU
    rcases Nat.eq_zero_or_pos N with hN0 | hN_pos
    · -- N = 0 ⟹ B = 0 ⟹ t = 0 = f 0.
      have h_ratio_le : 2 * Real.sqrt d * B / (δ : ℝ) ≤ 0 := by
        have hceil_zero : ⌈2 * Real.sqrt d * B / (δ : ℝ)⌉₊ = 0 := by
          rw [hN_def] at hN0; exact hN0
        rw [Nat.ceil_eq_zero] at hceil_zero; exact hceil_zero
      have h2sB_le : 2 * Real.sqrt d * B ≤ 0 := by
        have := (div_le_iff₀ hδ_pos).mp h_ratio_le
        linarith
      have h2sqrtd_pos : (0 : ℝ) < 2 * Real.sqrt d := by positivity
      have hB_le_zero : B ≤ 0 := by
        by_contra hB_pos
        push_neg at hB_pos
        have : 0 < 2 * Real.sqrt d * B := mul_pos h2sqrtd_pos hB_pos
        linarith
      have hB0 : B = 0 := le_antisymm hB_le_zero hB
      have ht0 : t = 0 := by
        have hL0 : -0 ≤ t := hB0 ▸ htL
        have hU0 : t ≤ 0 := hB0 ▸ htU
        linarith
      refine ⟨0, by omega, ?_⟩
      have hf0 : f 0 = 0 := by simp [hf_def, hB0]
      rw [ht0, hf0]
      simp
      exact div_nonneg hδ_nn hsqrtd_nn
    · have hN_real_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
      rcases (lt_or_eq_of_le hB) with hBpos | hB0sym
      · have h2B_pos : (0 : ℝ) < 2 * B := by linarith
        set s : ℝ := (t + B) / (2 * B) with hs_def
        have hs_nonneg : 0 ≤ s := by
          rw [hs_def]; exact div_nonneg (by linarith) h2B_pos.le
        have hs_le_one : s ≤ 1 := by
          rw [hs_def, div_le_one h2B_pos]; linarith
        set k : ℕ := ⌊s * (N : ℝ)⌋₊ with hk_def
        have hsN_nonneg : 0 ≤ s * (N : ℝ) := mul_nonneg hs_nonneg hN_real_pos.le
        have hk_le_N : k ≤ N := by
          rw [hk_def]
          have hle : s * (N : ℝ) ≤ (N : ℝ) := by
            have := mul_le_mul_of_nonneg_right hs_le_one hN_real_pos.le
            linarith
          calc ⌊s * (N : ℝ)⌋₊ ≤ ⌊(N : ℝ)⌋₊ := Nat.floor_mono hle
            _ = N := Nat.floor_natCast N
        have h_floor_le : (k : ℝ) ≤ s * (N : ℝ) := by
          rw [hk_def]; exact Nat.floor_le hsN_nonneg
        have h_lt_floor_add_one : s * (N : ℝ) < (k : ℝ) + 1 := by
          rw [hk_def]; exact Nat.lt_floor_add_one (s * (N : ℝ))
        have h_kN_le_s : (k : ℝ) / (N : ℝ) ≤ s := by
          rw [div_le_iff₀ hN_real_pos]; linarith
        have h_s_lt_kN : s < ((k : ℝ) + 1) / (N : ℝ) := by
          rw [lt_div_iff₀ hN_real_pos]; linarith
        have hfk_eq : f k = -B + s * (2 * B) - (s - (k : ℝ) / (N : ℝ)) * (2 * B) := by
          simp only [hf_def]; ring
        have ht_eq : t = -B + s * (2 * B) := by
          rw [hs_def, div_mul_cancel₀ _ (ne_of_gt h2B_pos)]
          ring
        have h_dist_eq : t - f k = (s - (k : ℝ) / (N : ℝ)) * (2 * B) := by
          rw [hfk_eq, ht_eq]; ring
        have h_diff_nonneg : 0 ≤ s - (k : ℝ) / (N : ℝ) := by linarith
        have h_diff_lt : s - (k : ℝ) / (N : ℝ) < 1 / (N : ℝ) := by
          have := h_s_lt_kN
          have hkN : ((k : ℝ) + 1) / (N : ℝ) = (k : ℝ) / (N : ℝ) + 1 / (N : ℝ) := by
            field_simp
          linarith [hkN ▸ this]
        have h_dist_le : t - f k ≤ (1 / (N : ℝ)) * (2 * B) := by
          rw [h_dist_eq]
          exact mul_le_mul_of_nonneg_right h_diff_lt.le h2B_pos.le
        have h_dist_nonneg : 0 ≤ t - f k := by
          rw [h_dist_eq]
          exact mul_nonneg h_diff_nonneg h2B_pos.le
        -- 1/N · 2B ≤ δ/√d.
        have h_oneN_le : (1 / (N : ℝ)) * (2 * B) ≤ (δ : ℝ) / Real.sqrt d := by
          rw [one_div, inv_mul_eq_div]
          rw [div_le_div_iff₀ hN_real_pos hsqrtd_pos]
          have h_step : 2 * Real.sqrt d * B ≤ (N : ℝ) * (δ : ℝ) := by
            have := (div_le_iff₀ hδ_pos).mp hN_ge_ratio
            linarith
          nlinarith [h_step]
        have h_abs : |t - f k| ≤ (δ : ℝ) / Real.sqrt d := by
          rw [abs_of_nonneg h_dist_nonneg]
          exact h_dist_le.trans h_oneN_le
        exact ⟨k, hk_le_N, h_abs⟩
      · -- B = 0 with N > 0 is impossible.
        exfalso
        have hB0 : B = 0 := hB0sym.symm
        have : N = 0 := by
          rw [hN_def]; subst hB0; simp
        omega
  -- Per-coordinate bound from L² norm: each |x i| ≤ B.
  have hCoordBound : ∀ x : EuclideanSpace ℝ (Fin d),
      x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) B →
      ∀ i : Fin d, -B ≤ x i ∧ x i ≤ B := by
    intro x hx i
    have hx_norm : ‖x‖ ≤ B := by
      rw [Metric.mem_closedBall, dist_zero_right] at hx; exact hx
    have hx_normSq : ‖x‖ ^ 2 ≤ B ^ 2 := by
      exact sq_le_sq' (by nlinarith [norm_nonneg x]) hx_norm
    have hsum : ‖x‖ ^ 2 = ∑ j : Fin d, (x j) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [Real.norm_eq_abs, sq_abs]
    have hxi_sq_le_sum : (x i) ^ 2 ≤ ∑ j : Fin d, (x j) ^ 2 := by
      refine Finset.single_le_sum (f := fun j => (x j) ^ 2) ?_ (Finset.mem_univ i)
      intro j _; exact sq_nonneg _
    have hxi_sq_le : (x i) ^ 2 ≤ B ^ 2 := by
      calc (x i) ^ 2 ≤ ∑ j : Fin d, (x j) ^ 2 := hxi_sq_le_sum
        _ = ‖x‖ ^ 2 := hsum.symm
        _ ≤ B ^ 2 := hx_normSq
    exact abs_le_of_sq_le_sq' hxi_sq_le hB
  -- Build the per-point grid index: for each x in the ball, pick coords k : Fin d → ℕ.
  have hDist : ∀ x : EuclideanSpace ℝ (Fin d),
      x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) B →
      ∃ k ∈ I, dist x (g k) ≤ (δ : ℝ) := by
    intro x hx
    -- Choose for each i a k i ≤ N with |x i - f (k i)| ≤ δ/√d.
    have hChoose : ∀ i : Fin d, ∃ ki, ki ≤ N ∧ |x i - f ki| ≤ (δ : ℝ) / Real.sqrt d := by
      intro i
      obtain ⟨hL, hU⟩ := hCoordBound x hx i
      exact hCoord (x i) hL hU
    choose k hk_le hk_abs using hChoose
    refine ⟨k, ?_, ?_⟩
    · rw [hI_def]
      refine Fintype.mem_piFinset.mpr ?_
      intro i; exact Finset.mem_range.mpr (by have := hk_le i; omega)
    · -- Pythagoras: dist² ≤ d · (δ/√d)² = δ².
      rw [EuclideanSpace.dist_eq]
      have hgi : ∀ i : Fin d, g k i = f (k i) := by
        intro i; simp [hg_def]
      have hcoord_dist_sq : ∀ i : Fin d,
          dist (x i) (g k i) ^ 2 ≤ ((δ : ℝ) / Real.sqrt d) ^ 2 := by
        intro i
        rw [hgi i, Real.dist_eq]
        rw [show |x i - f (k i)| ^ 2 = (x i - f (k i)) ^ 2 by rw [sq_abs]]
        have hki_abs := hk_abs i
        have h_nn : 0 ≤ (δ : ℝ) / Real.sqrt d := div_nonneg hδ_nn hsqrtd_nn
        have : (x i - f (k i)) ^ 2 ≤ ((δ : ℝ) / Real.sqrt d) ^ 2 := by
          rw [show ((x i - f (k i)) : ℝ) ^ 2 = |x i - f (k i)| ^ 2 by rw [sq_abs]]
          exact sq_le_sq' (by linarith [abs_nonneg (x i - f (k i))]) hki_abs
        exact this
      have hsum_le : ∑ i : Fin d, dist (x i) (g k i) ^ 2 ≤
          ∑ _i : Fin d, ((δ : ℝ) / Real.sqrt d) ^ 2 := by
        exact Finset.sum_le_sum (fun i _ => hcoord_dist_sq i)
      have hsum_const : ∑ _i : Fin d, ((δ : ℝ) / Real.sqrt d) ^ 2 = (δ : ℝ) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        rw [nsmul_eq_mul]
        rw [div_pow, Real.sq_sqrt hd_real_nn]
        field_simp
      have hsum_le_delta_sq : ∑ i : Fin d, dist (x i) (g k i) ^ 2 ≤ (δ : ℝ) ^ 2 := by
        calc ∑ i : Fin d, dist (x i) (g k i) ^ 2
            ≤ ∑ _i : Fin d, ((δ : ℝ) / Real.sqrt d) ^ 2 := hsum_le
          _ = (δ : ℝ) ^ 2 := hsum_const
      calc Real.sqrt (∑ i : Fin d, dist (x i) (g k i) ^ 2)
          ≤ Real.sqrt ((δ : ℝ) ^ 2) := Real.sqrt_le_sqrt hsum_le_delta_sq
        _ = (δ : ℝ) := Real.sqrt_sq hδ_nn
  -- Assemble IsCover.
  have hCover : Metric.IsCover δ
      (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) B)
      (C : Set (EuclideanSpace ℝ (Fin d))) := by
    rw [Metric.isCover_iff_subset_iUnion_closedBall]
    intro x hx
    obtain ⟨k, hk_mem, hk_dist⟩ := hDist x hx
    refine Set.mem_iUnion₂.mpr ⟨g k, ?_, ?_⟩
    · refine Finset.mem_coe.mpr ?_
      exact Finset.mem_image.mpr ⟨k, hk_mem, rfl⟩
    · rw [Metric.mem_closedBall]; exact hk_dist
  -- Bound cardinality of C.
  have hI_card : I.card = (N + 1) ^ d := by
    rw [hI_def, Fintype.card_piFinset]
    simp [Finset.card_range, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hC_card_le : (C.card : ℕ) ≤ (N + 1) ^ d := by
    calc C.card ≤ I.card := Finset.card_image_le
      _ = (N + 1) ^ d := hI_card
  have hC_encard : (C : Set (EuclideanSpace ℝ (Fin d))).encard ≤
      (((N + 1) ^ d : ℕ) : ℕ∞) := by
    rw [Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast hC_card_le
  exact (hCover.externalCoveringNumber_le_encard).trans hC_encard

/-- Tighter `(1 + 2B/δ)^d` covering-number bound for the closed Euclidean
`d`-ball, via volume-comparison / disjoint open-ball packing.

This is the classical `(1 + 2B/δ)^d` constant (e.g. Vershynin 2018,
Lemma 4.2.13) — sharper than `covering_number_euclidean_ball`'s
`(⌈2√d·B/δ⌉₊ + 1)^d` by the `√d` factor. The proof: any δ-separated
set in `closedBall 0 B` has disjoint open balls of radius `δ/2` around
its points, all contained in `ball 0 (B + δ/2)`; volume comparison
gives `|C| · (δ/2)^d ≤ (B + δ/2)^d`, so
`|C| ≤ (1 + 2B/δ)^d`, hence `packingNumber δ A ≤ ⌈(1+2B/δ)^d⌉₊`.
The cascade `external ≤ covering ≤ packing` then yields the result.

**This is a NEW theorem**; the existing `covering_number_euclidean_ball`
(with looser `√d` constant) is preserved for downstream
`WideNetworkDudley.lean` callers. -/
theorem covering_number_euclidean_ball_tight
    (d : ℕ) (B : ℝ) (δ : ℝ≥0) (hd : 1 ≤ d) (hB : 0 ≤ B) (hδ : δ ≠ 0) :
    Metric.externalCoveringNumber δ
        (Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) B) ≤
      (⌈(1 + 2 * B / (δ : ℝ)) ^ d⌉₊ : ℕ∞) := by
  classical
  set E := EuclideanSpace ℝ (Fin d) with hE_def
  set A : Set E := Metric.closedBall (0 : E) B with hA_def
  set r : ℝ := (δ : ℝ) / 2 with hr_def
  set R : ℝ := B + r with hR_def
  set K : ℕ := ⌈(1 + 2 * B / (δ : ℝ)) ^ d⌉₊ with hK_def
  -- Positivity facts.
  have hδ_pos : (0 : ℝ) < (δ : ℝ) := by
    have : (0 : ℝ≥0) < δ := pos_iff_ne_zero.mpr hδ
    exact_mod_cast this
  have hδ_nn : (0 : ℝ) ≤ (δ : ℝ) := hδ_pos.le
  have hr_pos : 0 < r := by rw [hr_def]; positivity
  have hr_nn : 0 ≤ r := hr_pos.le
  have hR_pos : 0 < R := by rw [hR_def]; linarith
  have hR_nn : 0 ≤ R := hR_pos.le
  -- Fin d nonempty (since d ≥ 1).
  have hd_pos : 0 < d := hd
  have : Nonempty (Fin d) := ⟨⟨0, hd_pos⟩⟩
  -- The volume-of-ball constant in EuclideanSpace ℝ (Fin d).
  set u : ℝ≥0∞ := ENNReal.ofReal
    (Real.sqrt Real.pi ^ Fintype.card (Fin d) /
      Real.Gamma (Fintype.card (Fin d) / 2 + 1)) with hu_def
  -- u is positive: Γ > 0 on (0, ∞), √π > 0, ratio is positive.
  have hu_pos : 0 < u := by
    rw [hu_def]
    rw [ENNReal.ofReal_pos]
    have hpi_pos : 0 < Real.pi := Real.pi_pos
    have hsqrtpi_pos : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr hpi_pos
    have hpow_pos : 0 < Real.sqrt Real.pi ^ Fintype.card (Fin d) :=
      pow_pos hsqrtpi_pos _
    have hcard_pos : (0 : ℝ) < Fintype.card (Fin d) := by
      rw [Fintype.card_fin]; exact_mod_cast hd_pos
    have hxpos : (0 : ℝ) < Fintype.card (Fin d) / 2 + 1 := by linarith
    have hGamma_pos : 0 < Real.Gamma (Fintype.card (Fin d) / 2 + 1) :=
      Real.Gamma_pos_of_pos hxpos
    exact div_pos hpow_pos hGamma_pos
  have hu_ne_zero : u ≠ 0 := ne_of_gt hu_pos
  have hu_ne_top : u ≠ ⊤ := by rw [hu_def]; exact ENNReal.ofReal_ne_top
  -- Volume of ball x s in E = (.ofReal s)^d * u (for any center, any radius).
  have hvol_ball : ∀ (x : E) (s : ℝ),
      MeasureTheory.volume (Metric.ball x s) = (ENNReal.ofReal s) ^ d * u := by
    intro x s
    have hcard : Fintype.card (Fin d) = d := Fintype.card_fin d
    have := EuclideanSpace.volume_ball (Fin d) x s
    rw [hcard] at this
    rw [this, hu_def, hcard]
  -- Key lemma: any δ-separated subset of A has at most K elements.
  have h_sep_encard :
      ∀ C : Set E, C ⊆ A → Metric.IsSeparated (δ : ℝ≥0∞) C → C.encard ≤ (K : ℕ∞) := by
    intro C hCA hCsep
    by_contra hnot
    push_neg at hnot
    -- K + 1 ≤ C.encard.
    have hKlt : (K : ℕ∞) < C.encard := hnot
    have hK_ne_top : (K : ℕ∞) ≠ ⊤ := ENat.coe_ne_top K
    have hK1le : ((K : ℕ∞) + 1) ≤ C.encard :=
      (ENat.add_one_le_iff hK_ne_top).mpr hKlt
    have hK1cast : ((K + 1 : ℕ) : ℕ∞) = (K : ℕ∞) + 1 := by push_cast; rfl
    have hK1le' : ((K + 1 : ℕ) : ℕ∞) ≤ C.encard := hK1cast ▸ hK1le
    obtain ⟨D, hDC, hDenc⟩ := Set.exists_subset_encard_eq hK1le'
    have hDfin : D.Finite := Set.finite_of_encard_eq_coe hDenc
    let F : Finset E := hDfin.toFinset
    have hF_mem : ∀ x, x ∈ F ↔ x ∈ D := by
      intro x; exact hDfin.mem_toFinset
    have hFcard : F.card = K + 1 := by
      have h1 : (F.card : ℕ∞) = D.encard := by
        rw [← Set.encard_coe_eq_coe_finsetCard]
        congr 1
        ext x
        simp [F]
      rw [hDenc] at h1
      exact_mod_cast h1
    have hDsep : Metric.IsSeparated (δ : ℝ≥0∞) D := hCsep.mono hDC
    have hDA : D ⊆ A := hDC.trans hCA
    -- Convert δ-separation: x, y ∈ D, x ≠ y ⟹ (δ : ℝ) < dist x y.
    have hDsep_dist : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → (δ : ℝ) < dist x y := by
      intro x hx y hy hxy
      have h1 : (δ : ℝ≥0∞) < edist x y := hDsep hx hy hxy
      -- edist x y = ENNReal.ofReal (dist x y)
      rw [edist_dist] at h1
      have hdist_nn : 0 ≤ dist x y := dist_nonneg
      have h_coe_eq : ((δ : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal (δ : ℝ) := by
        rw [ENNReal.ofReal_coe_nnreal]
      rw [h_coe_eq] at h1
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hδ_nn).mp h1
    -- Disjoint open balls of radius r centered at points of F.
    have hdisj : (F : Set E).PairwiseDisjoint (fun x => Metric.ball x r) := by
      intro x hxF y hyF hxy
      rw [Function.onFun, Set.disjoint_left]
      intro z hzx hzy
      have hxD : x ∈ D := (hF_mem x).mp (by simpa [Finset.mem_coe] using hxF)
      have hyD : y ∈ D := (hF_mem y).mp (by simpa [Finset.mem_coe] using hyF)
      have hxy_sep : (δ : ℝ) < dist x y := hDsep_dist x hxD y hyD hxy
      have hxz : dist x z < r := by
        rw [Metric.mem_ball] at hzx; rw [dist_comm]; exact hzx
      have hzy' : dist z y < r := by
        rw [Metric.mem_ball] at hzy; exact hzy
      have hxy_lt : dist x y < (δ : ℝ) := by
        calc dist x y ≤ dist x z + dist z y := dist_triangle x z y
          _ < r + r := add_lt_add hxz hzy'
          _ = (δ : ℝ) := by rw [hr_def]; ring
      linarith
    -- The disjoint union of open balls is inside ball 0 R.
    have hsub_big : (⋃ x ∈ F, Metric.ball x r) ⊆ Metric.ball (0 : E) R := by
      intro z hz
      rcases Set.mem_iUnion₂.mp hz with ⟨x, hxF, hzx⟩
      have hxD : x ∈ D := (hF_mem x).mp hxF
      have hxA : x ∈ A := hDA hxD
      have hxB : dist x (0 : E) ≤ B := by
        rw [hA_def, Metric.mem_closedBall] at hxA
        exact hxA
      have hzx' : dist z x < r := by
        rw [Metric.mem_ball] at hzx; exact hzx
      rw [Metric.mem_ball]
      calc dist z (0 : E) ≤ dist z x + dist x (0 : E) := dist_triangle z x 0
        _ < r + B := by linarith
        _ = R := by rw [hR_def]; ring
    -- Volume of the disjoint union equals the sum.
    have hmeasure_union :
        MeasureTheory.volume (⋃ x ∈ F, Metric.ball x r) =
          ∑ x ∈ F, MeasureTheory.volume (Metric.ball x r) :=
      MeasureTheory.measure_biUnion_finset hdisj
        (fun _ _ => measurableSet_ball)
    -- Sum bound: |F| · ofReal(r)^d · u ≤ ofReal(R)^d · u.
    have hsum_eq : ∑ x ∈ F, MeasureTheory.volume (Metric.ball x r) =
        (F.card : ℝ≥0∞) * ((ENNReal.ofReal r) ^ d * u) := by
      calc ∑ x ∈ F, MeasureTheory.volume (Metric.ball x r)
          = ∑ _x ∈ F, (ENNReal.ofReal r) ^ d * u := by
            apply Finset.sum_congr rfl
            intro x _; exact hvol_ball x r
        _ = (F.card : ℝ≥0∞) * ((ENNReal.ofReal r) ^ d * u) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    have hvol_le_big : MeasureTheory.volume (⋃ x ∈ F, Metric.ball x r) ≤
        MeasureTheory.volume (Metric.ball (0 : E) R) := MeasureTheory.measure_mono hsub_big
    have hvol_big_eq : MeasureTheory.volume (Metric.ball (0 : E) R) =
        (ENNReal.ofReal R) ^ d * u := hvol_ball 0 R
    have h_ennreal_chain : (F.card : ℝ≥0∞) * ((ENNReal.ofReal r) ^ d * u) ≤
        (ENNReal.ofReal R) ^ d * u := by
      calc (F.card : ℝ≥0∞) * ((ENNReal.ofReal r) ^ d * u)
          = ∑ x ∈ F, MeasureTheory.volume (Metric.ball x r) := hsum_eq.symm
        _ = MeasureTheory.volume (⋃ x ∈ F, Metric.ball x r) := hmeasure_union.symm
        _ ≤ MeasureTheory.volume (Metric.ball (0 : E) R) := hvol_le_big
        _ = (ENNReal.ofReal R) ^ d * u := hvol_big_eq
    -- Cancel u on both sides. We have u ≠ 0, u ≠ ⊤.
    have h_no_u : (F.card : ℝ≥0∞) * (ENNReal.ofReal r) ^ d ≤ (ENNReal.ofReal R) ^ d := by
      have hassoc1 : (F.card : ℝ≥0∞) * ((ENNReal.ofReal r) ^ d * u) =
          ((F.card : ℝ≥0∞) * (ENNReal.ofReal r) ^ d) * u := by ring
      rw [hassoc1] at h_ennreal_chain
      exact (ENNReal.mul_le_mul_iff_left hu_ne_zero hu_ne_top).mp h_ennreal_chain
    -- Convert ofReal r^d, ofReal R^d to ofReal (r^d), ofReal (R^d).
    have h_pow_r : (ENNReal.ofReal r) ^ d = ENNReal.ofReal (r ^ d) :=
      (ENNReal.ofReal_pow hr_nn d).symm
    have h_pow_R : (ENNReal.ofReal R) ^ d = ENNReal.ofReal (R ^ d) :=
      (ENNReal.ofReal_pow hR_nn d).symm
    rw [h_pow_r, h_pow_R] at h_no_u
    -- (F.card : ℝ≥0∞) = ENNReal.ofReal (F.card : ℝ).
    have h_F_ofReal : (F.card : ℝ≥0∞) = ENNReal.ofReal (F.card : ℝ) := by
      rw [← ENNReal.ofReal_natCast]
    rw [h_F_ofReal] at h_no_u
    have h_F_rd_nn : 0 ≤ (F.card : ℝ) * r ^ d :=
      mul_nonneg (by exact_mod_cast Nat.zero_le _) (pow_nonneg hr_nn d)
    rw [← ENNReal.ofReal_mul (by exact_mod_cast Nat.zero_le _ : (0 : ℝ) ≤ F.card)] at h_no_u
    have h_real : (F.card : ℝ) * r ^ d ≤ R ^ d :=
      (ENNReal.ofReal_le_ofReal_iff (pow_nonneg hR_nn d)).mp h_no_u
    -- Divide by r^d > 0: F.card ≤ (R/r)^d.
    have hrpow_pos : 0 < r ^ d := pow_pos hr_pos d
    have h_F_le_div : (F.card : ℝ) ≤ R ^ d / r ^ d := by
      rw [le_div_iff₀ hrpow_pos]; exact h_real
    -- Simplify R^d/r^d = (R/r)^d = (1 + 2B/δ)^d.
    have h_ratio_eq : R / r = 1 + 2 * B / (δ : ℝ) := by
      rw [hR_def, hr_def]
      field_simp
      ring
    have h_div_pow_eq : R ^ d / r ^ d = (R / r) ^ d := (div_pow R r d).symm
    have h_F_le_ratio : (F.card : ℝ) ≤ (1 + 2 * B / (δ : ℝ)) ^ d := by
      calc (F.card : ℝ) ≤ R ^ d / r ^ d := h_F_le_div
        _ = (R / r) ^ d := h_div_pow_eq
        _ = (1 + 2 * B / (δ : ℝ)) ^ d := by rw [h_ratio_eq]
    -- Conclude F.card ≤ K.
    have hF_card_le_K : F.card ≤ K := by
      have h_nat : (F.card : ℝ) ≤ ((K : ℕ) : ℝ) := by
        calc (F.card : ℝ) ≤ (1 + 2 * B / (δ : ℝ)) ^ d := h_F_le_ratio
          _ ≤ ⌈(1 + 2 * B / (δ : ℝ)) ^ d⌉₊ := Nat.le_ceil _
      exact_mod_cast h_nat
    omega
  -- Bound the packing number.
  have hpack : Metric.packingNumber δ A ≤ (K : ℕ∞) := by
    rw [Metric.packingNumber]
    refine iSup_le ?_; intro C
    refine iSup_le ?_; intro hCA
    refine iSup_le ?_; intro hCsep
    exact h_sep_encard C hCA hCsep
  -- Cascade: external ≤ covering ≤ packing.
  calc Metric.externalCoveringNumber δ A
      ≤ Metric.coveringNumber δ A :=
        Metric.externalCoveringNumber_le_coveringNumber δ A
    _ ≤ Metric.packingNumber δ A :=
        Metric.coveringNumber_le_packingNumber δ A
    _ ≤ (K : ℕ∞) := hpack

end LTFP
