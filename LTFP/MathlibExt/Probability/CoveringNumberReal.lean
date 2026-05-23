/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.Cover
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Real.Basic

/-!
# Explicit `(2B/δ + 1)` covering-number bound for `[-B, B] ⊂ ℝ`

The `δ`-covering number of the closed real interval `[-B, B]` (i.e.
`Metric.closedBall (0 : ℝ) B`) is bounded by `⌈2 * B / δ⌉₊ + 1`. This is
the concrete `d = 1` slice of the classical `(C * B / δ) ^ d` bound used
in the B8 N6 wide-network generalization carrier; the existing
`linear_class_covering_number_lt_top` only certifies finiteness.

The cover is the uniform grid `{ -B + (k : ℝ) / N * (2 * B) : k = 0,…,N }`
where `N := ⌈2 * B / δ⌉₊`. By construction the grid lies inside
`[-B, B]` (so the bound is for the *internal* covering number, matching
`Metric.coveringNumber`), and the spacing `2 * B / N ≤ δ` guarantees
every point of `[-B, B]` is within `δ` of some grid point.
-/

open scoped NNReal ENNReal

namespace LTFP

/-- The δ-covering number of the closed real interval `[-B, B]` is at
most `⌈2 * B / δ⌉₊ + 1`. Concrete `d = 1` instance of the deferred
`(3B/δ)^d` bound used by B8 N6 (wide-network generalization).

**Note (standalone result).** This theorem is *not* called by the final
wide-network B8 N6 closure chain in `WideNetworkDudley.lean`. That chain
threads through the general `d`-dimensional bound
`covering_number_euclidean_ball` (in `CoveringNumberEuclidean.lean`),
which is valid for any `d ≥ 1` and therefore subsumes both the `d = 1`
and `d = 2` cases. This `d = 1` interval bound is kept as a standalone
reference / sanity check — it is sharper in constants than the
specialization of the general `d`-bound to `d = 1` (no `√d = 1` factor,
and the spacing argument is one-sided rather than two-dimensional). -/
theorem covering_number_real_interval
    (B : ℝ) (δ : ℝ≥0) (hB : 0 ≤ B) (hδ : δ ≠ 0) :
    Metric.coveringNumber δ (Metric.closedBall (0 : ℝ) B) ≤
      (⌈2 * B / (δ : ℝ)⌉₊ + 1 : ℕ) := by
  classical
  set N : ℕ := ⌈2 * B / (δ : ℝ)⌉₊ with hN_def
  set f : ℕ → ℝ := fun k => -B + (k : ℝ) / (N : ℝ) * (2 * B) with hf_def
  set C : Finset ℝ := (Finset.range (N + 1)).image f with hC_def
  have hδ_pos : (0 : ℝ) < (δ : ℝ) := by
    have : (0 : ℝ≥0) < δ := pos_iff_ne_zero.mpr hδ
    exact_mod_cast this
  have h2B_nonneg : (0 : ℝ) ≤ 2 * B := by linarith
  -- Step 1: C ⊆ [-B, B].
  have hC_subset : (C : Set ℝ) ⊆ Metric.closedBall (0 : ℝ) B := by
    intro y hy
    rcases Finset.mem_coe.mp hy with hy
    rcases Finset.mem_image.mp hy with ⟨k, hk_range, rfl⟩
    have hk_le : k ≤ N := by
      have := Finset.mem_range.mp hk_range
      omega
    have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.zero_le k)
    -- f k = -B + (k/N) * 2B  ∈ [-B, B]
    rcases Nat.eq_zero_or_pos N with hN0 | hN_pos
    · -- N = 0 ⟹ k = 0 ⟹ f 0 = -B + 0 = -B. Combined with N=0 we have 2B/δ ≤ 0,
      -- so 2B ≤ 0, hence B ≤ 0, with hB : 0 ≤ B forcing B = 0.
      have hk0 : k = 0 := by omega
      have h2B_le_zero : 2 * B ≤ 0 := by
        have hceil_zero : ⌈2 * B / (δ : ℝ)⌉₊ = 0 := by
          rw [hN_def] at hN0; exact hN0
        have hle : 2 * B / (δ : ℝ) ≤ 0 := by
          rw [Nat.ceil_eq_zero] at hceil_zero; exact hceil_zero
        have := (div_le_iff₀ hδ_pos).mp hle
        linarith
      have hB0 : B = 0 := le_antisymm (by linarith) hB
      subst hB0
      subst hk0
      simp [hf_def]
    · -- N > 0: f k = -B + (k/N) * 2B with 0 ≤ k/N ≤ 1
      have hN_real_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
      have hk_div_le_one : (k : ℝ) / (N : ℝ) ≤ 1 := by
        rw [div_le_one hN_real_pos]; exact_mod_cast hk_le
      have hk_div_nonneg : (0 : ℝ) ≤ (k : ℝ) / (N : ℝ) :=
        div_nonneg hk_nonneg (le_of_lt hN_real_pos)
      have hfk_lower : -B ≤ f k := by
        simp only [hf_def]
        have : 0 ≤ (k : ℝ) / (N : ℝ) * (2 * B) :=
          mul_nonneg hk_div_nonneg h2B_nonneg
        linarith
      have hfk_upper : f k ≤ B := by
        simp only [hf_def]
        have : (k : ℝ) / (N : ℝ) * (2 * B) ≤ 1 * (2 * B) :=
          mul_le_mul_of_nonneg_right hk_div_le_one h2B_nonneg
        linarith
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le]
      exact ⟨by linarith, hfk_upper⟩
  -- Step 2: IsCover δ A C.
  have hCover : Metric.IsCover δ (Metric.closedBall (0 : ℝ) B) (C : Set ℝ) := by
    rw [Metric.isCover_iff_subset_iUnion_closedBall]
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le] at hx
    obtain ⟨hxL, hxU⟩ := hx
    rcases Nat.eq_zero_or_pos N with hN0 | hN_pos
    · -- N = 0 forces B = 0, hence x = 0 = f 0. The point 0 is in C.
      have h2B_le_zero : 2 * B ≤ 0 := by
        have hceil_zero : ⌈2 * B / (δ : ℝ)⌉₊ = 0 := by
          rw [hN_def] at hN0; exact hN0
        have hle : 2 * B / (δ : ℝ) ≤ 0 := by
          rw [Nat.ceil_eq_zero] at hceil_zero; exact hceil_zero
        have := (div_le_iff₀ hδ_pos).mp hle
        linarith
      have hB0 : B = 0 := le_antisymm (by linarith) hB
      have hx0 : x = 0 := by
        have hxL0 : -0 ≤ x := hB0 ▸ hxL
        have hxU0 : x ≤ 0 := hB0 ▸ hxU
        linarith
      refine Set.mem_iUnion₂.mpr ⟨f 0, ?_, ?_⟩
      · refine Finset.mem_coe.mpr ?_
        refine Finset.mem_image.mpr ⟨0, ?_, rfl⟩
        exact Finset.mem_range.mpr (by omega)
      · simp [hf_def, hB0, hx0, Metric.mem_closedBall]
    · -- N > 0: pick k := ⌊(x + B) / (2 * B) * N⌋₊  (clipped to [0, N]).
      have hN_real_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
      -- Case on whether B = 0 or B > 0.
      rcases (lt_or_eq_of_le hB) with hBpos | hB0sym
      · -- B > 0
        have h2B_pos : (0 : ℝ) < 2 * B := by linarith
        -- t := (x + B) / (2 * B) ∈ [0, 1]
        set t : ℝ := (x + B) / (2 * B) with ht_def
        have ht_nonneg : 0 ≤ t := by
          rw [ht_def]; exact div_nonneg (by linarith) h2B_pos.le
        have ht_le_one : t ≤ 1 := by
          rw [ht_def, div_le_one h2B_pos]; linarith
        -- k := ⌊t * N⌋₊, bounded by N
        set k : ℕ := ⌊t * (N : ℝ)⌋₊ with hk_def
        have htN_nonneg : 0 ≤ t * (N : ℝ) := mul_nonneg ht_nonneg hN_real_pos.le
        have hk_le_N : k ≤ N := by
          rw [hk_def]
          have : t * (N : ℝ) ≤ (N : ℝ) := by
            have := mul_le_mul_of_nonneg_right ht_le_one hN_real_pos.le
            linarith
          have := Nat.floor_le_of_le this
          calc ⌊t * (N : ℝ)⌋₊ ≤ ⌊(N : ℝ)⌋₊ := Nat.floor_mono (by linarith [mul_le_mul_of_nonneg_right ht_le_one hN_real_pos.le])
            _ = N := Nat.floor_natCast N
        have hk_range_mem : k ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
        -- k/N ≤ t ≤ (k+1)/N, hence |t - k/N| ≤ 1/N
        have h_floor_le : (k : ℝ) ≤ t * (N : ℝ) := by
          rw [hk_def]; exact Nat.floor_le htN_nonneg
        have h_lt_floor_add_one : t * (N : ℝ) < (k : ℝ) + 1 := by
          rw [hk_def]; exact Nat.lt_floor_add_one (t * (N : ℝ))
        -- Convert to k/N ≤ t < (k+1)/N
        have h_kN_le_t : (k : ℝ) / (N : ℝ) ≤ t := by
          rw [div_le_iff₀ hN_real_pos]; linarith
        have h_t_lt_kN : t < ((k : ℝ) + 1) / (N : ℝ) := by
          rw [lt_div_iff₀ hN_real_pos]; linarith
        -- Distance from x to f k
        have hfk_eq : f k = -B + t * (2 * B) - (t - (k : ℝ) / (N : ℝ)) * (2 * B) := by
          simp only [hf_def]; ring
        have hx_eq : x = -B + t * (2 * B) := by
          rw [ht_def, div_mul_cancel₀ _ (ne_of_gt h2B_pos)]
          ring
        have h_dist_eq : x - f k = (t - (k : ℝ) / (N : ℝ)) * (2 * B) := by
          rw [hfk_eq, hx_eq]; ring
        have h_diff_nonneg : 0 ≤ t - (k : ℝ) / (N : ℝ) := by linarith
        have h_diff_lt : t - (k : ℝ) / (N : ℝ) < 1 / (N : ℝ) := by
          have := h_t_lt_kN
          have hkN : ((k : ℝ) + 1) / (N : ℝ) = (k : ℝ) / (N : ℝ) + 1 / (N : ℝ) := by
            field_simp
          linarith [hkN ▸ this]
        have h_dist_le : x - f k ≤ (1 / (N : ℝ)) * (2 * B) := by
          rw [h_dist_eq]
          exact mul_le_mul_of_nonneg_right h_diff_lt.le h2B_pos.le
        have h_dist_nonneg : 0 ≤ x - f k := by
          rw [h_dist_eq]
          exact mul_nonneg h_diff_nonneg h2B_pos.le
        -- 1/N ≤ δ / (2B): since N ≥ 2B/δ, we have N · δ ≥ 2B, so 1/N ≤ δ/(2B).
        have hN_ge_ratio : (2 * B) / (δ : ℝ) ≤ (N : ℝ) := by
          rw [hN_def]; exact_mod_cast Nat.le_ceil _
        have h_oneN_le : (1 / (N : ℝ)) * (2 * B) ≤ (δ : ℝ) := by
          rw [one_div, inv_mul_eq_div]
          rw [div_le_iff₀ hN_real_pos]
          have : (2 * B) ≤ (N : ℝ) * (δ : ℝ) := by
            have := (div_le_iff₀ hδ_pos).mp hN_ge_ratio
            linarith
          linarith
        have h_abs : |x - f k| ≤ (δ : ℝ) := by
          rw [abs_of_nonneg h_dist_nonneg]
          exact h_dist_le.trans h_oneN_le
        refine Set.mem_iUnion₂.mpr ⟨f k, ?_, ?_⟩
        · exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨k, hk_range_mem, rfl⟩)
        · rw [Metric.mem_closedBall, Real.dist_eq]
          exact h_abs
      · -- B = 0 (degenerate, but N > 0 not possible since ⌈0⌉₊ = 0). Contradiction.
        exfalso
        have hB0 : B = 0 := hB0sym.symm
        have : N = 0 := by
          rw [hN_def]
          subst hB0
          simp
        omega
  -- Step 3: bound coveringNumber via IsCover.coveringNumber_le_encard.
  have hC_encard : (C : Set ℝ).encard ≤ ((N + 1 : ℕ) : ℕ∞) := by
    rw [Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast (Finset.card_image_le).trans (by simp : (Finset.range (N + 1)).card ≤ N + 1)
  exact (hCover.coveringNumber_le_encard hC_subset).trans hC_encard

end LTFP
