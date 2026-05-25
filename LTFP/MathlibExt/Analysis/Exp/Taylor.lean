/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Banach-algebra Taylor estimate for the exponential map

This file establishes two prerequisite norm bounds for the
Lie-Trotter product formula in a Banach algebra `𝔸`:

* `NormedSpace.norm_exp_le_exp_norm` — for any `Z : 𝔸`,
  `‖NormedSpace.exp Z‖ ≤ Real.exp ‖Z‖`. The hypothesis
  `[NormOneClass 𝔸]` is needed so that the `n = 0` term
  `‖(1 : 𝔸)‖ = 1` matches the scalar bound; matrix algebras and
  operator algebras satisfy this automatically.

* `NormedSpace.norm_exp_sub_one_sub_id_le_banach` — for any `Z : 𝔸`,
  `‖NormedSpace.exp Z - 1 - Z‖ ≤ ‖Z‖^2 * Real.exp ‖Z‖`. This is the
  Banach-algebra analogue of `Complex.norm_exp_sub_one_sub_id_le` but
  WITHOUT the `‖x‖ ≤ 1` hypothesis (replaced by the universal but
  looser `Real.exp ‖Z‖` factor). This version does NOT require
  `[NormOneClass 𝔸]`: the index-shift removes the `n = 0` and `n = 1`
  terms, where the `n = 0` term is the only one referencing `‖1‖`.

Both lemmas use the `NormedSpace.exp` API surface: scalars over `ℚ`
with `[NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]`, matching
the standard Mathlib convention.
-/

open scoped Nat

namespace NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℚ 𝔸] [CompleteSpace 𝔸]

/-! ### Auxiliary lemmas -/

/-- The rational scalar `((n!)⁻¹ : ℚ)` has real-valued norm `(n! : ℝ)⁻¹`. -/
private lemma norm_rat_inv_factorial (n : ℕ) :
    ‖((n !⁻¹ : ℚ))‖ = (n ! : ℝ)⁻¹ := by
  rw [← Rat.norm_cast_real, Rat.cast_inv, Rat.cast_natCast,
      Real.norm_eq_abs, abs_of_nonneg (by positivity)]

omit [CompleteSpace 𝔸] in
/-- Norm bound on an individual exponential series term, valid for all `n ≥ 1`. -/
private lemma norm_expSeries_term_le (Z : 𝔸) {n : ℕ} (hn : 0 < n) :
    ‖((n !⁻¹ : ℚ) • Z ^ n : 𝔸)‖ ≤ (n ! : ℝ)⁻¹ * ‖Z‖ ^ n := by
  rw [norm_smul, norm_rat_inv_factorial]
  exact mul_le_mul_of_nonneg_left (norm_pow_le' Z hn) (by positivity)

/-! ### Lemma F: `‖exp Z‖ ≤ Real.exp ‖Z‖` -/

/-- In a Banach algebra `𝔸` with `‖(1 : 𝔸)‖ = 1`, the operator norm of
`NormedSpace.exp Z` is bounded by the scalar exponential of `‖Z‖`. -/
theorem norm_exp_le_exp_norm [NormOneClass 𝔸] (Z : 𝔸) :
    ‖NormedSpace.exp Z‖ ≤ Real.exp ‖Z‖ := by
  -- Sum representation of `exp Z` in `𝔸`.
  have hZ : HasSum (fun n : ℕ => ((n !⁻¹ : ℚ) • Z ^ n : 𝔸)) (NormedSpace.exp Z) :=
    NormedSpace.exp_series_hasSum_exp' Z
  -- Sum representation of `Real.exp ‖Z‖` rewritten as `(n!)⁻¹ * ‖Z‖^n`.
  have hR' : HasSum (fun n : ℕ => (n ! : ℝ)⁻¹ * ‖Z‖ ^ n) (Real.exp ‖Z‖) := by
    have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (‖Z‖ : ℝ)
    rw [show NormedSpace.exp (‖Z‖ : ℝ) = Real.exp ‖Z‖ from
        (Real.exp_eq_exp_ℝ).symm ▸ rfl] at h
    simpa [smul_eq_mul] using h
  -- Term-wise bound.
  have hterm : ∀ n, ‖((n !⁻¹ : ℚ) • Z ^ n : 𝔸)‖ ≤ (n ! : ℝ)⁻¹ * ‖Z‖ ^ n := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one]
      have h1 : ((1 : ℚ) • (1 : 𝔸)) = (1 : 𝔸) := one_smul ℚ (1 : 𝔸)
      rw [h1]
      simp [norm_one]
    · exact norm_expSeries_term_le Z hn
  -- Apply `HasSum.norm_le_of_bounded`.
  exact hZ.norm_le_of_bounded hR' hterm

/-! ### Lemma A: Banach-algebra exp Taylor estimate -/

/-- Index-shifted form: the residual of `exp Z` after dropping the
constant and linear terms equals `∑' m, ((m+2)!)⁻¹ • Z^(m+2)`. -/
private lemma exp_sub_one_sub_self_eq_tsum (Z : 𝔸) :
    NormedSpace.exp Z - 1 - Z =
      ∑' m : ℕ, ((((m + 2) !)⁻¹ : ℚ) • Z ^ (m + 2) : 𝔸) := by
  -- Summability of the full exponential series.
  have hsum : Summable (fun n : ℕ => ((n !⁻¹ : ℚ) • Z ^ n : 𝔸)) :=
    NormedSpace.expSeries_summable' Z
  -- Split off the first two terms.
  have hsplit := hsum.sum_add_tsum_nat_add (k := 2)
  -- Compute the finite prefix `∑_{i ∈ range 2}` explicitly.
  have hprefix :
      (∑ i ∈ Finset.range 2, ((i !⁻¹ : ℚ) • Z ^ i : 𝔸)) = 1 + Z := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    have h0 : ((0 !⁻¹ : ℚ) • (Z ^ 0) : 𝔸) = 1 := by
      simp only [Nat.factorial_zero, Nat.cast_one, inv_one, pow_zero]
      exact one_smul ℚ (1 : 𝔸)
    have h1 : ((1 !⁻¹ : ℚ) • (Z ^ 1) : 𝔸) = Z := by
      simp only [Nat.factorial_one, Nat.cast_one, inv_one, pow_one]
      exact one_smul ℚ Z
    rw [h0, h1]
  -- Express `NormedSpace.exp Z` via the tsum.
  have hexp : NormedSpace.exp Z = ∑' n, ((n !⁻¹ : ℚ) • Z ^ n : 𝔸) := by
    rw [NormedSpace.exp_eq_tsum_rat]
  -- Solve for the residual.
  rw [hexp, ← hsplit, hprefix]
  abel

/-- Banach-algebra Taylor estimate for the exponential. For any
`Z : 𝔸`, the second-order residual of `exp` is controlled by
`‖Z‖^2 * Real.exp ‖Z‖`. Unlike the scalar version
`Complex.norm_exp_sub_one_sub_id_le`, no smallness assumption on `‖Z‖`
is required. -/
theorem norm_exp_sub_one_sub_id_le_banach (Z : 𝔸) :
    ‖NormedSpace.exp Z - 1 - Z‖ ≤ ‖Z‖ ^ 2 * Real.exp ‖Z‖ := by
  -- Rewrite the LHS as the tail tsum starting from index 2.
  rw [exp_sub_one_sub_self_eq_tsum Z]
  -- Sum for `Real.exp ‖Z‖` in the form `(n!)⁻¹ * ‖Z‖^n`.
  have hsum_full :
      HasSum (fun n : ℕ => (n ! : ℝ)⁻¹ * ‖Z‖ ^ n) (Real.exp ‖Z‖) := by
    have h := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (‖Z‖ : ℝ)
    rw [show NormedSpace.exp (‖Z‖ : ℝ) = Real.exp ‖Z‖ from
        (Real.exp_eq_exp_ℝ).symm ▸ rfl] at h
    simpa [smul_eq_mul] using h
  -- Bounding series: `‖Z‖^2 * ((m!)⁻¹ * ‖Z‖^m)`, with sum `‖Z‖^2 * Real.exp ‖Z‖`.
  have hsum_bound :
      HasSum (fun m : ℕ => ‖Z‖ ^ 2 * ((m ! : ℝ)⁻¹ * ‖Z‖ ^ m))
        (‖Z‖ ^ 2 * Real.exp ‖Z‖) :=
    hsum_full.mul_left (‖Z‖ ^ 2)
  -- Term-wise bound for the index-shifted series.
  have hterm : ∀ m,
      ‖((((m + 2) !)⁻¹ : ℚ) • Z ^ (m + 2) : 𝔸)‖ ≤
        ‖Z‖ ^ 2 * ((m ! : ℝ)⁻¹ * ‖Z‖ ^ m) := by
    intro m
    -- Step 1: term ≤ `((m+2)!)⁻¹ * ‖Z‖^(m+2)`.
    have h1 : ‖((((m + 2) !)⁻¹ : ℚ) • Z ^ (m + 2) : 𝔸)‖ ≤
        ((m + 2)! : ℝ)⁻¹ * ‖Z‖ ^ (m + 2) :=
      norm_expSeries_term_le Z (Nat.add_pos_right m (by decide))
    -- Step 2: `((m+2)!)⁻¹ ≤ (m!)⁻¹`.
    have hfact_le : ((m + 2)! : ℝ)⁻¹ ≤ (m ! : ℝ)⁻¹ := by
      have hpos_m : (0 : ℝ) < (m ! : ℝ) := by exact_mod_cast Nat.factorial_pos m
      have hle_nat : m ! ≤ (m + 2)! := Nat.factorial_le (Nat.le_add_right m 2)
      have hle_real : (m ! : ℝ) ≤ ((m + 2)! : ℝ) := by exact_mod_cast hle_nat
      exact inv_anti₀ hpos_m hle_real
    -- Step 3: `‖Z‖^(m+2) = ‖Z‖^2 * ‖Z‖^m`.
    have hpow : ‖Z‖ ^ (m + 2) = ‖Z‖ ^ 2 * ‖Z‖ ^ m := by
      rw [pow_add, mul_comm]
    -- Chain the bounds.
    calc ‖((((m + 2) !)⁻¹ : ℚ) • Z ^ (m + 2) : 𝔸)‖
        ≤ ((m + 2)! : ℝ)⁻¹ * ‖Z‖ ^ (m + 2) := h1
      _ = ((m + 2)! : ℝ)⁻¹ * (‖Z‖ ^ 2 * ‖Z‖ ^ m) := by rw [hpow]
      _ ≤ (m ! : ℝ)⁻¹ * (‖Z‖ ^ 2 * ‖Z‖ ^ m) := by
          have hZnn : 0 ≤ ‖Z‖ ^ 2 * ‖Z‖ ^ m := by positivity
          exact mul_le_mul_of_nonneg_right hfact_le hZnn
      _ = ‖Z‖ ^ 2 * ((m ! : ℝ)⁻¹ * ‖Z‖ ^ m) := by ring
  -- Conclude via `tsum_of_norm_bounded`.
  exact tsum_of_norm_bounded hsum_bound hterm

end NormedSpace
