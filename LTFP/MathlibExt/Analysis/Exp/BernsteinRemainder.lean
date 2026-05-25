/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Bennett-Bernstein scalar remainder bound for `exp`

This file establishes the scalar inequality

  `Real.exp y ≤ 1 + y + y^2 / (2 * (1 - b / 3))`,   for `|y| ≤ b` with `0 ≤ b < 3`,

which is the standard scalar version of the Bennett-Bernstein remainder
bound for the exponential function.  It controls the second-order Taylor
remainder by a *rational* function of `b`, which is sharper than the
universal `y^2 * exp(b)` form in the regime `b < 3`.

The proof bounds each Taylor coefficient `y^{m+2} / (m+2)!` by
`(y^2 / 2) * (b / 3)^m`, using the elementary factorial inequality
`(m+2)! ≥ 2 * 3^m`, and then sums the resulting geometric series.

## Main result

* `Real.exp_le_one_add_self_add_sq_div_of_abs_le` — the Bennett-Bernstein
  scalar remainder bound for `Real.exp`.
-/

open scoped Nat

namespace Real

/-! ### Factorial lower bound -/

/-- For every `m : ℕ`, the factorial `(m + 2)!` is at least `2 * 3 ^ m`.

This is the elementary bound underlying the Bennett-Bernstein rational
remainder form.  The proof is by induction on `m`: the base case is
`2! = 2 = 2 * 3 ^ 0`, and the inductive step uses `m + 3 ≥ 3`. -/
private lemma two_mul_three_pow_le_factorial_add_two (m : ℕ) :
    2 * 3 ^ m ≤ ((m + 2) ! : ℕ) := by
  induction m with
  | zero => decide
  | succ k ih =>
      -- `(k + 3)! = (k + 3) * (k + 2)!`
      have hfact : ((k + 1 + 2) ! : ℕ) = (k + 3) * ((k + 2) ! : ℕ) := by
        show (k + 3).factorial = (k + 3) * (k + 2).factorial
        exact Nat.factorial_succ (k + 2)
      have hpow : (2 : ℕ) * 3 ^ (k + 1) = 3 * (2 * 3 ^ k) := by ring
      rw [hfact, hpow]
      exact Nat.mul_le_mul (by omega) ih

/-! ### Term-wise bound on the Taylor coefficients -/

/-- For `0 ≤ b` and `|y| ≤ b`, the `(m+2)`-th Taylor coefficient of
`exp` at `y` is bounded by `(y^2 / 2) * (b / 3) ^ m`.

(The hypothesis `b < 3` is not required for the *termwise* bound — it
is needed only for the *summability* of the geometric series.) -/
private lemma exp_coeff_le {y b : ℝ} (hb0 : 0 ≤ b) (hy : |y| ≤ b)
    (m : ℕ) :
    y ^ (m + 2) / ((m + 2) ! : ℝ) ≤ y ^ 2 / 2 * (b / 3) ^ m := by
  -- `|y| ≤ b` so `|y|^m ≤ b^m`.
  have hbnn : (0 : ℝ) ≤ b := hb0
  have habs_nn : (0 : ℝ) ≤ |y| := abs_nonneg y
  have hy_pow_abs_le : |y| ^ m ≤ b ^ m := pow_le_pow_left₀ habs_nn hy m
  -- `y^m ≤ |y|^m`.
  have hy_pow_le_abs : y ^ m ≤ |y| ^ m := by
    rw [← abs_pow]; exact le_abs_self _
  -- Chain: `y^m ≤ b^m`.
  have hy_pow_le_b_pow : y ^ m ≤ b ^ m := le_trans hy_pow_le_abs hy_pow_abs_le
  -- `y^(m+2) = y^2 * y^m`, with `y^2 ≥ 0`.
  have hy2_nn : (0 : ℝ) ≤ y ^ 2 := sq_nonneg y
  have hb_pow_nn : (0 : ℝ) ≤ b ^ m := pow_nonneg hbnn m
  have hy_split : y ^ (m + 2) = y ^ 2 * y ^ m := by ring
  -- Step 1: `y^(m+2) ≤ y^2 * b^m`.
  have hnum_le : y ^ (m + 2) ≤ y ^ 2 * b ^ m := by
    rw [hy_split]
    exact mul_le_mul_of_nonneg_left hy_pow_le_b_pow hy2_nn
  -- Step 2: `(m+2)! ≥ 2 * 3^m` in `ℝ`.
  have hfact_nat : 2 * 3 ^ m ≤ ((m + 2) ! : ℕ) :=
    two_mul_three_pow_le_factorial_add_two m
  have hfact_real : (2 : ℝ) * 3 ^ m ≤ ((m + 2) ! : ℝ) := by
    have := (Nat.cast_le (α := ℝ)).mpr hfact_nat
    push_cast at this
    convert this using 1
  -- `(m+2)!` is positive in `ℝ`.
  have hfact_pos : (0 : ℝ) < ((m + 2) ! : ℝ) := by
    exact_mod_cast Nat.factorial_pos (m + 2)
  -- `2 * 3^m` is positive.
  have hden_pos : (0 : ℝ) < 2 * 3 ^ m := by positivity
  -- Step 3: divide both sides of step 1 by `(m+2)!`, and bound `1/(m+2)! ≤ 1/(2*3^m)`.
  have hnum_nn : (0 : ℝ) ≤ y ^ 2 * b ^ m := mul_nonneg hy2_nn hb_pow_nn
  -- `y^(m+2)/(m+2)! ≤ y^2 * b^m / (m+2)!`.
  have hstep1 : y ^ (m + 2) / ((m + 2) ! : ℝ) ≤ y ^ 2 * b ^ m / ((m + 2) ! : ℝ) :=
    div_le_div_of_nonneg_right hnum_le hfact_pos.le
  -- `y^2 * b^m / (m+2)! ≤ y^2 * b^m / (2 * 3^m)`.
  have hstep2 : y ^ 2 * b ^ m / ((m + 2) ! : ℝ) ≤ y ^ 2 * b ^ m / (2 * 3 ^ m) := by
    apply div_le_div_of_nonneg_left hnum_nn hden_pos hfact_real
  -- Algebra: `y^2 * b^m / (2 * 3^m) = (y^2 / 2) * (b/3)^m`.
  have h3_pow_pos : (0 : ℝ) < 3 ^ m := by positivity
  have h3_pow_ne : (3 ^ m : ℝ) ≠ 0 := h3_pow_pos.ne'
  have hpow_quot : (b / 3) ^ m = b ^ m / 3 ^ m := div_pow b 3 m
  have hrhs_eq : y ^ 2 * b ^ m / (2 * 3 ^ m) = y ^ 2 / 2 * (b / 3) ^ m := by
    rw [hpow_quot]
    field_simp
  -- Chain.
  calc y ^ (m + 2) / ((m + 2) ! : ℝ)
      ≤ y ^ 2 * b ^ m / ((m + 2) ! : ℝ) := hstep1
    _ ≤ y ^ 2 * b ^ m / (2 * 3 ^ m) := hstep2
    _ = y ^ 2 / 2 * (b / 3) ^ m := hrhs_eq

/-! ### Summability of the bounding series -/

private lemma summable_bound (y b : ℝ) (hb0 : 0 ≤ b) (hb3 : b < 3) :
    Summable (fun m : ℕ => y ^ 2 / 2 * (b / 3) ^ m) := by
  have hb3' : b / 3 < 1 := by linarith
  have hb_div_nn : (0 : ℝ) ≤ b / 3 := by positivity
  have h_abs : |b / 3| < 1 := by
    rw [abs_of_nonneg hb_div_nn]; exact hb3'
  exact (summable_geometric_of_abs_lt_one h_abs).mul_left (y ^ 2 / 2)

/-! ### Main result -/

/-- **Bennett-Bernstein scalar remainder bound for `exp`.**

For any `y, b : ℝ` with `0 ≤ b < 3` and `|y| ≤ b`,

  `Real.exp y ≤ 1 + y + y^2 / (2 * (1 - b / 3))`.

The proof bounds each Taylor coefficient `y^{m+2} / (m+2)!` by
`(y^2 / 2) * (b / 3)^m` (using `(m+2)! ≥ 2 * 3^m`), then sums the
resulting geometric series.

This is the scalar form underlying Bernstein-type inequalities, where
the rational factor `1 / (1 - b/3)` is sharper than the universal
`exp(b)` factor in the regime `b < 3`. -/
theorem exp_le_one_add_self_add_sq_div_of_abs_le
    {y b : ℝ}
    (hb0 : 0 ≤ b) (hb3 : b < 3) (hy : |y| ≤ b) :
    Real.exp y ≤
      1 + y + y ^ 2 / (2 * (1 - b / 3)) := by
  -- Step 1: express `Real.exp y` as a tsum.
  have hexp_tsum : Real.exp y = ∑' n : ℕ, y ^ n / (n ! : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  -- Step 2: split off the first two terms (`n = 0, 1`).
  have hsum : Summable (fun n : ℕ => y ^ n / (n ! : ℝ)) := by
    -- The exponential series in `ℝ` is always summable.
    have : Summable (fun n : ℕ => (n !⁻¹ : ℝ) • y ^ n) :=
      NormedSpace.expSeries_summable' (𝕂 := ℝ) y
    -- Convert `(n!)⁻¹ • y^n = y^n / n!`.
    simpa [smul_eq_mul, mul_comm, div_eq_mul_inv] using this
  have hsplit := hsum.sum_add_tsum_nat_add (k := 2)
  -- Compute the finite prefix `∑_{i ∈ range 2}`.
  have hprefix :
      (∑ i ∈ Finset.range 2, y ^ i / (i ! : ℝ)) = 1 + y := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp [Nat.factorial_zero, Nat.factorial_one, pow_zero, pow_one]
  -- So `exp y = 1 + y + ∑' m, y^(m+2)/(m+2)!`.
  have hexp_eq :
      Real.exp y =
        1 + y + ∑' m : ℕ, y ^ (m + 2) / ((m + 2) ! : ℝ) := by
    rw [hexp_tsum, ← hsplit, hprefix]
  rw [hexp_eq]
  -- Step 3: compare tsums termwise.
  -- LHS tail summable (it's a difference of two summables).
  have hsum_tail :
      Summable (fun m : ℕ => y ^ (m + 2) / ((m + 2) ! : ℝ)) := by
    have := (summable_nat_add_iff (f := fun n : ℕ => y ^ n / (n ! : ℝ)) 2).mpr hsum
    simpa using this
  -- RHS bound summable.
  have hsum_bnd : Summable (fun m : ℕ => y ^ 2 / 2 * (b / 3) ^ m) :=
    summable_bound y b hb0 hb3
  -- Geometric series sum.
  have hb3_lt1 : b / 3 < 1 := by linarith
  have hb_div_nn : (0 : ℝ) ≤ b / 3 := by positivity
  have hgeom : ∑' m : ℕ, (b / 3) ^ m = (1 - b / 3)⁻¹ :=
    tsum_geometric_of_lt_one hb_div_nn hb3_lt1
  -- `∑' m, y^2/2 * (b/3)^m = y^2/2 * (1 - b/3)⁻¹`.
  have hsum_eq :
      ∑' m : ℕ, y ^ 2 / 2 * (b / 3) ^ m = y ^ 2 / 2 * (1 - b / 3)⁻¹ := by
    rw [tsum_mul_left, hgeom]
  -- Step 4: tsum comparison.
  have h_tsum_le :
      ∑' m : ℕ, y ^ (m + 2) / ((m + 2) ! : ℝ)
        ≤ ∑' m : ℕ, y ^ 2 / 2 * (b / 3) ^ m :=
    hsum_tail.tsum_le_tsum (fun m => exp_coeff_le hb0 hy m) hsum_bnd
  -- Combine with the algebraic identity `y^2/2 * (1 - b/3)⁻¹ = y^2 / (2 * (1 - b/3))`.
  have h1mb3_pos : (0 : ℝ) < 1 - b / 3 := by linarith
  have halg : y ^ 2 / 2 * (1 - b / 3)⁻¹ = y ^ 2 / (2 * (1 - b / 3)) := by
    field_simp
  -- Conclude.
  have hRHS_bound :
      ∑' m : ℕ, y ^ (m + 2) / ((m + 2) ! : ℝ) ≤ y ^ 2 / (2 * (1 - b / 3)) := by
    calc ∑' m : ℕ, y ^ (m + 2) / ((m + 2) ! : ℝ)
        ≤ ∑' m : ℕ, y ^ 2 / 2 * (b / 3) ^ m := h_tsum_le
      _ = y ^ 2 / 2 * (1 - b / 3)⁻¹ := hsum_eq
      _ = y ^ 2 / (2 * (1 - b / 3)) := halg
  linarith [hRHS_bound]

end Real
