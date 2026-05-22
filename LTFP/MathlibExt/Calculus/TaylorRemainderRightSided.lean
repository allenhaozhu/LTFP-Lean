/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.Calculus.Taylor

/-!
# Right-sided Taylor remainder bound

For a `ContDiff ℝ 2` function `f` and `x₀ < x`, if the second derivative
is bounded by `M` on `[x₀, x]`, then
`|f(x) - taylorWithinEval f 1 ... x₀ x| ≤ (M/2) (x - x₀)²`.

Sub-step toward the full B8 N5 uniform-on-ball Taylor remainder
(the symmetric / two-sided extension is the missing piece).
-/

open Set

theorem taylor_remainder_bound_right
    {f : ℝ → ℝ} {x₀ x M : ℝ} (hf : ContDiff ℝ 2 f) (hx : x₀ < x)
    (hM : ∀ y ∈ Icc x₀ x, |iteratedDeriv 2 f y| ≤ M) :
    |f x - taylorWithinEval f 1 (Icc x₀ x) x₀ x|
      ≤ (M / 2) * (x - x₀) ^ 2 := by
  have hContDiffOn : ContDiffOn ℝ (1 + 1 : ℕ) f (Icc x₀ x) := by
    simpa using hf.contDiffOn
  obtain ⟨ξ, hξ, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (f := f) (x := x) (x₀ := x₀)
      (n := 1) hx hContDiffOn
  have hξIcc : ξ ∈ Icc x₀ x := ⟨le_of_lt hξ.1, le_of_lt hξ.2⟩
  have hpow_nonneg : 0 ≤ (x - x₀) ^ 2 := sq_nonneg _
  have hdiv_nonneg : 0 ≤ (x - x₀) ^ 2 / 2 := div_nonneg hpow_nonneg (by norm_num)
  calc
    |f x - taylorWithinEval f 1 (Icc x₀ x) x₀ x|
        = |iteratedDeriv 2 f ξ * (x - x₀) ^ 2 / 2| := by
          rw [hrem]; simp
    _ = |iteratedDeriv 2 f ξ| * ((x - x₀) ^ 2 / 2) := by
          rw [abs_div, abs_mul, abs_of_nonneg hpow_nonneg,
              abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2), mul_div_assoc]
    _ ≤ M * ((x - x₀) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_right (hM ξ hξIcc) hdiv_nonneg
    _ = (M / 2) * (x - x₀) ^ 2 := by ring
