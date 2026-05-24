/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Algebra.Order.Star.Basic

/-!
# Hansen-Pedersen Jensen inequality for `rpow` on positive elements

This file builds toward `CFC.star_mul_rpow_mul_le_rpow_star_mul`, the
Hansen-Pedersen Jensen inequality: for `0 ≤ a`, `star v * v ≤ 1`,
`p ∈ [0,1]`,
`star v * (a ^ p) * v ≤ (star v * a * v) ^ p`.

This is Part 5 of the B6 L3 carrier closure path (Parts 1–4 already
landed in `CStarShiftedResolventConcave`, `CStarRpowIntegrandConcave`,
`CStarRpowConcave`, `CStarLogConcave`).

The full proof for `p ∈ (0,1)` reduces via the rpow integral
representation to a conjugated shifted-resolvent inequality
(Sub-Part 5.1). This file currently contains the trivial endpoint
cases (`p = 0` and `p = 1`, Sub-Part 5.4).

## Main results

* `CFC.star_mul_rpow_mul_le_rpow_star_mul_zero` — endpoint `p = 0`:
  reduces to `star v * v ≤ 1`.
* `CFC.star_mul_rpow_mul_le_rpow_star_mul_one` — endpoint `p = 1`:
  reduces to the trivial equality `star v * a * v = star v * a * v`.
-/

namespace LTFP.MathlibExt.MatrixAnalysis

open scoped NNReal

/-- **Hansen-Pedersen Jensen inequality, endpoint `p = 0`.**

For `0 ≤ a` and `star v * v ≤ 1`, we have
`star v * (a ^ (0 : ℝ)) * v ≤ (star v * a * v) ^ (0 : ℝ)`.

Both sides collapse via `CFC.rpow_zero`: the left side becomes
`star v * 1 * v = star v * v`, the right side becomes `1`, and the
inequality is exactly the hypothesis `hv`. -/
lemma CFC.star_mul_rpow_mul_le_rpow_star_mul_zero
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a v : A} (ha : 0 ≤ a) (hv : star v * v ≤ 1) :
    star v * (a ^ (0 : ℝ)) * v ≤ (star v * a * v) ^ (0 : ℝ) := by
  have hvav : 0 ≤ star v * a * v := star_left_conjugate_nonneg ha v
  rw [_root_.CFC.rpow_zero a ha, _root_.CFC.rpow_zero (star v * a * v) hvav,
    mul_one]
  exact hv

/-- **Hansen-Pedersen Jensen inequality, endpoint `p = 1`.**

For `0 ≤ a` and `star v * v ≤ 1`, we have
`star v * (a ^ (1 : ℝ)) * v ≤ (star v * a * v) ^ (1 : ℝ)`.

Both sides collapse via `CFC.rpow_one` to `star v * a * v`, so the
inequality is reflexivity. The hypothesis `hv` is not used here but
is retained so the lemma signature matches the general statement
`star_mul_rpow_mul_le_rpow_star_mul` for arbitrary `p ∈ [0,1]`. -/
lemma CFC.star_mul_rpow_mul_le_rpow_star_mul_one
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a v : A} (ha : 0 ≤ a) (hv : star v * v ≤ 1) :
    star v * (a ^ (1 : ℝ)) * v ≤ (star v * a * v) ^ (1 : ℝ) := by
  have hvav : 0 ≤ star v * a * v := star_left_conjugate_nonneg ha v
  rw [_root_.CFC.rpow_one a ha, _root_.CFC.rpow_one (star v * a * v) hvav]

end LTFP.MathlibExt.MatrixAnalysis
