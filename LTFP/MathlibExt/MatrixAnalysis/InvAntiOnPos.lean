/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic

/-!
# Operator-antitone inversion on positive elements

Two complementary forms of the fact that `t ↦ 1/t` is order-reversing on
positive elements:

1. Scalar form: `t ↦ t⁻¹` is antitone on `Set.Ioi (0 : ℝ)`.
2. CStarAlgebra form: in a C*-algebra, if `0 ≤ a` and `a ≤ b` (with both
   units), then `b⁻¹ ≤ a⁻¹`.

Sub-steps toward the full B6 L3 `operatorAntitone_inv_on_pos` statement
(which is blocked on the partial-domain refactor of the `OperatorAntitone`
predicate).
-/

theorem cstar_inv_anti_on_pos_units
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] {a b : Aˣ}
    (ha : 0 ≤ (a : A)) (hab : (a : A) ≤ b) :
    ((b⁻¹ : Aˣ) : A) ≤ ((a⁻¹ : Aˣ) : A) := by
  exact CStarAlgebra.inv_le_inv ha hab

theorem inv_antitoneOn_Ioi_real :
    AntitoneOn (fun t : ℝ => t⁻¹) (Set.Ioi 0) := by
  simpa [one_div] using (inv_antitoneOn_Ioi (α := ℝ))
