/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.MatrixAnalysis.InvAntiOnPos
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.RCLike.Basic

/-!
# Matrix inverse antitonicity via the CStarMatrix path

Lift `cstar_inv_anti_on_pos_units` to the `CStarMatrix n n ℂ` C*-algebra,
working around the `RCLike` matrix typeclass timeouts that blocked round 20.
Requires `open scoped ComplexOrder` for the order structure on `ℂ` to
propagate to `CStarMatrix n n ℂ`.

Sub-step toward the full B6 L3 carrier.
-/

open scoped ComplexOrder

theorem cstarMatrix_inv_anti_on_posDef
    {n : Type*} [Fintype n] [DecidableEq n]
    {A B : CStarMatrix n n ℂ}
    (hA : 0 ≤ (A : CStarMatrix n n ℂ)) (hAunit : IsUnit (A : CStarMatrix n n ℂ))
    (hAB : (A : CStarMatrix n n ℂ) ≤ B) (hBunit : IsUnit (B : CStarMatrix n n ℂ)) :
    (Ring.inverse (B : CStarMatrix n n ℂ)) ≤ Ring.inverse (A : CStarMatrix n n ℂ) := by
  have h := cstar_inv_anti_on_pos_units
    (A := CStarMatrix n n ℂ) (a := hAunit.unit) (b := hBunit.unit)
    (by simpa [IsUnit.unit_spec] using hA)
    (by simpa [IsUnit.unit_spec] using hAB)
  rw [Ring.inverse_of_isUnit hBunit, Ring.inverse_of_isUnit hAunit]
  exact h
