/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.MatrixAnalysis.OperatorConcaveScalarBridge
import Mathlib.Analysis.Convex.Function

/-!
# Scalar bridges for `OperatorConvex`

Convex companion to `OperatorConcaveScalarBridge.lean`: operator-convex
functions are scalar-convex, and their negation is scalar-concave.
-/

namespace LTFP.MathlibExt.MatrixAnalysis

theorem OperatorConvex.convexOn_univ {f : ℝ → ℝ}
    (hf : OperatorConvex.{0, 0} f) : ConvexOn ℝ Set.univ f := by
  have hconc : OperatorConcave.{0, 0} (-f) :=
    (operatorConvex_iff_neg_operatorConcave (f := f)).1 hf
  simpa using (OperatorConcave.concaveOn_univ hconc).neg

theorem OperatorConvex.concaveOn_neg {f : ℝ → ℝ}
    (hf : OperatorConvex.{0, 0} f) : ConcaveOn ℝ Set.univ (fun x => - f x) := by
  exact OperatorConcave.concaveOn_univ
    ((operatorConvex_iff_neg_operatorConcave (f := f)).1 hf)

end LTFP.MathlibExt.MatrixAnalysis
