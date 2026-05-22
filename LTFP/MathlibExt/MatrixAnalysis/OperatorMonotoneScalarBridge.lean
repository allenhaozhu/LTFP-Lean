/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.MatrixAnalysis.OperatorMonotone

/-!
# Scalar bridge from `OperatorMonotone` to `MonotoneOn`

Companion to `OperatorAntitoneScalarBridge.lean` and
`OperatorConcaveScalarBridge.lean`. If `f : ℝ → ℝ` is operator-monotone
in the matrix sense (`OperatorMonotone f`, defined in
`OperatorMonotone.lean`), then `f` is monotone on the whole real line.
This is the universe-`(0, 0)`-instantiated set-restricted form: we
combine the scalar bridge `OperatorMonotone.monotone` with
`Monotone.monotoneOn`.
-/

namespace LTFP.MathlibExt.MatrixAnalysis

/-- An operator-monotone function is monotone on `Set.univ`. -/
theorem OperatorMonotone.monotoneOn_univ {f : ℝ → ℝ}
    (hf : OperatorMonotone.{0, 0} f) : MonotoneOn f Set.univ :=
  (OperatorMonotone.monotone hf).monotoneOn _

end LTFP.MathlibExt.MatrixAnalysis
