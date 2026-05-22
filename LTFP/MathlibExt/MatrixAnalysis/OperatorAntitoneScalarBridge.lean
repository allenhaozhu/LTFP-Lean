/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.MatrixAnalysis.OperatorMonotone

/-!
# Scalar bridge from `OperatorAntitone` to `AntitoneOn`

Companion to `OperatorConcaveScalarBridge.lean`. If `f : ℝ → ℝ` is
operator-antitone in the matrix sense (`OperatorAntitone f`, defined in
`OperatorMonotone.lean`), then `f` is antitone on the whole real line.
This is the universe-`(0, 0)`-instantiated set-restricted form: we
combine the scalar bridge `OperatorAntitone.antitone` with
`Antitone.antitoneOn`.
-/

namespace LTFP.MathlibExt.MatrixAnalysis

/-- An operator-antitone function is antitone on `Set.univ`. -/
theorem OperatorAntitone.antitoneOn_univ {f : ℝ → ℝ}
    (hf : OperatorAntitone.{0, 0} f) : AntitoneOn f Set.univ :=
  (OperatorAntitone.antitone hf).antitoneOn _

end LTFP.MathlibExt.MatrixAnalysis
