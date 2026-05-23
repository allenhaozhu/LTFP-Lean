/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# Operator-monotone powers on nonnegative CStarMatrix type copies

This file records a finite-matrix-facing wrapper around Mathlib's C⋆-algebra
operator-monotonicity theorem for powers `t ↦ t ^ p`, `p ∈ [0, 1]`.

The existing universal `OperatorMonotone` predicate for `Matrix n n 𝕜`
quantifies over all Hermitian matrices, with no positivity/domain hypothesis.
That predicate is intentionally not used for `Real.rpow`, since `Real.rpow`
is not monotone on all of `ℝ`.

Also includes the strictly-positive-cone variant
`CStarOperatorMonotoneOnStrictlyPos` and the corresponding `Real.log`
instance via `CFC.log_monotoneOn`.
-/

namespace LTFP.MathlibExt.MatrixAnalysis

universe uA un

/-- A real function is operator monotone on the nonnegative cone of finite
`CStarMatrix` type copies if real CFC by that function preserves spectral order
there. -/
def CStarOperatorMonotoneOnNonneg (f : ℝ → ℝ) : Prop :=
  ∀ {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {n : Type un} [Fintype n] [DecidableEq n],
    MonotoneOn (fun M : CStarMatrix n n A => cfc f M) {M | 0 ≤ M}

/-- `t ↦ t ^ p` is operator monotone on the nonnegative cone of finite
`CStarMatrix` type copies for `p ∈ [0, 1]`. -/
theorem cStarOperatorMonotoneOnNonneg_rpow {p : ℝ} (hp : p ∈ Set.Icc 0 1) :
    CStarOperatorMonotoneOnNonneg.{uA, un} (fun t : ℝ => t ^ p) := by
  intro A _ _ _ n _ _ M hM N hN hMN
  change cfc (fun t : ℝ => t ^ p) M ≤ cfc (fun t : ℝ => t ^ p) N
  rw [← CFC.rpow_eq_cfc_real (a := M) (y := p) hM,
    ← CFC.rpow_eq_cfc_real (a := N) (y := p) hN]
  exact CFC.monotone_rpow (A := CStarMatrix n n A) hp hMN

/-- A real function is operator monotone on the strictly-positive cone of finite
`CStarMatrix` type copies if real CFC by that function preserves spectral order
on strictly-positive matrices. -/
def CStarOperatorMonotoneOnStrictlyPos (f : ℝ → ℝ) : Prop :=
  ∀ {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {n : Type un} [Fintype n] [DecidableEq n],
    MonotoneOn (fun M : CStarMatrix n n A => cfc f M)
      {M | IsStrictlyPositive M}

/-- The natural logarithm `Real.log` is operator monotone on the strictly-positive
cone of finite `CStarMatrix` type copies, via Mathlib's `CFC.log_monotoneOn`. -/
theorem cStarOperatorMonotoneOnStrictlyPos_log :
    CStarOperatorMonotoneOnStrictlyPos.{uA, un} Real.log := by
  intro A _ _ _ n _ _ M hM N hN hMN
  -- `CFC.log` unfolds to `cfc Real.log`; `CFC.log_monotoneOn` gives the conclusion.
  change cfc Real.log M ≤ cfc Real.log N
  exact CFC.log_monotoneOn (A := CStarMatrix n n A) hM hN hMN

/-- `Real.sqrt` is operator monotone on the nonnegative cone of finite
`CStarMatrix` type copies, as the `p = 1/2` instance of
`cStarOperatorMonotoneOnNonneg_rpow` via the unconditional identity
`Real.sqrt x = x ^ (1/2)`. -/
theorem cStarOperatorMonotoneOnNonneg_sqrt :
    CStarOperatorMonotoneOnNonneg.{uA, un} Real.sqrt := by
  intro A _ _ _ n _ _ M hM N hN hMN
  have hsqrt : (Real.sqrt : ℝ → ℝ) = fun t : ℝ => t ^ (1 / (2 : ℝ)) := by
    funext t; exact Real.sqrt_eq_rpow t
  change cfc Real.sqrt M ≤ cfc Real.sqrt N
  rw [hsqrt]
  exact cStarOperatorMonotoneOnNonneg_rpow.{uA, un}
    (by norm_num : (1 / (2 : ℝ)) ∈ Set.Icc (0 : ℝ) 1) hM hN hMN

end LTFP.MathlibExt.MatrixAnalysis
