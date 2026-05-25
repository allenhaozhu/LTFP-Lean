/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Strict positivity of the matrix exponential of a Hermitian matrix

For a Hermitian matrix `H : Matrix n n ℂ`, the matrix exponential
`NormedSpace.exp H` is strictly positive: it is positive semidefinite
(since `H` is self-adjoint and `exp` of a self-adjoint element is
nonnegative in the CFC order) and a unit (matrix exponentials are
always invertible in finite dimension).

The predicate `IsStrictlyPositive a` from `Mathlib.Algebra.Algebra.StrictPositivity`
unfolds to `0 ≤ a ∧ IsUnit a`; both halves are direct one-liner
consequences of named Mathlib lemmas:

* `IsSelfAdjoint.exp_nonneg` gives `0 ≤ NormedSpace.exp H`.
* `Matrix.isUnit_exp`         gives `IsUnit (NormedSpace.exp H)`.

This small bridge is used throughout the matrix Bernstein chain
(parts 6–8) and elsewhere in the LTFP matrix-analysis layer.
-/
import Mathlib.Algebra.Algebra.StrictPositivity
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian

namespace Matrix

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

set_option maxHeartbeats 400000 in
/-- The matrix exponential of a Hermitian matrix is strictly positive.

`IsStrictlyPositive` unfolds (per Mathlib's `StrictPositivity` file) to
`0 ≤ M ∧ IsUnit M`, and both conjuncts follow from named lemmas:

* `0 ≤ NormedSpace.exp H` — from `IsSelfAdjoint.exp_nonneg`, composed
  with the bridge `Matrix.IsHermitian.isSelfAdjoint`.
* `IsUnit (NormedSpace.exp H)` — from `Matrix.isUnit_exp` (the matrix
  exponential is always invertible in finite dimension).
-/
theorem IsHermitian.isStrictlyPositive_exp
    {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    IsStrictlyPositive (NormedSpace.exp H : Matrix n n ℂ) := by
  have hH_sa : IsSelfAdjoint H := hH.isSelfAdjoint
  have hexp_nn : (0 : Matrix n n ℂ) ≤ NormedSpace.exp H := hH_sa.exp_nonneg
  have hexp_unit : IsUnit (NormedSpace.exp H : Matrix n n ℂ) := Matrix.isUnit_exp H
  exact hexp_unit.isStrictlyPositive hexp_nn

/-- The real-part trace of the matrix exponential is continuous.

Composition of three continuous maps:

* `NormedSpace.exp : Matrix n n ℂ → Matrix n n ℂ` is continuous
  (`NormedSpace.exp_continuous`).
* `Matrix.trace : Matrix n n ℂ → ℂ` is continuous as a finite-dimensional
  ℂ-linear map (via `Matrix.traceLinearMap` and
  `LinearMap.continuous_of_finiteDimensional`).
* `Complex.re : ℂ → ℝ` is continuous (`Complex.continuous_re`).

This continuity is used in the matrix Bernstein chain for limit
arguments on `Re tr (exp H)` over parameter families.
-/
theorem continuous_re_trace_exp
    {n : Type*} [Fintype n] [DecidableEq n] :
    Continuous (fun H : Matrix n n ℂ => (Matrix.trace (NormedSpace.exp H)).re) := by
  let +nondep : NormedAlgebra ℚ (Matrix n n ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ (Matrix n n ℂ)
  have htrace : Continuous (Matrix.trace : Matrix n n ℂ → ℂ) :=
    (Matrix.traceLinearMap n ℂ ℂ).continuous_of_finiteDimensional
  exact Complex.continuous_re.comp (htrace.comp NormedSpace.exp_continuous)

end Matrix
