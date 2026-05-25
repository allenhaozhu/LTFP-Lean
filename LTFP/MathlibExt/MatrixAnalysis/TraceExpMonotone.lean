/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.MatrixAnalysis.MatrixRelEntropy
import LTFP.MathlibExt.MatrixAnalysis.LiebTraceComplementary
import LTFP.MathlibExt.MatrixAnalysis.MatrixExpPositivity
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Trace of the matrix exponential is monotone (real part) under the Loewner order

For Hermitian matrices `A, B : Matrix n n ℂ` with `A ≤ B` in the Loewner
(operator) order, the real part of the trace of the matrix exponential
satisfies

  `Re tr (exp A) ≤ Re tr (exp B)`.

This is the **trace-monotonicity** statement; it is strictly weaker than
operator monotonicity of `exp`. (For noncommuting Hermitian `A, B` with
`A ≤ B`, in general `exp A ≤ exp B` does *not* hold.) The trace version
nonetheless holds and is the form needed for the Bernstein /
log-partition arguments in the matrix Chernoff chain.

## Proof strategy

We route through the **Gibbs variational** characterisation of
`log (Re tr (exp A))` already developed in
`LTFP.MathlibExt.MatrixAnalysis.MatrixRelEntropy`.

Set `Z_A := Re tr (exp A)` and `Z_B := Re tr (exp B)`. Both are strictly
positive (`Matrix.IsHermitian.re_trace_exp_pos`). It suffices to show
`log Z_A ≤ log Z_B`, by `Real.log_le_log_iff`.

`Matrix.gibbs_variational_equality` for `A` produces the **Gibbs state**
`P := Z_A⁻¹ • exp A`, strictly positive with `Re tr P = 1`, satisfying

  `Re tr (P · A) - Re tr (P · log P) = log Z_A`.

By `Matrix.gibbs_variational_inequality` applied to `B` at the *same*
`P`,

  `Re tr (P · B) - Re tr (P · log P) ≤ log Z_B`.

The two together reduce the inequality to

  `Re tr (P · A) ≤ Re tr (P · B)`,

i.e. `0 ≤ Re tr (P · (B - A))`. This is a special case of
`CFC.re_trace_mul_nonneg_of_posSemidef`: both `P` (strictly positive,
hence PSD) and `B - A` (PSD by `A ≤ B` ↔ `Matrix.le_iff`) are positive
semidefinite, so their product has nonnegative trace.

The two ingredients (Gibbs variational equality/inequality + PSD trace
nonnegativity) discharge the inequality without any spectral
decomposition, in keeping with the convex-analytic flavour of the matrix
Bernstein chain.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace Matrix

/-- **Trace-monotonicity of the matrix exponential under the Loewner order.**

For Hermitian `A, B : Matrix n n ℂ` with `A ≤ B` in the Loewner order,

  `Re tr (exp A) ≤ Re tr (exp B)`.

This is a strictly weaker statement than operator monotonicity of `exp`
(which fails for noncommuting Hermitian arguments); the trace version
holds and is the form required for log-partition / Bernstein arguments.

The proof routes through the Gibbs variational characterisation of
`log (Re tr (exp H))` (see `Matrix.gibbs_variational_equality` and
`Matrix.gibbs_variational_inequality`), combined with the PSD-trace
nonnegativity `CFC.re_trace_mul_nonneg_of_posSemidef`. -/
theorem re_trace_exp_mono_of_hermitian_le
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hAB : A ≤ B) :
    (Matrix.trace (NormedSpace.exp A)).re ≤ (Matrix.trace (NormedSpace.exp B)).re := by
  classical
  -- Set `Z_A := Re tr (exp A)` and `Z_B := Re tr (exp B)`; both are positive.
  set Z_A : ℝ := (Matrix.trace (NormedSpace.exp A : Matrix n n ℂ)).re with hZA_def
  set Z_B : ℝ := (Matrix.trace (NormedSpace.exp B : Matrix n n ℂ)).re with hZB_def
  have hZA_pos : 0 < Z_A := Matrix.IsHermitian.re_trace_exp_pos hA
  have hZB_pos : 0 < Z_B := Matrix.IsHermitian.re_trace_exp_pos hB
  -- It suffices to show `Real.log Z_A ≤ Real.log Z_B`, then strip the `log`.
  refine (Real.log_le_log_iff hZA_pos hZB_pos).mp ?_
  -- Extract the Gibbs state `P` for `A` from `gibbs_variational_equality`.
  obtain ⟨P, hP_sp, hPtrace, hP_eq⟩ := Matrix.gibbs_variational_equality hA
  -- `hP_eq : (trace (P * A)).re - (trace (P * CFC.log P)).re = log Z_A`.
  rw [← hZA_def] at hP_eq
  -- Apply the Gibbs variational inequality at `B` with the same `P`.
  have hGV_B :
      (Matrix.trace (P * B)).re - (Matrix.trace (P * CFC.log P)).re ≤
        Real.log Z_B :=
    Matrix.gibbs_variational_inequality hB hP_sp hPtrace
  -- Show `(trace (P * A)).re ≤ (trace (P * B)).re` via PSD-trace nonnegativity.
  -- `P` is PSD (since strictly positive) and `B - A` is PSD (from `A ≤ B`).
  have hP_psd : P.PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp hP_sp.nonneg
  have hBA_psd : (B - A).PosSemidef := Matrix.le_iff.mp hAB
  have hnn : 0 ≤ (Matrix.trace (P * (B - A))).re :=
    CFC.re_trace_mul_nonneg_of_posSemidef hP_psd hBA_psd
  -- Distribute: `P * (B - A) = P * B - P * A`, so the trace splits.
  have htr_split :
      Matrix.trace (P * (B - A)) = Matrix.trace (P * B) - Matrix.trace (P * A) := by
    rw [Matrix.mul_sub, Matrix.trace_sub]
  have htr_split_re :
      (Matrix.trace (P * (B - A))).re =
        (Matrix.trace (P * B)).re - (Matrix.trace (P * A)).re := by
    rw [htr_split, Complex.sub_re]
  have hPA_le_PB :
      (Matrix.trace (P * A)).re ≤ (Matrix.trace (P * B)).re := by
    have := hnn
    rw [htr_split_re] at this
    linarith
  -- Combine: `log Z_A = Re tr (P · A) - Re tr (P · log P)
  --                 ≤ Re tr (P · B) - Re tr (P · log P)
  --                 ≤ log Z_B`.
  linarith [hP_eq, hGV_B, hPA_le_PB]

end Matrix
