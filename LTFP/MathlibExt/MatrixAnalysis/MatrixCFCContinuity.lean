/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Continuity of the matrix continuous functional calculus log

For a finite index type `n`, the map `A ↦ CFC.log A : Matrix n n ℂ → Matrix n n ℂ`
is continuous on the Loewner-spectral box

  `{A : Matrix n n ℂ | A.IsHermitian ∧ r • 1 ≤ A ∧ A ≤ R' • 1}`

whenever `0 < r ≤ R'`. The proof uses Mathlib's `ContinuousOn.cfc'`
together with the scoped `CStarAlgebra (Matrix n n ℂ)` instance from
`LiebTraceComplementary.lean` (under `Matrix.Norms.L2Operator`), which
unlocks `IsometricContinuousFunctionalCalculus ℝ _ IsSelfAdjoint`.

The result feeds Part 7b of the matrix Bernstein chain (Bochner Jensen
for `Re tr exp(H + log A)` over the bounded strict-positive slice).

## Main results

* `Matrix.continuousOn_log_strict_pos_slice` — `CFC.log` is continuous
  on `{A | A.IsHermitian ∧ r • 1 ≤ A ∧ A ≤ R' • 1}` for `0 < r`.

* `Matrix.continuousOn_re_trace_exp_H_plus_log` — the composed Bochner
  Jensen functional `A ↦ Re tr exp(H + log A)` is continuous on the
  same slice (using `continuous_re_trace_exp` from
  `MatrixExpPositivity.lean`).
-/
import LTFP.MathlibExt.MatrixAnalysis.LiebTraceComplementary
import LTFP.MathlibExt.MatrixAnalysis.MatrixExpPositivity
import LTFP.MathlibExt.MatrixAnalysis.PosSemidefClosed
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator CFC.Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The spectrum of a matrix on the Loewner-spectral box
`{A | r • 1 ≤ A ∧ A ≤ R' • 1}` is contained in `[r, R']`.

This is the `algebraMap`-based spectrum localization: under the scoped
`CStarAlgebra (Matrix n n ℂ)` instance, the order is the standard
`StarOrderedRing` order on a C⋆-algebra, and the Loewner bounds translate
to spectrum bounds via `algebraMap_le_iff_le_spectrum` and
`le_algebraMap_iff_spectrum_le`. -/
theorem spectrum_subset_Icc_of_smul_one_le_of_le_smul_one
    {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {r R' : ℝ} (h_low : r • (1 : Matrix n n ℂ) ≤ A)
    (h_up : A ≤ R' • (1 : Matrix n n ℂ)) :
    spectrum ℝ A ⊆ Set.Icc r R' := by
  -- Translate the smul bounds to algebraMap bounds.
  have h_low' : algebraMap ℝ (Matrix n n ℂ) r ≤ A := by
    rwa [Algebra.algebraMap_eq_smul_one]
  have h_up' : A ≤ algebraMap ℝ (Matrix n n ℂ) R' := by
    rwa [Algebra.algebraMap_eq_smul_one]
  have hAsa : IsSelfAdjoint A := hA.isSelfAdjoint
  -- Now both are spectrum conditions via the CStarAlgebra-side API.
  intro x hx
  refine ⟨?_, ?_⟩
  · exact (algebraMap_le_iff_le_spectrum (r := r) (a := A) hAsa).mp h_low' x hx
  · exact (le_algebraMap_iff_spectrum_le (r := R') (a := A) hAsa).mp h_up' x hx

set_option maxHeartbeats 400000 in
/-- **Main result**: the CFC logarithm is continuous on the bounded
strict-positive Loewner slice of `Matrix n n ℂ`.

For `0 < r`, the map `A ↦ CFC.log A` is continuous on

  `{A : Matrix n n ℂ | A.IsHermitian ∧ r • 1 ≤ A ∧ A ≤ R' • 1}`.

The proof uses Mathlib's `ContinuousOn.cfc'` with the scoped
`CStarAlgebra (Matrix n n ℂ)` instance under `Matrix.Norms.L2Operator`,
which provides the `IsometricContinuousFunctionalCalculus ℝ _ IsSelfAdjoint`
needed for `ContinuousOn.cfc'` to apply. `Real.log` is continuous on the
compact `Set.Icc r R'` (away from zero since `0 < r`). -/
theorem continuousOn_log_strict_pos_slice
    [Nonempty n] (r R' : ℝ) (hr : 0 < r) :
    ContinuousOn (fun A : Matrix n n ℂ => CFC.log A)
      {A : Matrix n n ℂ |
        A.IsHermitian ∧
        r • (1 : Matrix n n ℂ) ≤ A ∧
        A ≤ R' • (1 : Matrix n n ℂ)} := by
  -- Unfold `CFC.log = cfc Real.log`.
  show ContinuousOn (fun A : Matrix n n ℂ => cfc Real.log A) _
  -- Apply `ContinuousOn.cfc'` with `s = Set.Icc r R'`.
  -- Conditions: `IsCompact s`, identity is continuous, spectrum ⊆ s,
  -- predicate `IsSelfAdjoint` holds, and `Real.log` is continuous on `s`.
  have hcompact : IsCompact (Set.Icc r R') := isCompact_Icc
  have hlog_cont : ContinuousOn Real.log (Set.Icc r R') := by
    apply ContinuousOn.mono Real.continuousOn_log
    intro x hx hx_zero
    have hx_pos : 0 < x := lt_of_lt_of_le hr hx.1
    exact absurd hx_zero (ne_of_gt hx_pos)
  refine ContinuousOn.cfc' (𝕜 := ℝ) hcompact Real.log
    (a := fun A : Matrix n n ℂ => A) continuousOn_id ?_ ?_ hlog_cont
  · -- spectrum bound
    intro A hA
    exact spectrum_subset_Icc_of_smul_one_le_of_le_smul_one hA.1 hA.2.1 hA.2.2
  · -- IsSelfAdjoint predicate
    intro A hA
    exact hA.1.isSelfAdjoint

/-- **Useful corollary**: the composed Bochner-Jensen functional
`A ↦ Re tr exp(H + CFC.log A)` is continuous on the bounded strict-positive
Loewner slice.

This is the form needed for Part 7b of the matrix Bernstein chain. -/
theorem continuousOn_re_trace_exp_H_plus_log
    [Nonempty n] (H : Matrix n n ℂ) (r R' : ℝ) (hr : 0 < r) :
    ContinuousOn
      (fun A : Matrix n n ℂ => (Matrix.trace (NormedSpace.exp (H + CFC.log A))).re)
      {A : Matrix n n ℂ |
        A.IsHermitian ∧
        r • (1 : Matrix n n ℂ) ≤ A ∧
        A ≤ R' • (1 : Matrix n n ℂ)} := by
  -- Composition: A ↦ CFC.log A → H + · → Re tr exp.
  have h1 : ContinuousOn (fun A : Matrix n n ℂ => H + CFC.log A)
      {A : Matrix n n ℂ |
        A.IsHermitian ∧
        r • (1 : Matrix n n ℂ) ≤ A ∧
        A ≤ R' • (1 : Matrix n n ℂ)} :=
    continuousOn_const.add (continuousOn_log_strict_pos_slice r R' hr)
  exact continuous_re_trace_exp.continuousOn.comp h1 (fun A _ => Set.mem_univ _)

end Matrix
