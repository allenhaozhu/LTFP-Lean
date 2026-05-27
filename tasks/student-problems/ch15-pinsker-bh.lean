/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.Ch15_LowerBounds.Statistical

/-! # Bach §15.1 — Pinsker / Bretagnolle-Huber inequality

**Problem.** Bach (2024, §15.1, p. 434) uses information-theoretic
inequalities to lower-bound the minimax risk. The classical *Pinsker
inequality* states that total-variation distance is dominated by the
square root of KL divergence:

  `tvDist(μ, ν) ≤ √(KL(μ ‖ ν))`.

This is the **weak (unconditional) Bretagnolle-Huber form**: it holds
for all `μ ≪ ν` with finite KL, without the Csiszár scalar lower bound
that would tighten the bound to `√(KL/2)`. LTlib ships this weak form
as an end-to-end theorem composing the Bretagnolle-Huber chain
(`tvDist_le_sqrt_one_sub_exp_neg_klDiv`) with the algebraic core
`1 - exp(-x) ≤ x`.

**Hints**:
- LTlib lemma: `LTFP.tvDist_le_sqrt_klDiv` in
  `LTFP/Ch15_LowerBounds/Statistical.lean` (line 529).
- This is the **unconditional** weak form `tv ≤ √KL`. The tighter
  classical form `tv ≤ √(KL/2)` is `pinsker_inequality_tvDist` in
  `LTFP/MathlibExt/Probability/Distance/Pinsker.lean`, but it takes
  the Csiszár scalar hypothesis as an input; this problem targets the
  unconditional form.
- Expected length: 1-2 lines (a direct `exact ... `).
- Common pitfall: the conclusion compares `toReal` values
  (`(tvDist μ ν).toReal ≤ Real.sqrt (InformationTheory.klDiv μ ν).toReal`);
  the underlying `ENNReal` versions live in Mathlib's
  `Mathlib.InformationTheory.KullbackLeibler.Basic`. Keep everything
  in `toReal` land for this exercise.

**How to verify**: replace `sorry` with your proof, then run
`lake build LTFP.Ch15_LowerBounds` from the repo root.
-/

open LTFP.MathlibExt.Probability MeasureTheory
open scoped MeasureTheory ENNReal

namespace LTFP.StudentProblems.Ch15

variable {α : Type*} [MeasurableSpace α]

/-- §15.1 — Pinsker / Bretagnolle-Huber unconditional weak form. -/
theorem student_problem_ch15_pinsker_bh
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (hkl : InformationTheory.klDiv μ ν ≠ ∞) :
    (tvDist μ ν).toReal ≤ Real.sqrt (InformationTheory.klDiv μ ν).toReal := by
  sorry

end LTFP.StudentProblems.Ch15
