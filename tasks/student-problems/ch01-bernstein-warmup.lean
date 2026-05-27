/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.Moments.BernsteinTextbook

/-! # Bach §1.2.1 — Bernstein/Hoeffding MGF warm-up

**Problem.** Bach (2024, §1.2.3, p. 14, Lemma 1.2.3(a)) gives a textbook-strict
Taylor bound on the moment-generating function (MGF) of a centered, bounded
random variable. Here you re-state the same bound in the *symmetric* `|s|·c < 3`
regime: for `Z : Ω → ℝ` with `|Z| ≤ c` a.e. under a probability measure `μ`,
`∫ Z dμ = 0`, and variance `σ² := ∫ Z² dμ`, prove that for any `s` with
`|s|·c < 3`,

  `∫ exp(s·Z) dμ ≤ exp(s² · σ² / (2 · (1 - |s|·c / 3)))`.

This is one direct application of LTlib's textbook-strict carrier
`ProbabilityTheory.bach_taylor_mgf`.

**Hints**:
- LTlib lemma: `ProbabilityTheory.bach_taylor_mgf` in
  `LTFP/MathlibExt/Probability/Moments/BernsteinTextbook.lean` (line 273).
- The carrier already gives the exact conclusion: pass the hypotheses through.
- Expected length: 1-3 lines (a single `exact ... ` or `apply ...`).
- Common pitfall: the carrier takes `sigma2` as an *argument* together with
  the *definitional* hypothesis `hsigma2_def : sigma2 = ∫ ω, (Z ω) ^ 2 ∂μ`;
  do not forget to supply the `rfl` witness for `hsigma2_def`.

**How to verify**: replace `sorry` with your proof, then run
`lake build LTFP.MathlibExt.Probability.Moments.BernsteinTextbook` from
the repo root to confirm the surrounding context still compiles, and
open this file in VS Code to view the goal state.
-/

open MeasureTheory ProbabilityTheory Real

namespace LTFP.StudentProblems.Ch01

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- §1.2.3 — Symmetric Bernstein/Hoeffding MGF warm-up. -/
theorem student_problem_ch01_bernstein_mgf
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (hZ_meas : Measurable Z)
    (c : ℝ) (hc : 0 ≤ c)
    (h_bdd : ∀ᵐ ω ∂μ, |Z ω| ≤ c)
    (h_centered : ∫ ω, Z ω ∂μ = 0)
    (s : ℝ) (hsc : |s| * c < 3) :
    ∫ ω, Real.exp (s * Z ω) ∂μ ≤
      Real.exp (s ^ 2 * (∫ ω, (Z ω) ^ 2 ∂μ) /
        (2 * (1 - |s| * c / 3))) := by
  sorry

end LTFP.StudentProblems.Ch01
