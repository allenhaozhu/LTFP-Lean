/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.Ch14_Probabilistic.PACBayes

/-! # Bach §14.4.2 — PAC-Bayes Step 1: per-θ Hoeffding linear MGF

**Problem.** Bach (2024, §14.4.2, p. 424, Eq. 14.4) opens the PAC-Bayes
McAllester derivation with a per-hypothesis Hoeffding MGF bound: for a
single fixed hypothesis `θ` whose loss `ℓ_θ : 𝒳 → ℝ` is `[0, ℓ∞]`-bounded
a.e. under the data distribution `D`, the moment-generating function of
the centered empirical-process gap

  `gap(S) := R(θ) - R̂_n(θ, S)
            = (∫ ℓ_θ dD) - (1/n) ∑_{i=1}^{n} ℓ_θ(Sᵢ)`

under the product measure `Dⁿ` satisfies

  `∫_S exp(s · gap(S)) dDⁿ(S) ≤ exp(s² · ℓ∞² / (8 n))`.

This is the **first** of the four steps in Bach's §14.4.2 chain
(per-θ Hoeffding → integrate over the prior → Donsker-Varadhan →
Chernoff exponentiation), and the only one that does *not* yet
involve the posterior `Q`.

**Hints**:
- LTlib lemma: `LTFP.pac_bayes_bach_step1_hoeffding_per_theta` in
  `LTFP/Ch14_Probabilistic/PACBayes.lean` (line 1345).
- The lemma's conclusion exactly matches the target up to symbol
  renaming; supply the hypotheses through.
- Expected length: 1-3 lines.
- Common pitfall: the convention is `R - R̂_n` (population minus
  empirical), NOT `R̂_n - R`. Bach (2024) Eq. (14.4) uses the former.
  The carrier matches this orientation exactly; do not negate.

**How to verify**: replace `sorry` with your proof, then run
`lake build LTFP.Ch14_Probabilistic` from the repo root.
-/

open MeasureTheory

namespace LTFP.StudentProblems.Ch14

/-- §14.4.2 — Per-θ Hoeffding linear-MGF bound (Bach Eq. 14.4). -/
theorem student_problem_ch14_pac_bayes_step1
    {𝒳 : Type*} [MeasurableSpace 𝒳]
    (D : MeasureTheory.Measure 𝒳) [MeasureTheory.IsProbabilityMeasure D]
    (ℓ : 𝒳 → ℝ) (hℓ_meas : Measurable ℓ)
    (linf : ℝ)
    (hbdd : ∀ᵐ x ∂D, ℓ x ∈ Set.Icc (0 : ℝ) linf)
    {n : ℕ} (hn : 0 < n)
    (s : ℝ) :
    ∫ S, Real.exp (s * ((∫ x, ℓ x ∂D) -
            (1 / (n : ℝ)) * ∑ i : Fin n, ℓ (S i)))
          ∂(MeasureTheory.Measure.pi (fun _ : Fin n => D))
      ≤ Real.exp (s ^ 2 * (linf ^ 2 / (8 * (n : ℝ)))) := by
  sorry

end LTFP.StudentProblems.Ch14
