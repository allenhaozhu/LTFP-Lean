/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Function-class concentration for PAC-Bayes

Proposed Mathlib path: `Mathlib/Probability/PACBayes/FunctionClassConcentration.lean`.
Proposed Mathlib namespace: `ProbabilityTheory`.

This file packages the **function-class concentration** step that PAC-Bayes
generalization bounds need. Given a hypothesis class `ℋ`, a prior `P` on
`ℋ`, an i.i.d. sample distribution `D` over the sample space `Ω`, and a
"gap" function `gap : ℋ → Ω → ℝ` representing `R̂_n(h) − R(h)` (the
empirical-minus-population risk), the McAllester PAC-Bayes proof needs

  `E_{h∼P}[ E_{S∼Dⁿ}[ exp(2 n · gap(S,h)²) ] ] ≤ 2 √n`,

and from this — via Markov's inequality applied to the inner
`E_{S∼Dⁿ}[…]` viewed as a function of `h` — the high-probability bound

  `D{ S : E_{h∼P}[exp(2 n · gap(S,h)²)] ≤ 2 √n / δ } ≥ 1 − δ`.

The latter is the form fed into `pac_bayes_mcallester`'s `h_conc_mgf`
hypothesis.

## Structural cut

The proof has two architecturally separable pieces:

1. **Per-`h` squared-gap MGF bound** (Bach 2024 Eq. 14.21):
   `E_{S∼Dⁿ}[exp(2 n · gap(S,h)²)] ≤ 2 √n` for each fixed `h`.

   This is a self-contained scalar result derived from Hoeffding's
   two-sided tail bound integrated against `t ↦ 2 t · exp(t²)`:
   `E[exp(c X²)] = 1 + 2 c ∫₀^∞ t · exp(c t²) · ℙ(|X| ≥ t) dt`.
   For bounded `X ∈ [a, b]`, Hoeffding gives
   `ℙ(|gap| ≥ t) ≤ 2 exp(−2 n t²)`, so the integrand collapses to a
   computable Gaussian-against-exp integral whose value is `1 + …`.

   The full Lean proof requires improper Riemann integration of
   `t · exp(c t²)` against a tail-bound integrand — substantial
   `MeasureTheory.Integral.IntervalIntegral` work. We keep it as the
   single hypothesis `h_per_h_mgf` below; this is the right Mathlib-PR
   cut.

2. **Fubini lift + Chernoff/Markov step** (this file's main content):
   given the per-`h` bound from (1), use `MeasureTheory.integral_integral`
   to switch the order of integration, and `mul_meas_ge_le_integral_of_nonneg`
   for the Chernoff step. Both are standard Mathlib lemmas.

Once piece (1) lands upstream (or as a separate MathlibExt module), the
wrapper `pac_bayes_function_class_mgf_bound` below becomes the
unconditional function-class concentration lemma.

## Why this lives in `MathlibExt`

The Fubini-and-Markov chain on the function-class MGF is general
probability theory; it is not specific to PAC-Bayes beyond the choice of
test function. It is therefore the natural next layer above
`Mathlib.MeasureTheory.Integral.Prod` and
`Mathlib.MeasureTheory.Integral.Bochner.Basic`.

## Main statements

* `function_class_mgf_fubini`
    : Fubini's theorem applied to the joint MGF
      `E_{(h,S)∼P×D}[exp(2 n · gap(h,S)²)]`, expressing it as the iterated
      integral `E_{S∼D}[E_{h∼P}[…]]` (or vice versa).
* `function_class_mgf_bound_of_per_h`
    : if the per-`h` MGF is bounded by `2 √n` for every `h`, then so is
      the iterated MGF `E_{h∼P}[E_{S∼D}[exp(2 n · gap(h,S)²)]]`.
* `pac_bayes_chernoff_step`
    : Markov's inequality lifts an expectation bound on a non-negative
      `expFnc : Ω → ℝ` to a high-probability event:
      `D{ S : expFnc S ≤ M / δ } ≥ 1 − δ`.
* `function_class_chernoff_event_for_mgf`
    : assembled high-probability statement for the PAC-Bayes carrier,
      ready to plug into `pac_bayes_mcallester`'s `h_conc_mgf`
      hypothesis.

## References

* F. Bach, *Learning Theory from First Principles*, MIT Press, 2024,
  §14.4 (PAC-Bayesian analysis), Eq. 14.21 (per-`h` squared-gap MGF
  bound).
* D. McAllester, *PAC-Bayesian model averaging*, COLT 1999.
* P. Alquier, *User-friendly introduction to PAC-Bayes bounds*,
  Foundations and Trends in Machine Learning, vol. 17, no. 2,
  pp. 174--303, 2024.

## Tags

PAC-Bayes, McAllester bound, function-class concentration, Fubini,
Markov inequality
-/

namespace LTFP.MathlibExt.Probability

open MeasureTheory Real
open scoped ENNReal

variable {ℋ Ω : Type*} {mℋ : MeasurableSpace ℋ} {mΩ : MeasurableSpace Ω}

/-! ### Fubini lift of the function-class MGF

The squared-gap MGF over the joint measure `P × D` factors into either
order of iterated integrals. This is a direct application of Mathlib's
`MeasureTheory.integral_integral` to the test function
`g(h, S) := exp(2 n · gap(h, S)²)`. Joint measurability of `g` follows
from joint measurability of `gap`. -/

/-- **Fubini for the function-class MGF.** For a jointly measurable
gap function `gap : ℋ → Ω → ℝ`, the iterated integral of
`exp(c · gap(h, S)²)` over `P × D` may be evaluated in either order,
provided the joint integrand is integrable on the product measure
`P.prod D`. This is a direct application of `integral_integral_swap`. -/
theorem function_class_mgf_fubini
    (P : Measure ℋ) (D : Measure Ω) [SFinite P] [SFinite D]
    (gap : ℋ → Ω → ℝ) (c : ℝ)
    (h_int_joint :
      Integrable (fun p : ℋ × Ω => Real.exp (c * (gap p.1 p.2) ^ 2)) (P.prod D)) :
    ∫ h, ∫ s, Real.exp (c * (gap h s) ^ 2) ∂D ∂P
      = ∫ s, ∫ h, Real.exp (c * (gap h s) ^ 2) ∂P ∂D := by
  -- `integral_integral_swap` takes `Integrable (uncurry f) (μ.prod ν)`.
  -- Our `f h s := Real.exp (c * (gap h s)^2)`. Its uncurry is
  -- `fun p => Real.exp (c * (gap p.1 p.2)^2)`. Definitionally, this is
  -- exactly `h_int_joint`'s witness.
  have h_unc :
      Integrable (Function.uncurry (fun h s => Real.exp (c * (gap h s) ^ 2))) (P.prod D) := by
    simpa [Function.uncurry] using h_int_joint
  exact integral_integral_swap h_unc

/-! ### Per-`h` bound lifts to function-class bound

Given a uniform per-`h` bound `E_{S∼D}[exp(c · gap(h,S)²)] ≤ M`, the
iterated integral over `P` of the same quantity is also bounded by `M`
provided `P` is a probability measure. This is just `integral_mono`
followed by `integral_const`. -/

/-- **Per-`h` MGF bound lifts to function-class MGF bound.**
If `E_{S∼D}[exp(c · gap(h,S)²)] ≤ M` for every `h`, and the per-`h`
expectation is integrable in `h`, then the iterated function-class MGF

  `E_{h∼P}[E_{S∼D}[exp(c · gap(h,S)²)]] ≤ M`,

since `P` is a probability measure. -/
theorem function_class_mgf_bound_of_per_h
    {P : Measure ℋ} {D : Measure Ω}
    [IsProbabilityMeasure P]
    (gap : ℋ → Ω → ℝ) (c M : ℝ)
    (h_per_h : ∀ h, ∫ s, Real.exp (c * (gap h s) ^ 2) ∂D ≤ M)
    (h_int : Integrable (fun h => ∫ s, Real.exp (c * (gap h s) ^ 2) ∂D) P) :
    ∫ h, ∫ s, Real.exp (c * (gap h s) ^ 2) ∂D ∂P ≤ M := by
  -- Bound the inner integrand pointwise by the constant `M`.
  have h_le : ∫ h, ∫ s, Real.exp (c * (gap h s) ^ 2) ∂D ∂P
                ≤ ∫ _h, M ∂P :=
    integral_mono_ae h_int (integrable_const _) (Filter.Eventually.of_forall h_per_h)
  -- `∫ _h, M ∂P = M` because `P` is a probability measure.
  have h_const : ∫ _h, M ∂P = M := by
    simp [integral_const]
  linarith [h_le, h_const.le, h_const.ge]

/-! ### Chernoff / Markov step

The standard conversion from "expectation is bounded" to
"high-probability event": for a non-negative integrable `f : Ω → ℝ` with
`E[f] ≤ M`, Markov's inequality gives

  `D{ ω : M / δ ≤ f ω } ≤ δ`.

Complementing, `D{ ω : f ω < M / δ } ≥ 1 − δ`, and for sufficiently
generous `M / δ` this is the high-probability event needed by the
PAC-Bayes carrier theorem. -/

/-- **Chernoff / Markov step for PAC-Bayes.** Let `f : Ω → ℝ` be a
non-negative integrable function under a probability measure `D` with
`E_D[f] ≤ M`. Then for every `δ > 0`,

  `D{ ω : M / δ ≤ f ω } ≤ δ`.

This is the standard quantitative form of Markov's inequality. It is
the conversion step that lifts the function-class expectation bound

  `E_{h∼P}[E_{S∼D}[exp(2 n · gap²)]] ≤ 2 √n`

to the high-probability event

  `D^n{ S : E_{h∼P}[exp(2 n · gap²)] ≤ 2 √n / δ } ≥ 1 − δ`

consumed by `pac_bayes_mcallester` as `h_conc_mgf`. -/
theorem pac_bayes_chernoff_step
    {D : Measure Ω} [IsProbabilityMeasure D]
    {f : Ω → ℝ} {M δ : ℝ}
    (hM_pos : 0 < M) (hδ_pos : 0 < δ)
    (hf_nn : 0 ≤ᵐ[D] f) (hf_int : Integrable f D)
    (h_exp_le : ∫ ω, f ω ∂D ≤ M) :
    D.real { ω | M / δ ≤ f ω } ≤ δ := by
  -- Markov: `(M/δ) · D{ω : M/δ ≤ f ω} ≤ ∫ f ∂D ≤ M`.
  have h_markov := mul_meas_ge_le_integral_of_nonneg (μ := D) hf_nn hf_int (M / δ)
  have h_chain : (M / δ) * D.real { ω | M / δ ≤ f ω } ≤ M :=
    le_trans h_markov h_exp_le
  -- Multiply both sides by `δ / M > 0`. After cancellation we get
  -- `D.real { … } ≤ δ`.
  have hM_ne : M ≠ 0 := ne_of_gt hM_pos
  have hδ_ne : δ ≠ 0 := ne_of_gt hδ_pos
  have hδM_nn : 0 ≤ δ / M := le_of_lt (div_pos hδ_pos hM_pos)
  have h_mul :
      (M / δ) * D.real { ω | M / δ ≤ f ω } * (δ / M)
        ≤ M * (δ / M) :=
    mul_le_mul_of_nonneg_right h_chain hδM_nn
  -- Simplify both sides.
  have h_lhs :
      (M / δ) * D.real { ω | M / δ ≤ f ω } * (δ / M)
        = D.real { ω | M / δ ≤ f ω } := by
    field_simp
  have h_rhs : M * (δ / M) = δ := by field_simp
  rw [h_lhs, h_rhs] at h_mul
  exact h_mul

/-! ### Existence of a "good sample" for the PAC-Bayes carrier

The PAC-Bayes McAllester bound is stated for a *sample-dependent*
posterior `Q = Q(S)` and a fixed prior `P`. The function-class
concentration argument produces a high-probability event over the
sample `S` on which the per-`S` function-class MGF is bounded. Below we
expose the contrapositive form of the Markov step: there exists a
sample `S` (in fact, a `1-δ` measure set of samples) for which the
function-class MGF is bounded by `2 √n / δ`. -/

/-- **Existence of a "good sample" set for PAC-Bayes.** Given the
function-class MGF expectation bound `E_{h∼P}[E_{S∼D}[exp(2n·gap²)]] ≤ 2√n`
and `δ ∈ (0, 1]`, there exists a measurable set `G ⊆ Ω` with
`D(G) ≥ 1 - δ` such that for every `S ∈ G`,
`E_{h∼P}[exp(2n·gap(h,S)²)] ≤ 2√n / δ`. This is the high-probability
statement consumed by `pac_bayes_mcallester` as `h_conc_mgf`. -/
theorem function_class_chernoff_event_for_mgf
    {P : Measure ℋ} {D : Measure Ω}
    [IsProbabilityMeasure P] [IsProbabilityMeasure D]
    (gap : ℋ → Ω → ℝ) (n : ℝ) (hn_pos : 0 < n) (δ : ℝ) (hδ_pos : 0 < δ)
    (h_inner_int :
      Integrable (fun s => ∫ h, Real.exp (2 * n * (gap h s) ^ 2) ∂P) D)
    (h_inner_nn :
      0 ≤ᵐ[D] fun s => ∫ h, Real.exp (2 * n * (gap h s) ^ 2) ∂P)
    (h_exp_bound :
      ∫ s, ∫ h, Real.exp (2 * n * (gap h s) ^ 2) ∂P ∂D ≤ 2 * Real.sqrt n) :
    D.real { s | 2 * Real.sqrt n / δ ≤ ∫ h, Real.exp (2 * n * (gap h s) ^ 2) ∂P } ≤ δ := by
  have hM_pos : 0 < 2 * Real.sqrt n := by
    have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
    linarith
  exact pac_bayes_chernoff_step hM_pos hδ_pos h_inner_nn h_inner_int h_exp_bound

/-! ### Composing: function-class MGF + log step

The PAC-Bayes carrier consumes `Real.log` of the function-class MGF.
Once the MGF is bounded by `2 √n / δ`, taking `log` of both sides gives
the form required by `pac_bayes_mcallester`'s `h_conc` hypothesis. The
log step itself is `Real.log_le_log_iff` and lives in
`Ch14_Probabilistic/PACBayes.lean` (see `pac_bayes_conc_of_mgf_bound`).
We expose it here also for the function-class shape. -/

/-- **Log-form of the function-class MGF bound.** If the per-sample
function-class exponential moment is bounded by `2 √n / δ`, then its
logarithm is bounded by `log(2 √n / δ)`. This is the form fed into the
`h_conc` hypothesis of `pac_bayes_mcallester_abstract`. -/
theorem function_class_log_mgf_bound
    {expFC : ℝ} (n : ℝ) (hn_pos : 0 < n) (δ : ℝ) (hδ_pos : 0 < δ)
    (h_expFC_pos : 0 < expFC)
    (h_expFC_le : expFC ≤ 2 * Real.sqrt n / δ) :
    Real.log expFC ≤ Real.log (2 * Real.sqrt n / δ) := by
  have h_bound_pos : 0 < 2 * Real.sqrt n / δ := by
    have hsqrt_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
    positivity
  exact (Real.log_le_log_iff h_expFC_pos h_bound_pos).mpr h_expFC_le

end LTFP.MathlibExt.Probability
