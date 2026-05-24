/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Kullback--Leibler divergence (LTFP re-exports + Donsker--Varadhan inequality)

Proposed Mathlib path: `Mathlib/InformationTheory/KullbackLeibler/DonskerVaradhan.lean`.
Proposed Mathlib namespace: `InformationTheory`.

Mathlib already provides the `klDiv μ ν : ℝ≥0∞` definition (in
`Mathlib.InformationTheory.KullbackLeibler.Basic`) together with Gibbs'
inequality (`integral_llr_add_sub_measure_univ_nonneg`), the converse
Gibbs identity (`klDiv_eq_zero_iff`), and the `llr` / `Measure.tilted`
machinery. What is **not** yet present upstream is the **Donsker--Varadhan
variational inequality**

  `∫ f ∂μ  ≤  (klDiv μ ν).toReal  +  log (∫ exp ∘ f ∂ν)`,

the measure-theoretic backbone of PAC-Bayes generalization bounds.

This file:

1. Re-exports the Mathlib API surface for `klDiv` so that downstream LTFP
   modules can import a single `LTFP.MathlibExt.Probability.KullbackLeibler`
   module instead of chasing the Mathlib path.
2. Proves the Donsker--Varadhan inequality
   (`donsker_varadhan_inequality`) for probability measures via the
   tilted-measure argument: applying the chain rule for `llr` on the
   tilted measure `ν.tilted f` (Mathlib's `integral_llr_tilted_right`) and
   Gibbs' nonnegativity for `klDiv μ (ν.tilted f)` recovers the textbook
   bound.

## Why this lives in `MathlibExt`

The Donsker--Varadhan inequality is a natural extension of Mathlib's
existing `KullbackLeibler` module and would be the obvious next file in
that directory. We keep it in `LTFP.MathlibExt.Probability` until it
lands upstream; the proof translates verbatim (only the namespace
changes).

## Main statements

* `klDiv_self_zero`           : `klDiv μ μ = 0` (re-export of `klDiv_self`
  under the LTFP namespace, taking `IsProbabilityMeasure μ`).
* `klDiv_nonneg_toReal`       : `0 ≤ (klDiv μ ν).toReal` (trivial, since
  `ℝ≥0∞.toReal ≥ 0`; this is the LTFP-named handle for Gibbs).
* `donsker_varadhan_inequality`
    : the measure-theoretic Donsker--Varadhan upper bound on `∫ f ∂μ`.

## References

* M. D. Donsker and S. R. S. Varadhan, *Asymptotic evaluation of certain
  Markov process expectations for large time. I*, Comm. Pure Appl. Math.,
  vol. 28, pp. 1--47, 1975.
* P. Dupuis and R. S. Ellis, *A Weak Convergence Approach to the Theory of
  Large Deviations*, Wiley, 1997, Proposition 1.4.2 (the Donsker--Varadhan
  variational representation).
* S. Boucheron, G. Lugosi, and P. Massart, *Concentration Inequalities*,
  Oxford University Press, 2013, Section 4.10.

## Tags

Kullback-Leibler divergence, Donsker-Varadhan, variational formula,
PAC-Bayes
-/

namespace LTFP.MathlibExt.Probability

-- When upstreamed, replace `LTFP.MathlibExt.Probability` by
-- `InformationTheory` throughout this file.

open MeasureTheory InformationTheory Real
open scoped ENNReal

variable {α : Type*} {mα : MeasurableSpace α} {μ ν : Measure α}

/-! ### Re-exports of Mathlib's `klDiv` API

These wrappers expose the Mathlib API under the LTFP `MathlibExt`
namespace. They are pure re-exports (no proof content beyond `exact`):
their purpose is to give downstream LTFP modules a stable import surface
so that the eventual Mathlib upstreaming can proceed by a single
`open InformationTheory` swap. -/

/-- **KL-divergence self-zero (LTFP re-export).** For every
sigma-finite measure `μ`, the Kullback--Leibler divergence `klDiv μ μ`
equals zero. This is Mathlib's `klDiv_self` repackaged under the LTFP
namespace. -/
theorem klDiv_self_zero (μ : Measure α) [SigmaFinite μ] :
    klDiv μ μ = 0 :=
  klDiv_self μ

/-- **KL-divergence non-negativity (LTFP re-export).** The real part of
the Kullback--Leibler divergence is non-negative. This is a trivial
consequence of `klDiv` taking values in `ℝ≥0∞`, but is exposed as a named
theorem so that downstream proofs can refer to "Gibbs' inequality" by
name. -/
theorem klDiv_nonneg_toReal (μ ν : Measure α) :
    0 ≤ (klDiv μ ν).toReal :=
  ENNReal.toReal_nonneg

/-- **Converse Gibbs (LTFP re-export).** For finite measures, the
Kullback--Leibler divergence vanishes iff the two measures coincide.
Repackaging of `InformationTheory.klDiv_eq_zero_iff`. -/
theorem klDiv_eq_zero_iff_eq
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv μ ν = 0 ↔ μ = ν :=
  klDiv_eq_zero_iff

/-! ### The Donsker--Varadhan variational inequality

Given probability measures `μ ≪ ν` and a test function `f` with `f`
integrable under `μ` and `exp ∘ f` integrable under `ν`, the
**Donsker--Varadhan inequality** reads

  `∫ f ∂μ  ≤  (klDiv μ ν).toReal  +  log (∫ exp ∘ f ∂ν)`.

The proof follows the textbook tilted-measure argument. Define
`ν' := ν.tilted f`. Then:

* `ν'` is a probability measure (`isProbabilityMeasure_tilted`),
* `ν ≪ ν'`, hence `μ ≪ ν'`,
* the chain rule for `llr` gives
  `∫ llr μ ν' dμ = ∫ llr μ ν dμ - ∫ f dμ + log ∫ exp f dν`
  (`integral_llr_tilted_right`),
* Gibbs' inequality yields `0 ≤ ∫ llr μ ν' dμ` (the LHS equals
  `(klDiv μ ν').toReal ≥ 0`),
* rearranging gives `∫ f dμ ≤ ∫ llr μ ν dμ + log ∫ exp f dν`, and
* for probability measures, `(klDiv μ ν).toReal = ∫ llr μ ν dμ` via
  `toReal_klDiv_of_measure_eq`.

-/

/-- **Donsker--Varadhan variational inequality.** For probability
measures `μ ≪ ν` on a measurable space `α`, a real-valued test function
`f` integrable under `μ` with `Real.exp ∘ f` integrable under `ν`, and
log-likelihood-ratio integrable under `μ`, the Donsker--Varadhan
inequality holds:

  `∫ f ∂μ  ≤  (klDiv μ ν).toReal  +  Real.log (∫ exp ∘ f ∂ν)`.

This is the measure-theoretic backbone of PAC-Bayes generalization
bounds: combined with Markov's inequality applied to `exp f` under `ν`,
it produces high-probability bounds on `∫ f ∂μ` in terms of
`klDiv μ ν`. -/
theorem donsker_varadhan_inequality
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : α → ℝ}
    (hμν : μ ≪ ν) (hf : Integrable f μ)
    (hfν : Integrable (fun x => Real.exp (f x)) ν)
    (h_int : Integrable (llr μ ν) μ) :
    ∫ x, f x ∂μ ≤ (klDiv μ ν).toReal + Real.log (∫ x, Real.exp (f x) ∂ν) := by
  -- Auxiliary: the tilted measure `ν.tilted f` is a probability measure.
  have hν' : IsProbabilityMeasure (ν.tilted f) :=
    isProbabilityMeasure_tilted hfν
  -- Absolute continuity chain: `μ ≪ ν ≪ ν.tilted f`.
  have hν_ac : ν ≪ ν.tilted f := absolutelyContinuous_tilted hfν
  have hμν' : μ ≪ ν.tilted f := hμν.trans hν_ac
  -- Integrability of `llr μ (ν.tilted f)` under `μ`.
  have h_int' : Integrable (llr μ (ν.tilted f)) μ :=
    integrable_llr_tilted_right hμν hf h_int hfν
  -- Chain-rule identity for `llr` on the tilted measure.
  have h_chain :
      ∫ x, llr μ (ν.tilted f) x ∂μ
        = ∫ x, llr μ ν x ∂μ - ∫ x, f x ∂μ + Real.log (∫ x, Real.exp (f x) ∂ν) :=
    integral_llr_tilted_right hμν hf hfν h_int
  -- Gibbs' inequality for `μ ≪ ν.tilted f`: the integrand of `klDiv` is non-negative.
  have h_gibbs : 0 ≤ ∫ x, llr μ (ν.tilted f) x ∂μ := by
    have h_meas_eq : μ Set.univ = (ν.tilted f) Set.univ := by
      rw [show μ Set.univ = (1 : ℝ≥0∞) from measure_univ,
          show (ν.tilted f) Set.univ = (1 : ℝ≥0∞) from measure_univ]
    have h_eq : (klDiv μ (ν.tilted f)).toReal = ∫ x, llr μ (ν.tilted f) x ∂μ :=
      toReal_klDiv_of_measure_eq hμν' h_meas_eq
    rw [← h_eq]
    exact ENNReal.toReal_nonneg
  -- For probability measures, `(klDiv μ ν).toReal = ∫ llr μ ν dμ`.
  have h_klDiv_eq : (klDiv μ ν).toReal = ∫ x, llr μ ν x ∂μ := by
    have h_meas_eq : μ Set.univ = ν Set.univ := by
      rw [show μ Set.univ = (1 : ℝ≥0∞) from measure_univ,
          show ν Set.univ = (1 : ℝ≥0∞) from measure_univ]
    exact toReal_klDiv_of_measure_eq hμν h_meas_eq
  -- Combine.
  have h_combined :
      0 ≤ ∫ x, llr μ ν x ∂μ - ∫ x, f x ∂μ + Real.log (∫ x, Real.exp (f x) ∂ν) := by
    rw [← h_chain]; exact h_gibbs
  linarith [h_klDiv_eq, h_combined]

/-- **Donsker--Varadhan inequality, rearranged form.** Symmetric
restatement of `donsker_varadhan_inequality` in the form most commonly
used downstream:

  `∫ f ∂μ  -  log (∫ exp ∘ f ∂ν)  ≤  (klDiv μ ν).toReal`,

i.e., the test-function expectation minus the log-moment-generating
value is bounded by KL. This is the form fed into PAC-Bayes proofs as
the measure-theoretic counterpart to `donsker_varadhan_scalar` in
`DonskerVaradhan.lean`. -/
theorem donsker_varadhan_inequality_diff
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f : α → ℝ}
    (hμν : μ ≪ ν) (hf : Integrable f μ)
    (hfν : Integrable (fun x => Real.exp (f x)) ν)
    (h_int : Integrable (llr μ ν) μ) :
    ∫ x, f x ∂μ - Real.log (∫ x, Real.exp (f x) ∂ν) ≤ (klDiv μ ν).toReal := by
  have h := donsker_varadhan_inequality hμν hf hfν h_int
  linarith

/-! ### Tilted-attainment identity (Donsker--Varadhan, sub-step 1)

The Donsker--Varadhan upper bound proved above is sharp on the
exponential-family slice: choosing `μ = ν.tilted f` (the exponential
tilt of `ν` by `f`) saturates the bound. Concretely, for an
exponentially tilted probability measure `ν.tilted f` we have

  `(klDiv (ν.tilted f) ν).toReal
     = ∫ x, f x ∂(ν.tilted f) - log (∫ x, exp (f x) ∂ν)`.

This is the *tilted-attainment identity*: it exhibits an explicit
attainment witness for the variational supremum on the
exponential-family slice, without yet formalizing the supremum over
bounded measurable functions (that is the next sub-step of the
Donsker--Varadhan milestone).

The proof uses Mathlib's `log_rnDeriv_tilted_left_self`
(`llr (ν.tilted f) ν =ᵐ[ν] f - log Z`) together with
`tilted_absolutelyContinuous` (to transfer the a.e. equality from `ν`
to `ν.tilted f`) and `toReal_klDiv_of_measure_eq` (to convert the
`klDiv` into an integral of `llr`). The argument is short: every
piece is already in Mathlib at the pinned commit. -/

/-- **Tilted-attainment identity for the Donsker--Varadhan
inequality.** For a probability measure `ν` and a test function `f`
with `Real.exp ∘ f` integrable under `ν`, the Kullback--Leibler
divergence of the exponential tilt `ν.tilted f` against `ν` equals the
Donsker--Varadhan functional evaluated at `f`:

  `(klDiv (ν.tilted f) ν).toReal
     = ∫ x, f x ∂(ν.tilted f) - Real.log (∫ x, Real.exp (f x) ∂ν)`.

In particular, the choice `μ = ν.tilted f` saturates
`donsker_varadhan_inequality_diff`. This is sub-step 1 of the
Donsker--Varadhan attainment milestone: it provides an explicit
attainment witness on the exponential-family slice without invoking
the supremum over the full class of bounded measurable functions. -/
theorem klDiv_tilted_eq_dvFunctional
    (ν : Measure α) [IsProbabilityMeasure ν]
    {f : α → ℝ}
    (hf_exp : Integrable (fun x => Real.exp (f x)) ν)
    (hf_int_tilted : Integrable f (ν.tilted f)) :
    (klDiv (ν.tilted f) ν).toReal
      = ∫ x, f x ∂(ν.tilted f) - Real.log (∫ x, Real.exp (f x) ∂ν) := by
  -- The tilted measure is a probability measure.
  have hν' : IsProbabilityMeasure (ν.tilted f) := isProbabilityMeasure_tilted hf_exp
  -- Absolute continuity: `ν.tilted f ≪ ν`.
  have hac : ν.tilted f ≪ ν := tilted_absolutelyContinuous ν f
  -- Convert `(klDiv (ν.tilted f) ν).toReal` to an integral of `llr` against
  -- the tilted measure (both measures are probability measures, so
  -- their universes agree and no separate integrability is needed).
  have h_meas_eq : (ν.tilted f) Set.univ = ν Set.univ := by
    rw [show (ν.tilted f) Set.univ = (1 : ℝ≥0∞) from measure_univ,
        show ν Set.univ = (1 : ℝ≥0∞) from measure_univ]
  have h_klDiv :
      (klDiv (ν.tilted f) ν).toReal
        = ∫ x, llr (ν.tilted f) ν x ∂(ν.tilted f) :=
    toReal_klDiv_of_measure_eq hac h_meas_eq
  -- Pointwise identification of `llr (ν.tilted f) ν` via Mathlib's
  -- `log_rnDeriv_tilted_left_self`. This is a.e. ν; lift to a.e.
  -- `ν.tilted f` via absolute continuity.
  set Z : ℝ := ∫ x, Real.exp (f x) ∂ν with hZ
  have h_ae_ν : llr (ν.tilted f) ν =ᵐ[ν] fun x => f x - Real.log Z := by
    -- Unfold `llr` to match Mathlib's statement.
    have := log_rnDeriv_tilted_left_self (μ := ν) (f := f) hf_exp
    -- `this : (fun x => log ((ν.tilted f).rnDeriv ν x).toReal)
    --          =ᵐ[ν] fun x => f x - log (∫ x, exp (f x) ∂ν)`
    -- which is exactly `llr (ν.tilted f) ν =ᵐ[ν] fun x => f x - log Z`
    -- after unfolding `llr`.
    simpa [llr, hZ] using this
  have h_ae_tilted : llr (ν.tilted f) ν =ᵐ[ν.tilted f] fun x => f x - Real.log Z :=
    hac.ae_le h_ae_ν
  -- Compute the integral of the simple expression `f x - log Z` against
  -- the tilted probability measure.
  have h_int_eq :
      ∫ x, llr (ν.tilted f) ν x ∂(ν.tilted f)
        = ∫ x, (f x - Real.log Z) ∂(ν.tilted f) :=
    integral_congr_ae h_ae_tilted
  have h_split :
      ∫ x, (f x - Real.log Z) ∂(ν.tilted f)
        = ∫ x, f x ∂(ν.tilted f) - Real.log Z := by
    rw [integral_sub hf_int_tilted (integrable_const _)]
    simp
  rw [h_klDiv, h_int_eq, h_split, hZ]

end LTFP.MathlibExt.Probability
