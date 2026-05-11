/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Donsker--Varadhan variational formula (algebraic core)

Proposed Mathlib path: `Mathlib/Probability/DonskerVaradhan.lean` or
`Mathlib/InformationTheory/DonskerVaradhan.lean`.
Proposed Mathlib namespace: `ProbabilityTheory` (this file currently lives in
`LTFP.MathlibExt.Probability` until upstreamed; see the leading `namespace`
block).

For any probability measure `ν` and any `μ ≪ ν` on a measurable space, the
**Donsker--Varadhan variational formula** states that

`KL(μ ‖ ν) = sup_{f bounded measurable} { E_μ[f] - log E_ν[exp f] }`,

and the supremum is attained at `f = log (dμ/dν)` (up to an additive
constant). This identity is the algebraic backbone of PAC-Bayes
generalization bounds: combined with Markov's inequality applied to `exp f`
under `ν`, it produces high-probability bounds on `E_μ[f]` in terms of
`KL(μ ‖ ν)`. It also underpins Cramér-type tail bounds in the theory of
large deviations.

## Status

**Partial — full Donsker--Varadhan variational characterization pending.**
This module isolates the **real-variable algebraic content** of the
Donsker--Varadhan formula: the inequalities and identities relating the
pair `(E_μ[f], log E_ν[exp f])` to a candidate divergence value `KL`, the
Jensen anchor `1 + x ≤ exp x` that underlies the inequality, and the
attainment identities at `f = log (dμ/dν)`. The full
measure-theoretic identity

`klDiv μ ν = ⨆ f, ∫ f ∂μ - log (∫ exp ∘ f ∂ν)`,

where the supremum ranges over bounded measurable real-valued functions, is
**not** proved here. Closing this gap upstream requires:

1. a Mathlib API exposing the Radon--Nikodym density of `μ` w.r.t. `ν` in a
   form compatible with `MeasureTheory.Measure.rnDeriv` and the existing
   `Mathlib.InformationTheory.KullbackLeibler.Basic.klDiv`;
2. a packaged Fenchel-style duality lemma matching `x · log x - x + 1 ≥ 0`
   to the convex conjugate `exp y - 1`;
3. the standard monotone-convergence / truncation argument that lifts the
   pointwise inequality from log-density test functions to the full
   bounded measurable supremum.

The algebraic primitives in this file are intended to be reused verbatim
once these prerequisites are in place.

## Main definitions

* `ProbabilityTheory.dvFunctional Ef logEexp` — the scalar Donsker--Varadhan
  functional `Ef - logEexp` as a function of the expectation
  `Ef = E_μ[f]` and the log-moment-generating value
  `logEexp = log E_ν[exp f]`.

## Main results (algebraic core)

* `ProbabilityTheory.dvFunctional_log_exp` — collapse identity:
  `dvFunctional a (log (exp b)) = a - b`.
* `ProbabilityTheory.dvFunctional_self_eq_zero` — the functional vanishes
  on the diagonal: `dvFunctional x (log (exp x)) = 0`.
* `ProbabilityTheory.dvFunctional_mono_Ef` — monotonicity in the first
  argument (the test-function expectation under `μ`).
* `ProbabilityTheory.dvFunctional_antitone_logEexp` — antitonicity in the
  second argument (the log-moment-generating value under `ν`).
* `ProbabilityTheory.dvFunctional_jensen_anchor` — the underlying Jensen
  anchor `1 + x ≤ exp x`.
* `ProbabilityTheory.dvFunctional_jensen_log_concavity_anchor` — Jensen for
  `log ∘ exp`: `dvFunctional x (log (exp x)) ≤ 0` (the log-concavity side
  of the DV inequality, equivalent to `x ≤ log (exp x)`).
* `ProbabilityTheory.dvFunctional_le_kl_iff` — the DV inequality in
  scalar form: `dvFunctional Ef logEexp ≤ KL ↔ Ef ≤ KL + logEexp`.
* `ProbabilityTheory.dvFunctional_le_kl_of_test_bounded` — bounded-test
  corollary: if `Ef ≤ logEexp + K` then `dvFunctional Ef logEexp ≤ K`.
* `ProbabilityTheory.dvFunctional_attained_at_log_density` — attainment at
  the log-density: `dvFunctional a (log (exp a * 1)) = 0`.
* `ProbabilityTheory.dvFunctional_attained_at_log_density_form2` — second
  algebraic form of the optimum: `dvFunctional (log r) (log r) = 0` for
  any positive `r`.

## References

* M. D. Donsker and S. R. S. Varadhan, *Asymptotic evaluation of certain
  Markov process expectations for large time. I*, Comm. Pure Appl. Math.,
  vol. 28, pp. 1–47, 1975.
* M. D. Donsker and S. R. S. Varadhan, *Asymptotic evaluation of certain
  Markov process expectations for large time. II*, Comm. Pure Appl. Math.,
  vol. 28, pp. 279–301, 1975.
* M. D. Donsker and S. R. S. Varadhan, *Asymptotic evaluation of certain
  Markov process expectations for large time. III*, Comm. Pure Appl. Math.,
  vol. 29, pp. 389–461, 1976.
* S. Boucheron, G. Lugosi, and P. Massart, *Concentration Inequalities: A
  Nonasymptotic Theory of Independence*, Oxford University Press, 2013,
  Section 4.10 (variational formulation of KL and Cramér's transform).
* A. Dembo and O. Zeitouni, *Large Deviations Techniques and Applications*,
  Springer, 2nd ed., 1998, Section 6.2 (Donsker--Varadhan variational
  formula and contraction principle).
* O. Catoni, *PAC-Bayesian Supervised Classification*, IMS Lecture Notes
  Monograph Series, vol. 56, 2007, Section 1.2.

## Tags

Donsker-Varadhan, KL divergence, variational formula, large deviations,
PAC-Bayes
-/

namespace LTFP.MathlibExt.Probability

-- When upstreamed, replace `LTFP.MathlibExt.Probability` by
-- `ProbabilityTheory` throughout this file. All declarations are intended
-- to live in the `ProbabilityTheory` namespace.

open Real

/-- The scalar **Donsker--Varadhan functional**, as a function of the
expectation `Ef = E_μ[f]` and the log-moment-generating value
`logEexp = log E_ν[exp f]`:

`dvFunctional Ef logEexp = Ef - logEexp`.

This is the quantity whose supremum over bounded measurable test functions
`f` equals the Kullback--Leibler divergence `KL(μ ‖ ν)` in the full
Donsker--Varadhan formula. It is isolated as a real-valued function so
that its algebraic content can be reasoned about without commitments to a
particular measure-theoretic setup. -/
def dvFunctional (Ef logEexp : ℝ) : ℝ := Ef - logEexp

/-- Collapse identity: substituting `logEexp = log (exp b)` into the
Donsker--Varadhan functional reduces it to the linear difference `a - b`.
This is the trivial sanity check that the log/exp pair on the second
argument is inert when the test function is constant. -/
theorem dvFunctional_log_exp (a b : ℝ) :
    dvFunctional a (Real.log (Real.exp b)) = a - b := by
  unfold dvFunctional
  rw [Real.log_exp]

/-- The Donsker--Varadhan functional vanishes on the log-density
diagonal: when `Ef = x` and `logEexp = log (exp x)`, the functional value
is exactly `0`. This is the algebraic form of the optimality condition
`sup = KL` attained at `f = log (dμ/dν)`, in the constant-test-function
limit `f ≡ x`. -/
theorem dvFunctional_self_eq_zero (x : ℝ) :
    dvFunctional x (Real.log (Real.exp x)) = 0 := by
  rw [dvFunctional_log_exp]; ring

/-- Monotonicity in the first argument: for any fixed `logEexp`, the map
`Ef ↦ dvFunctional Ef logEexp` is monotone. Increasing the expectation
of the test function under `μ` only increases the DV functional value. -/
theorem dvFunctional_mono_Ef (logEexp : ℝ) :
    Monotone (fun Ef : ℝ => dvFunctional Ef logEexp) := by
  intro Ef₁ Ef₂ h
  unfold dvFunctional
  linarith

/-- Antitonicity in the second argument: for any fixed `Ef`, the map
`logEexp ↦ dvFunctional Ef logEexp` is antitone. Increasing the
log-moment-generating function under `ν` decreases the DV functional
value. -/
theorem dvFunctional_antitone_logEexp (Ef : ℝ) :
    Antitone (fun logEexp : ℝ => dvFunctional Ef logEexp) := by
  intro logEexp₁ logEexp₂ h
  unfold dvFunctional
  linarith

/-- The Jensen-style anchor underlying the Donsker--Varadhan formula:
`1 + x ≤ exp x` for every real `x`. Applying this pointwise with
`x = f - log E_ν[exp f]` and integrating under `ν` yields the DV
inequality `E_μ[f] - log E_ν[exp f] ≤ KL(μ ‖ ν)` once the relevant
measure-theoretic API is in place. -/
theorem dvFunctional_jensen_anchor (x : ℝ) : 1 + x ≤ Real.exp x := by
  have h : x + 1 ≤ Real.exp x := Real.add_one_le_exp x
  linarith

/-- Jensen log-concavity anchor for the Donsker--Varadhan inequality: for
every real `x`, the functional `dvFunctional x (log (exp x))` is
nonpositive (in fact zero). This is the scalar shadow of Jensen's
inequality `log E_ν[exp f] ≥ E_ν[f]` evaluated at the constant test
function `f ≡ x` — the side of the DV inequality establishing that
log-moment-generating values dominate expectations. -/
theorem dvFunctional_jensen_log_concavity_anchor (x : ℝ) :
    dvFunctional x (Real.log (Real.exp x)) ≤ 0 := by
  rw [dvFunctional_self_eq_zero]

/-- Scalar form of the DV inequality as an `iff`: the DV functional
value is bounded above by `KL` exactly when the test-function expectation
is bounded by `KL + logEexp`. This is the form in which the DV
inequality is most commonly applied in PAC-Bayes arguments, where `Ef`
is the quantity to be bounded and `KL + logEexp` is the resulting tail
bound. -/
theorem dvFunctional_le_kl_iff (Ef logEexp KL : ℝ) :
    dvFunctional Ef logEexp ≤ KL ↔ Ef ≤ KL + logEexp := by
  unfold dvFunctional
  constructor
  · intro h; linarith
  · intro h; linarith

/-- Bounded-test corollary of the Donsker--Varadhan inequality: if the
test-function expectation `Ef` is dominated by `logEexp + K`, then the DV
functional value is bounded by `K`. This is the form that combines
directly with Markov's inequality on `exp f` under `ν` to produce
PAC-Bayes-style tail bounds. -/
theorem dvFunctional_le_kl_of_test_bounded {Ef logEexp K : ℝ}
    (h : Ef ≤ logEexp + K) : dvFunctional Ef logEexp ≤ K := by
  unfold dvFunctional; linarith

/-- The Donsker--Varadhan functional is attained at the log-density test
function: when `f = log (dμ/dν)`, the moment-generating value
`E_ν[exp f]` equals `E_ν[dμ/dν] = 1` (since `μ ≪ ν`), so
`log E_ν[exp f] = log (exp a * 1) = a`, giving the optimality identity
`dvFunctional a (log (exp a * 1)) = 0`. This module captures the
final algebraic identity. -/
theorem dvFunctional_attained_at_log_density (a : ℝ) :
    dvFunctional a (Real.log (Real.exp a * 1)) = 0 := by
  unfold dvFunctional
  rw [mul_one, Real.log_exp]; ring

/-- Second algebraic form of the Donsker--Varadhan optimum: for any
strictly positive `r` (representing a density ratio value `dμ/dν` at a
point), the DV functional vanishes at the pair `(log r, log r)`. This is
the pointwise version of the optimality identity, obtained by tracking
`log E_ν[exp f]` at the constant test function `f ≡ log r` (where the
moment-generating value `E_ν[exp f] = r` matches the test-function
expectation under the Dirac measure at the density's argument). -/
theorem dvFunctional_attained_at_log_density_form2 {r : ℝ} (_hr : 0 < r) :
    dvFunctional (Real.log r) (Real.log r) = 0 := by
  unfold dvFunctional; ring

/-! ### Examples

The two examples below pin down the boundary algebraic identities of the
Donsker--Varadhan functional: the `exp 0 = 1` case (the trivial test
function `f ≡ 0`), and the diagonal case (the log-density attainment). -/

section Examples

/-- At the trivial test function `f ≡ 0`, the DV functional vanishes:
`Ef = 0`, `logEexp = log (E_ν[exp 0]) = log 1 = 0`. -/
example : dvFunctional 0 (Real.log (Real.exp 0)) = 0 := by
  rw [Real.exp_zero, Real.log_one]; unfold dvFunctional; ring

/-- At the log-density test function `f = log (dμ/dν)` (algebraic
shadow): if `Ef = a` and `logEexp = a`, the functional vanishes and the
DV supremum is attained. -/
example (a : ℝ) : dvFunctional a a = 0 := by
  unfold dvFunctional; ring

end Examples

end LTFP.MathlibExt.Probability
