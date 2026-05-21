/-
LTFP §14.4 — PAC-Bayesian analysis.

Bach (2024) §14.4, pp. 423-426. PAC-Bayes bounds compare a *posterior*
distribution `Q` over the hypothesis class with a fixed *prior* `P`.
Under bounded losses, with probability `1 − δ`,
`E_{f ∼ Q}[R(f)] ≤ E_{f ∼ Q}[R̂_n(f)] + √((KL(Q ‖ P) + log(1/δ)) / (2n))`.

The full bound requires probability machinery; we land here just the
KL divergence wrapper from `LTFP.Foundations.InfoTheory` and a
sanity lemma that `KL(P ‖ P) = 0`.
-/
import LTFP.Foundations.InfoTheory
import LTFP.MathlibExt.Probability.BoundedMeanSqExp
import LTFP.MathlibExt.Probability.DonskerVaradhan
import LTFP.MathlibExt.Probability.FunctionClassConcentration
import LTFP.MathlibExt.Probability.KullbackLeibler
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Constructions.Pi

namespace LTFP

open MeasureTheory InformationTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

/-- §14.4 — KL divergence wrapper specialized to the LTFP namespace
    for use in PAC-Bayes bounds. Re-exports `LTFP.kl`. -/
noncomputable def pacBayesKL (Q P : Measure α) : ENNReal := kl Q P

/-- §14.4 sanity lemma: PAC-Bayes KL of a measure against itself is zero. -/
theorem pacBayesKL_self (P : Measure α) [SigmaFinite P] :
    pacBayesKL P P = 0 :=
  kl_self P

/-- §14.4 — PAC-Bayes KL is `∞` when posterior is not absolutely
    continuous w.r.t. prior — penalizing posteriors that put mass
    where the prior assigns zero probability. -/
theorem pacBayesKL_of_not_ac (Q P : Measure α) (h : ¬ Q ≪ P) :
    pacBayesKL Q P = ∞ :=
  kl_of_not_ac Q P h

/-- §14.4 — PAC-Bayes KL with zero-probability prior is `∞`. -/
theorem pacBayesKL_zero_prior (Q : Measure α) [NeZero Q] :
    pacBayesKL Q 0 = ∞ :=
  kl_zero_right Q

/-- §14.4 — PAC-Bayes KL is non-top iff Q absolutely continuous w.r.t.
    P and integrable. -/
theorem pacBayesKL_ne_top_iff (Q P : Measure α) :
    pacBayesKL Q P ≠ ∞ ↔ Q ≪ P ∧ Integrable (llr Q P) Q :=
  kl_ne_top_iff Q P

/-- §14.4 — PAC-Bayes KL = top iff non-AC or non-integrable. -/
theorem pacBayesKL_eq_top_iff (Q P : Measure α) :
    pacBayesKL Q P = ∞ ↔ (Q ≪ P → ¬ Integrable (llr Q P) Q) :=
  kl_eq_top_iff Q P

/-- §14.4 — PAC-Bayes KL definition unfolded. -/
theorem pacBayesKL_def (Q P : Measure α) :
    pacBayesKL Q P = kl Q P := rfl

/-! ### McAllester PAC-Bayes bound — algebraic core (Bach 2024 §14.4)

The McAllester bound states that with probability `≥ 1 − δ` over the sample,
for all posteriors `Q ≪ P`,
`E_{f∼Q}[R(f)] ≤ E_{f∼Q}[R̂_n(f)] + √((KL(Q‖P) + log(1/δ) + log(2n)) / (2(n-1)))`.

The high-probability statement requires the Donsker–Varadhan variational
formula combined with a concentration argument over the function class —
both of which are only partially available in Mathlib (no `tvDist`-style
infrastructure yet, and the DV formula is only stated for finite cases).

What we land here is the **algebraic core** of the bound: the deviation
expression `√((kl + r) / (2 m))` (with `kl, r ≥ 0` and `m > 0` standing in
for `KL`, `log(1/δ)`, and `n − 1` respectively) is

  * non-negative,
  * monotone non-decreasing in `kl`,
  * non-increasing in `m` (i.e. as `n` grows),

together with the textbook subadditivity `√(x + y) ≤ √x + √y` for
`x, y ≥ 0` that drives McAllester's proof of the bound.
-/

/-- §14.4 — McAllester deviation: `√((kl + r) / (2 m))`. The arguments
    stand in for `KL(Q‖P)`, `log(1/δ) + log(2n)`, and `n − 1` (or any
    positive scaling that arises in the proof). All real-valued so we
    can prove monotonicity directly. -/
noncomputable def mcallesterBound (kl r m : ℝ) : ℝ :=
  Real.sqrt ((kl + r) / (2 * m))

/-- §14.4 — Subadditivity of `√`: `√(x + y) ≤ √x + √y` for `x, y ≥ 0`.
    This is the algebraic identity that lets the McAllester proof split
    `KL + log(1/δ)` contributions into separate `√` terms. -/
theorem sqrt_add_le_sqrt_add_sqrt (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have hx' : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  have hy' : 0 ≤ Real.sqrt y := Real.sqrt_nonneg _
  have hsum : 0 ≤ Real.sqrt x + Real.sqrt y := add_nonneg hx' hy'
  have hxy : 0 ≤ x + y := add_nonneg hx hy
  -- Compare squares.
  rw [← Real.sqrt_sq hsum]
  apply Real.sqrt_le_sqrt
  have hxsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx
  have hysq : Real.sqrt y ^ 2 = y := Real.sq_sqrt hy
  have hcross : 0 ≤ Real.sqrt x * Real.sqrt y := mul_nonneg hx' hy'
  nlinarith [hxsq, hysq, hcross]

/-- §14.4 — McAllester deviation is non-negative for `kl, r ≥ 0`,
    `m > 0`. (Square-root of any real is `≥ 0` in Mathlib's `Real.sqrt`.) -/
theorem mcallester_bound_nonneg (kl r m : ℝ) :
    0 ≤ mcallesterBound kl r m :=
  Real.sqrt_nonneg _

/-- §14.4 — McAllester deviation is non-decreasing in `kl` (for fixed
    `r ≥ 0` and `m > 0`). Larger posterior–prior divergence cannot
    shrink the bound. -/
theorem mcallester_bound_mono_kl
    {kl₁ kl₂ r m : ℝ} (hm : 0 < m) (h : kl₁ ≤ kl₂) :
    mcallesterBound kl₁ r m ≤ mcallesterBound kl₂ r m := by
  unfold mcallesterBound
  apply Real.sqrt_le_sqrt
  have h2m : 0 < 2 * m := by linarith
  exact (div_le_div_iff_of_pos_right h2m).mpr (by linarith)

/-- §14.4 — McAllester deviation is non-increasing in `m`
    (the sample-size proxy `n − 1`) for fixed `kl, r ≥ 0` and
    `m₁, m₂ > 0` with `m₁ ≤ m₂`: more samples cannot make the bound
    larger. -/
theorem mcallester_bound_antitone_n
    {kl r m₁ m₂ : ℝ} (hkl : 0 ≤ kl) (hr : 0 ≤ r)
    (hm₁ : 0 < m₁) (h : m₁ ≤ m₂) :
    mcallesterBound kl r m₂ ≤ mcallesterBound kl r m₁ := by
  unfold mcallesterBound
  apply Real.sqrt_le_sqrt
  have hm₂ : 0 < m₂ := lt_of_lt_of_le hm₁ h
  have h2m₁ : 0 < 2 * m₁ := by linarith
  have h2m₂ : 0 < 2 * m₂ := by linarith
  have h2 : 2 * m₁ ≤ 2 * m₂ := by linarith
  have hnum : 0 ≤ kl + r := add_nonneg hkl hr
  exact div_le_div_of_nonneg_left hnum h2m₁ h2

/-! ### Abstract McAllester PAC-Bayes bound

We now assemble the full McAllester bound

`E_{h∼Q}[R(h)] − E_{h∼Q}[R̂_n(h)] ≤ √((KL(Q ‖ P) + log(2√n / δ)) / (2n))`

at the scalar level, parametric in:

* the posterior–prior divergence value `D` (standing in for `KL(Q ‖ P)`);
* the test-function squared-gap expectation under `Q`, abbreviated
  `EQgapSq`, playing the role of `E_{h∼Q}[(R̂_n(h) − R(h))²]`;
* the log-moment-generating value `logMGFp`, playing the role of
  `log E_{h∼P}[exp(2n · (R̂_n(h) − R(h))²)]`;
* a Jensen hypothesis relating `(E_Q[gap])²` to `E_Q[gap²]`;
* a Donsker--Varadhan hypothesis (in scalar `dvFunctional_le_kl_of_test_bounded`
  form) bounding `2n · E_Q[gap²]` by `D + logMGFp`;
* a "concentration over function class" hypothesis bounding `logMGFp` by
  `log(2√n / δ)`.

This is the *abstract algebraic content* of the McAllester theorem. The
underlying measure-theoretic Donsker--Varadhan formula is only partially
available in Mathlib (see `LTFP.MathlibExt.Probability.DonskerVaradhan`),
so we accept these hypotheses as inputs. Once the full DV formula and a
function-class concentration lemma land upstream, both `h_DV` and
`h_conc` discharge automatically and the abstract bound below becomes
the textbook McAllester theorem.
-/

/-- §14.4 — **Abstract McAllester PAC-Bayes bound.**

Given a non-negative posterior-vs-empirical gap `EQgap` with the
Donsker--Varadhan and concentration-over-function-class hypotheses in
scalar form, the gap is bounded by the McAllester deviation

`√((D + log(2√n / δ)) / (2n))`,

where `D` plays the role of `KL(Q ‖ P)`. The proof composes Jensen
(scalar form) with the scalar DV inequality
`Ef ≤ logEexp + KL` (cf. `dvFunctional_le_kl_of_test_bounded`) and the
concentration hypothesis, then squares-and-roots through
`Real.sqrt_le_sqrt`. -/
theorem pac_bayes_mcallester_abstract
    {EQgap EQgapSq logMGFp D n δ : ℝ}
    (hn : 0 < n) (_hδ : 0 < δ)
    (_hD : 0 ≤ D)
    (hEQgap_nn : 0 ≤ EQgap)
    (h_jensen : EQgap ^ 2 ≤ EQgapSq)
    (h_DV : 2 * n * EQgapSq ≤ D + logMGFp)
    (h_conc : logMGFp ≤ Real.log (2 * Real.sqrt n / δ)) :
    EQgap ≤ mcallesterBound D (Real.log (2 * Real.sqrt n / δ)) n := by
  -- Set `r := log(2√n / δ)` for brevity.
  set r : ℝ := Real.log (2 * Real.sqrt n / δ) with hr_def
  -- Compose DV + concentration: 2n · EQgapSq ≤ D + r.
  have h_dv_conc : 2 * n * EQgapSq ≤ D + r := by linarith
  -- Apply Jensen (scalar): 2n · EQgap² ≤ 2n · EQgapSq.
  have h2n_pos : 0 < 2 * n := by linarith
  have h2n_nn : 0 ≤ 2 * n := le_of_lt h2n_pos
  have h_jensen_scaled : 2 * n * EQgap ^ 2 ≤ 2 * n * EQgapSq :=
    mul_le_mul_of_nonneg_left h_jensen h2n_nn
  -- Combine: 2n · EQgap² ≤ D + r.
  have h_combined : 2 * n * EQgap ^ 2 ≤ D + r :=
    le_trans h_jensen_scaled h_dv_conc
  -- Divide by 2n.
  have h_sq_le : EQgap ^ 2 ≤ (D + r) / (2 * n) := by
    rw [le_div_iff₀ h2n_pos]
    linarith
  -- Take square roots, using `EQgap = √(EQgap²)` for nonneg `EQgap`.
  have h_sqrt_sq : Real.sqrt (EQgap ^ 2) = EQgap := by
    rw [sq, Real.sqrt_mul_self hEQgap_nn]
  have h_final : Real.sqrt (EQgap ^ 2) ≤ Real.sqrt ((D + r) / (2 * n)) :=
    Real.sqrt_le_sqrt h_sq_le
  rw [h_sqrt_sq] at h_final
  exact h_final

/-- §14.4 — **Corollary**: the abstract McAllester bound rewritten in the
form `EQgap ≤ √((D + log(2√n / δ)) / (2 n))`, unfolded from the
`mcallesterBound` wrapper. This is the form most commonly quoted in
PAC-Bayes references (Bach 2024, Theorem 14.6; McAllester 1999). -/
theorem pac_bayes_mcallester_abstract_unfolded
    {EQgap EQgapSq logMGFp D n δ : ℝ}
    (hn : 0 < n) (hδ : 0 < δ)
    (hD : 0 ≤ D)
    (hEQgap_nn : 0 ≤ EQgap)
    (h_jensen : EQgap ^ 2 ≤ EQgapSq)
    (h_DV : 2 * n * EQgapSq ≤ D + logMGFp)
    (h_conc : logMGFp ≤ Real.log (2 * Real.sqrt n / δ)) :
    EQgap ≤ Real.sqrt ((D + Real.log (2 * Real.sqrt n / δ)) / (2 * n)) :=
  pac_bayes_mcallester_abstract (logMGFp := logMGFp)
    hn hδ hD hEQgap_nn h_jensen h_DV h_conc

/-! ### Discharging the McAllester hypotheses from scalar primitives

The two PAC-Bayes hypotheses `h_DV` and `h_conc` in
`pac_bayes_mcallester_abstract` are independent measure-theoretic
inputs in their natural forms (an integral over the function class
under the prior, and a scalar Donsker--Varadhan inequality on
`log E_P[exp(2n · gap²)]`).

The lemmas below discharge them at the **scalar level**, taking as input
the *real-valued* quantities that the upstream measure theory would
produce. This is the scalar shadow of the full PAC-Bayes proof: once the
measure-theoretic API (Donsker--Varadhan variational formula on `klDiv`,
Hoeffding applied per hypothesis followed by Fubini over the function
class) is in Mathlib, the hypotheses below discharge from those upstream
results and the entire McAllester bound becomes a clean corollary.

The two scalar primitives are:

* `dv_scalar_primitive`: `2 n · E_Q[gap²] - log E_P[exp(2 n · gap²)] ≤ D`
  — the scalar Donsker--Varadhan inequality applied to the test function
  `f(h) := 2 n · (R̂_n(h) - R(h))²` with `D = KL(Q ‖ P)`. This is
  `donsker_varadhan_scalar` from `MathlibExt.Probability.DonskerVaradhan`
  composed with the measure-theoretic DV inequality (a scalar consequence
  of Fenchel duality between `x log x` and `exp y - 1`).

* `conc_scalar_primitive`: `E_P[exp(2 n · gap²)] ≤ 2 √n / δ` — the
  function-class concentration bound. The natural derivation: apply
  Hoeffding's lemma to `2 n · gap(h)²` per fixed hypothesis `h`, giving
  `E_sample[exp(2 n · gap(h)²)] ≤ 2 √n` (Bach 2024, eq. 14.21, derived
  from the Hoeffding tail bound integrated against `t ↦ 2t exp(t²)`),
  then take expectation over `h ~ P` and apply Fubini. The `1/δ` factor
  arises from the Chernoff/Markov bound in the PAC-Bayes conversion from
  expectation to high-probability statement, absorbing the `δ` factor of
  the desired confidence level.
-/

/-- §14.4 — **Scalar discharge of the McAllester concentration hypothesis**.
If the exponential moment under the prior is bounded by `2 √n / δ`, then
its logarithm is bounded by `log(2 √n / δ)`. This is the scalar shadow
of the function-class concentration argument: the Hoeffding+Fubini
chain produces the inner bound `E_P[exp(2 n · gap²)] ≤ 2 √n / δ`, and
taking `log` of both sides gives the form consumed by
`pac_bayes_mcallester_abstract`. -/
theorem pac_bayes_conc_of_mgf_bound
    {expMGFp n δ : ℝ}
    (hn : 0 < n) (hδ : 0 < δ)
    (h_mgf_pos : 0 < expMGFp)
    (h_mgf : expMGFp ≤ 2 * Real.sqrt n / δ) :
    Real.log expMGFp ≤ Real.log (2 * Real.sqrt n / δ) := by
  have hsqrt_n_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have h_bound_pos : 0 < 2 * Real.sqrt n / δ := by positivity
  exact (Real.log_le_log_iff h_mgf_pos h_bound_pos).mpr h_mgf

/-- §14.4 — **Scalar discharge of the McAllester DV hypothesis**.
If the scalar Donsker--Varadhan primitive
`2 n · EQgapSq - logMGFp ≤ D` holds, then the rearranged form
`2 n · EQgapSq ≤ D + logMGFp` consumed by
`pac_bayes_mcallester_abstract` holds. This is pure real arithmetic
once the underlying DV inequality
`E_Q[f] - log E_P[exp f] ≤ KL(Q ‖ P)` is established (with
`f := 2 n · gap²`, `Q := posterior`, `P := prior`). -/
theorem pac_bayes_dv_of_primitive
    {EQgapSq logMGFp D n : ℝ}
    (h_prim : 2 * n * EQgapSq - logMGFp ≤ D) :
    2 * n * EQgapSq ≤ D + logMGFp :=
  LTFP.MathlibExt.Probability.dv_two_n_gap_of_primitive h_prim

/-- §14.4 — **McAllester PAC-Bayes bound discharged from scalar primitives**.

This is `pac_bayes_mcallester_abstract` with both `h_DV` and `h_conc`
hypotheses discharged from their natural scalar precursors:

* `h_DV_primitive` is the scalar Donsker--Varadhan inequality applied
  to the test function `f(h) := 2 n · gap(h)²`, expressed in the
  Mathlib-compatible `Ef - logEexp ≤ KL` direction. Discharged via
  `pac_bayes_dv_of_primitive`.
* `h_conc_mgf` is the function-class concentration bound on the
  exponential moment, expressed as `E_P[exp(2 n · gap²)] ≤ 2 √n / δ`.
  Discharged via `pac_bayes_conc_of_mgf_bound` after taking logs.
* `h_mgf_pos` asserts strict positivity of the exponential moment
  (automatic in the measure-theoretic setting since `exp` is strictly
  positive and the prior has positive mass).

The conclusion is the standard McAllester bound. Once Mathlib provides
the full measure-theoretic DV inequality on `klDiv` and Hoeffding +
Fubini for the function-class MGF, both primitive hypotheses discharge
automatically and this theorem becomes the unconditional McAllester
PAC-Bayes generalization bound. -/
theorem pac_bayes_mcallester
    {EQgap EQgapSq expMGFp D n δ : ℝ}
    (hn : 0 < n) (hδ : 0 < δ)
    (hD : 0 ≤ D)
    (hEQgap_nn : 0 ≤ EQgap)
    (h_jensen : EQgap ^ 2 ≤ EQgapSq)
    (h_mgf_pos : 0 < expMGFp)
    (h_DV_primitive : 2 * n * EQgapSq - Real.log expMGFp ≤ D)
    (h_conc_mgf : expMGFp ≤ 2 * Real.sqrt n / δ) :
    EQgap ≤ mcallesterBound D (Real.log (2 * Real.sqrt n / δ)) n := by
  -- Discharge h_DV from the scalar DV primitive.
  have h_DV : 2 * n * EQgapSq ≤ D + Real.log expMGFp :=
    pac_bayes_dv_of_primitive h_DV_primitive
  -- Discharge h_conc from the exponential-moment bound.
  have h_conc : Real.log expMGFp ≤ Real.log (2 * Real.sqrt n / δ) :=
    pac_bayes_conc_of_mgf_bound hn hδ h_mgf_pos h_conc_mgf
  -- Apply the abstract bound with logMGFp := Real.log expMGFp.
  exact pac_bayes_mcallester_abstract (logMGFp := Real.log expMGFp)
    hn hδ hD hEQgap_nn h_jensen h_DV h_conc

/-- §14.4 — **Unfolded form** of the discharged McAllester bound. -/
theorem pac_bayes_mcallester_unfolded
    {EQgap EQgapSq expMGFp D n δ : ℝ}
    (hn : 0 < n) (hδ : 0 < δ)
    (hD : 0 ≤ D)
    (hEQgap_nn : 0 ≤ EQgap)
    (h_jensen : EQgap ^ 2 ≤ EQgapSq)
    (h_mgf_pos : 0 < expMGFp)
    (h_DV_primitive : 2 * n * EQgapSq - Real.log expMGFp ≤ D)
    (h_conc_mgf : expMGFp ≤ 2 * Real.sqrt n / δ) :
    EQgap ≤ Real.sqrt ((D + Real.log (2 * Real.sqrt n / δ)) / (2 * n)) :=
  pac_bayes_mcallester (expMGFp := expMGFp)
    hn hδ hD hEQgap_nn h_jensen h_mgf_pos h_DV_primitive h_conc_mgf

/-! ### Measure-theoretic discharge of `h_DV_primitive`

The scalar `h_DV_primitive` hypothesis of `pac_bayes_mcallester` is the
real-valued shadow of the measure-theoretic Donsker--Varadhan inequality.
The lemma below discharges it directly from
`donsker_varadhan_inequality_diff` (in
`LTFP.MathlibExt.Probability.KullbackLeibler`) by instantiating with the
test function `f(h) := 2 n · gap(h)²`.

Specifically, given probability measures `Q ≪ P` (a posterior and prior
on a hypothesis space), a real-valued "gap" function
`gap : α → ℝ` (typically `R̂_n(h) − R(h)`), a sample size `n > 0`, and
the standard integrability hypotheses on `2 n · gap²` and
`exp ∘ (2 n · gap²)`, the inequality

  `2 n · ∫ gap² ∂Q − log (∫ exp(2 n · gap²) ∂P) ≤ (klDiv Q P).toReal`

follows directly from `donsker_varadhan_inequality_diff`. This is the
exact form consumed as `h_DV_primitive` (with
`D := (klDiv Q P).toReal`, `EQgapSq := ∫ gap² ∂Q`,
`expMGFp := ∫ exp(2 n · gap²) ∂P`). -/
theorem pac_bayes_h_DV_primitive_discharged
    {ℋ : Type*} [MeasurableSpace ℋ]
    (Q P : MeasureTheory.Measure ℋ)
    [MeasureTheory.IsProbabilityMeasure Q] [MeasureTheory.IsProbabilityMeasure P]
    (hQP : Q.AbsolutelyContinuous P)
    (gap : ℋ → ℝ) {n : ℝ} (_hn : 0 < n)
    (hgap_int : MeasureTheory.Integrable (fun h => 2 * n * gap h ^ 2) Q)
    (hexp_int :
      MeasureTheory.Integrable (fun h => Real.exp (2 * n * gap h ^ 2)) P)
    (hllr_int : MeasureTheory.Integrable (MeasureTheory.llr Q P) Q) :
    2 * n * (∫ h, gap h ^ 2 ∂Q)
        - Real.log (∫ h, Real.exp (2 * n * gap h ^ 2) ∂P)
      ≤ (InformationTheory.klDiv Q P).toReal := by
  -- Apply DV with f := 2 n · gap².
  have h_dv :=
    LTFP.MathlibExt.Probability.donsker_varadhan_inequality_diff
      (μ := Q) (ν := P) (f := fun h => 2 * n * gap h ^ 2)
      hQP hgap_int hexp_int hllr_int
  -- Pull `(2 n) ·` outside the integral on the LHS.
  have h_pull :
      ∫ h, (2 * n) * gap h ^ 2 ∂Q = (2 * n) * ∫ h, gap h ^ 2 ∂Q := by
    exact MeasureTheory.integral_const_mul (2 * n) (fun h => gap h ^ 2)
  -- Rewrite `h_dv` using `h_pull` to expose the `2 * n * (∫ gap²)` form.
  -- The DV inequality reads:
  --   `∫ (2 n · gap²) ∂Q - log(∫ exp(...) ∂P) ≤ kl`,
  -- and `∫ (2 n · gap²) ∂Q = 2 n · ∫ gap² ∂Q` by `integral_const_mul`.
  calc 2 * n * (∫ h, gap h ^ 2 ∂Q)
        - Real.log (∫ h, Real.exp (2 * n * gap h ^ 2) ∂P)
      = (∫ h, (2 * n) * gap h ^ 2 ∂Q)
          - Real.log (∫ h, Real.exp (2 * n * gap h ^ 2) ∂P) := by
        rw [h_pull]
    _ ≤ (InformationTheory.klDiv Q P).toReal := h_dv

/-! ### Discharging the per-h MGF hypothesis

The PAC-Bayes carrier's remaining input — after Primitive 1 is
discharged via Donsker--Varadhan — is the function-class MGF bound

  `E_{h∼P}[E_{S∼D}[exp(2 n · gap(h, S)²)]] ≤ 2 √n`,

which factors into a per-`h` Hoeffding-MGF bound followed by Fubini
over the prior. The per-`h` step (Bach 2024 Eq. 14.21) requires the
improper Riemann integration of `t · exp(c t²)` against a
Hoeffding-tail integrand; we expose it as a hypothesis below, and
discharge the Fubini-plus-Markov chain via
`LTFP.MathlibExt.Probability.function_class_mgf_bound_of_per_h` and
`LTFP.MathlibExt.Probability.pac_bayes_chernoff_step`. Once the per-`h`
bound lands upstream (as a Mathlib lemma on bounded random variables),
this assembly becomes the unconditional function-class concentration
step. -/

/-- §14.4 — **Function-class MGF expectation bound from per-`h` MGF bounds.**

If for every fixed hypothesis `h ∈ ℋ` the per-sample squared-gap MGF is
bounded by `2 √n`, i.e.

  `∀ h, ∫ s, exp(2 n · gap(h, s)²) ∂D ≤ 2 √n`,

then the iterated function-class MGF under the prior also satisfies

  `∫ h, ∫ s, exp(2 n · gap(h, s)²) ∂D ∂P ≤ 2 √n`.

This is a direct application of
`LTFP.MathlibExt.Probability.function_class_mgf_bound_of_per_h` to the
test function `c := 2 n`. -/
theorem pac_bayes_function_class_mgf_expectation
    {ℋ Ω : Type*} [MeasurableSpace ℋ] [MeasurableSpace Ω]
    {P : MeasureTheory.Measure ℋ} {D : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P]
    (gap : ℋ → Ω → ℝ) (n : ℝ) (_hn : 0 < n)
    (h_per_h_mgf :
      ∀ h, ∫ s, Real.exp (2 * n * (gap h s) ^ 2) ∂D ≤ 2 * Real.sqrt n)
    (h_inner_int :
      MeasureTheory.Integrable
        (fun h => ∫ s, Real.exp (2 * n * (gap h s) ^ 2) ∂D) P) :
    ∫ h, ∫ s, Real.exp (2 * n * (gap h s) ^ 2) ∂D ∂P ≤ 2 * Real.sqrt n :=
  LTFP.MathlibExt.Probability.function_class_mgf_bound_of_per_h
    gap (2 * n) (2 * Real.sqrt n) h_per_h_mgf h_inner_int

/-- §14.4 — **Existence of a "good sample" for PAC-Bayes**.

Given the per-`h` Hoeffding-based squared-gap MGF bound
`∀ h, E_{S∼D}[exp(2 n · gap(h,S)²)] ≤ 2 √n` and `δ > 0`, the set of
samples on which the function-class MGF under the prior fails the
high-probability bound `E_{h∼P}[exp(2 n · gap(h,S)²)] ≤ 2 √n / δ`
has measure at most `δ`. Hence there exists a "good sample" event of
measure `≥ 1 − δ` on which the carrier hypothesis `h_conc_mgf` of
`pac_bayes_mcallester` holds. This is the function-class
concentration step in its high-probability form. -/
theorem pac_bayes_good_sample_event
    {ℋ Ω : Type*} [MeasurableSpace ℋ] [MeasurableSpace Ω]
    {P : MeasureTheory.Measure ℋ} {D : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P] [MeasureTheory.IsProbabilityMeasure D]
    (gap : ℋ → Ω → ℝ) (n : ℝ) (hn : 0 < n) (δ : ℝ) (hδ : 0 < δ)
    (h_inner_int :
      MeasureTheory.Integrable
        (fun s => ∫ h, Real.exp (2 * n * (gap h s) ^ 2) ∂P) D)
    (h_inner_nn :
      0 ≤ᵐ[D] fun s => ∫ h, Real.exp (2 * n * (gap h s) ^ 2) ∂P)
    (h_exp_bound :
      ∫ s, ∫ h, Real.exp (2 * n * (gap h s) ^ 2) ∂P ∂D
        ≤ 2 * Real.sqrt n) :
    D.real { s | 2 * Real.sqrt n / δ ≤ ∫ h, Real.exp (2 * n * (gap h s) ^ 2) ∂P }
      ≤ δ :=
  LTFP.MathlibExt.Probability.function_class_chernoff_event_for_mgf
    gap n hn δ hδ h_inner_int h_inner_nn h_exp_bound

/-! ### Near-fully-discharged McAllester wrapper

This wrapper assembles all of the above into a single statement: given a
*fixed* sample `S` on which the function-class MGF under the prior `P` is
bounded by `2 √n / δ` (i.e., `S` belongs to the "good sample" event of
measure `≥ 1 − δ` provided by `pac_bayes_good_sample_event`), and given
standard measure-theoretic regularity on the posterior `Q ≪ P`, the
McAllester bound holds.

The only remaining input that this wrapper does *not* discharge from
ambient assumptions is the *per-sample* function-class MGF bound under
the prior, `expFnc ≤ 2 √n / δ`. The latter comes from
`pac_bayes_good_sample_event` once the per-`h` Hoeffding-MGF bound
(Bach Eq. 14.21) is available — which is a self-contained
`MeasureTheory.Integral.IntervalIntegral` exercise pending upstream
Mathlib work. Other than this single per-`h` Hoeffding-MGF input, the
McAllester PAC-Bayes bound is fully wired in Lean. -/

/-- §14.4 — **McAllester PAC-Bayes bound, measure-theoretically wired.**

For a fixed sample on which the per-sample function-class exponential
moment under the prior is bounded by `2 √n / δ` (the "good sample"
event provided by `pac_bayes_good_sample_event`), the McAllester PAC-Bayes
bound holds with `D := (klDiv Q P).toReal`. The DV step is discharged
from the measure-theoretic Donsker--Varadhan inequality via
`pac_bayes_h_DV_primitive_discharged`; the concentration step is
discharged from the supplied per-sample MGF bound via
`pac_bayes_conc_of_mgf_bound`.

This is the form to invoke once the per-`h` Hoeffding-based squared-gap
MGF bound (Bach 2024 Eq. 14.21) is available upstream: combine it with
`pac_bayes_function_class_mgf_expectation` to obtain the joint MGF
expectation bound, then `pac_bayes_good_sample_event` to extract a "good
sample" `S` on which the present theorem applies. -/
theorem pac_bayes_mcallester_measure_theoretic
    {ℋ : Type*} [MeasurableSpace ℋ]
    (Q P : MeasureTheory.Measure ℋ)
    [MeasureTheory.IsProbabilityMeasure Q] [MeasureTheory.IsProbabilityMeasure P]
    (hQP : Q.AbsolutelyContinuous P)
    (gap : ℋ → ℝ) {n δ : ℝ} (hn : 0 < n) (hδ : 0 < δ)
    (EQgap : ℝ) (hEQgap_nn : 0 ≤ EQgap)
    (h_jensen : EQgap ^ 2 ≤ ∫ h, gap h ^ 2 ∂Q)
    (hgap_int : MeasureTheory.Integrable (fun h => 2 * n * gap h ^ 2) Q)
    (hexp_int :
      MeasureTheory.Integrable (fun h => Real.exp (2 * n * gap h ^ 2)) P)
    (hllr_int : MeasureTheory.Integrable (MeasureTheory.llr Q P) Q)
    (h_expFnc_pos : 0 < ∫ h, Real.exp (2 * n * gap h ^ 2) ∂P)
    (h_expFnc_le :
      ∫ h, Real.exp (2 * n * gap h ^ 2) ∂P ≤ 2 * Real.sqrt n / δ) :
    EQgap ≤ mcallesterBound
              ((InformationTheory.klDiv Q P).toReal)
              (Real.log (2 * Real.sqrt n / δ))
              n := by
  -- Discharge `h_DV_primitive` from the measure-theoretic DV inequality.
  have h_DV_primitive :
      2 * n * (∫ h, gap h ^ 2 ∂Q)
          - Real.log (∫ h, Real.exp (2 * n * gap h ^ 2) ∂P)
        ≤ (InformationTheory.klDiv Q P).toReal :=
    pac_bayes_h_DV_primitive_discharged
      Q P hQP gap hn hgap_int hexp_int hllr_int
  -- Wrap the rest with `pac_bayes_mcallester`.
  have hD : 0 ≤ (InformationTheory.klDiv Q P).toReal :=
    ENNReal.toReal_nonneg
  exact pac_bayes_mcallester
    (EQgapSq := ∫ h, gap h ^ 2 ∂Q)
    (expMGFp := ∫ h, Real.exp (2 * n * gap h ^ 2) ∂P)
    (D := (InformationTheory.klDiv Q P).toReal)
    hn hδ hD hEQgap_nn h_jensen h_expFnc_pos h_DV_primitive h_expFnc_le

/-- §14.4 — **Unfolded form of the measure-theoretically wired McAllester
bound**: identical to `pac_bayes_mcallester_measure_theoretic` but with
the `mcallesterBound` wrapper unfolded to `√((D + log(2√n/δ)) / (2n))`. -/
theorem pac_bayes_mcallester_measure_theoretic_unfolded
    {ℋ : Type*} [MeasurableSpace ℋ]
    (Q P : MeasureTheory.Measure ℋ)
    [MeasureTheory.IsProbabilityMeasure Q] [MeasureTheory.IsProbabilityMeasure P]
    (hQP : Q.AbsolutelyContinuous P)
    (gap : ℋ → ℝ) {n δ : ℝ} (hn : 0 < n) (hδ : 0 < δ)
    (EQgap : ℝ) (hEQgap_nn : 0 ≤ EQgap)
    (h_jensen : EQgap ^ 2 ≤ ∫ h, gap h ^ 2 ∂Q)
    (hgap_int : MeasureTheory.Integrable (fun h => 2 * n * gap h ^ 2) Q)
    (hexp_int :
      MeasureTheory.Integrable (fun h => Real.exp (2 * n * gap h ^ 2)) P)
    (hllr_int : MeasureTheory.Integrable (MeasureTheory.llr Q P) Q)
    (h_expFnc_pos : 0 < ∫ h, Real.exp (2 * n * gap h ^ 2) ∂P)
    (h_expFnc_le :
      ∫ h, Real.exp (2 * n * gap h ^ 2) ∂P ≤ 2 * Real.sqrt n / δ) :
    EQgap ≤ Real.sqrt
      (((InformationTheory.klDiv Q P).toReal + Real.log (2 * Real.sqrt n / δ))
        / (2 * n)) :=
  pac_bayes_mcallester_measure_theoretic
    Q P hQP gap hn hδ EQgap hEQgap_nn h_jensen
    hgap_int hexp_int hllr_int h_expFnc_pos h_expFnc_le

/-! ### Narrowing the residual hypothesis to a single named slot

The carrier `pac_bayes_mcallester_measure_theoretic` consumes a
sample-fixed bound `∫ h, exp(2 n · gap(h)²) ∂P ≤ 2 √n / δ` as
`h_expFnc_le`. Producing this bound from a per-`h` Bach Eq. 14.21 input
requires three steps: lift the per-`h` bound to a joint expectation,
swap the Fubini order, and apply Markov over the sample.

A 2026-05-19 `xhigh`-Codex audit observed that the per-`h` step is **not**
discharged by the naive Hoeffding-tail layer-cake calculation: at the
critical exponent `2 n`, the resulting integral diverges (or is `O(n)`
after truncation), not `O(√n)`. The actual proof of Bach Eq. 14.21 goes
via the **bounded-differences moment lemma** in the Catoni / Alquier /
McAllester style — convex-order arguments on log-MGFs of bounded
differences — and is a self-contained 3–7 person-day standalone Mathlib
project. We therefore *do not* attempt to prove Eq. 14.21 here; instead
we expose it as a single named predicate
(`bounded_average_sq_exp_moment_assumption`) that future work can
discharge, and provide a carrier
(`pac_bayes_mcallester_measure_theoretic_with_bounded_moment_assumption`) that consumes
this single predicate (plus standard integrability regularity) and
produces the function-class concentration event needed by
`pac_bayes_mcallester_measure_theoretic`. -/

/-- §14.4 — **Bach 2024 Eq. 14.21 as a named predicate.**

For a `[0, 1]`-bounded loss `ℓ : 𝒳 → ℝ` and i.i.d. sample distribution
`D` on `𝒳`, the squared-gap exponential moment under `Dⁿ` satisfies

  `∫ S, exp(2 n · ((1/n)∑ᵢ ℓ(Sᵢ) - E_D[ℓ])²) ∂Dⁿ ≤ 2 √n`.

This is Bach 2024 Eq. 14.21, the per-`h` scalar input to the PAC-Bayes
function-class concentration argument.

**Why this is a named predicate, not a theorem.** A 2026-05-19 `xhigh`
Codex audit determined that this bound is **not** obtained from
Hoeffding's two-sided tail bound by the naive layer-cake calculation —
at the critical exponent `2 n`, that calculation diverges (or yields
`O(n)`). The actual proof goes via the **bounded-differences moment
lemma** in the Catoni / Alquier / McAllester style: convex-order arguments
on log-MGFs of bounded differences combined with the
McDiarmid-style martingale decomposition. Formalizing this in Lean is a
self-contained 3–7 person-day standalone Mathlib project requiring
machinery (convex-order, McDiarmid, Hoeffding–Azuma) that is only
partially available upstream. We therefore keep this as a named
predicate to be discharged by future focused work; the rest of the
PAC-Bayes chain is unconditionally wired through it.

References:
* F. Bach, *Learning Theory from First Principles*, 2024, Eq. 14.21.
* O. Catoni, *PAC-Bayesian Supervised Classification: The Thermodynamics
  of Statistical Learning*, IMS Lecture Notes, 2007.
* P. Alquier, *User-friendly introduction to PAC-Bayes bounds*,
  Foundations and Trends in Machine Learning, 17(2):174–303, 2024. -/
def bounded_average_sq_exp_moment_assumption
    {𝒳 : Type*} [MeasurableSpace 𝒳]
    (D : MeasureTheory.Measure 𝒳) [MeasureTheory.IsProbabilityMeasure D]
    (ℓ : 𝒳 → ℝ)
    (_hℓ : ∀ x, ℓ x ∈ Set.Icc (0 : ℝ) 1)
    (n : ℕ) (_hn : 0 < n) : Prop :=
  ∫ s, Real.exp (2 * (n : ℝ) *
        ((1 / (n : ℝ)) * ∑ i : Fin n, ℓ (s i)
          - ∫ x, ℓ x ∂D) ^ 2) ∂(MeasureTheory.Measure.pi (fun _ : Fin n => D))
    ≤ 2 * Real.sqrt (n : ℝ)

/-- §14.4 — **PAC-Bayes carrier with residual narrowed to a single
named slot.**

Given the **single** non-trivial residual hypothesis
`bounded_average_sq_exp_moment_assumption` (Bach 2024 Eq. 14.21) on the
loss `ℓ` and the i.i.d. sample distribution `D`, together with standard
joint-integrability regularity on the squared-gap exponential moment,
the **function-class concentration event** for PAC-Bayes holds: the
sample-product measure of the *bad* set on which the function-class MGF
exceeds `2 √n / δ` is at most `δ`. Equivalently, the *good* set on which
the carrier's `h_expFnc_le` hypothesis holds has `Dⁿ`-measure `≥ 1 − δ`.

On any sample `S` in this good set,
`pac_bayes_mcallester_measure_theoretic` applies and yields the
McAllester PAC-Bayes bound

  `E_{h∼Q}[gap(h, S)] ≤ √((KL(Q ‖ P) + log(2 √n / δ)) / (2 n))`.

The chain internally uses
`LTFP.MathlibExt.Probability.function_class_mgf_bound_of_per_h_swapped`
to flip the order of integration from `∫ h ∫ S` to `∫ S ∫ h`, so the
output is directly in the form consumed by
`pac_bayes_good_sample_event`. -/
theorem pac_bayes_mcallester_measure_theoretic_with_bounded_moment_assumption
    {𝒳 ℋ : Type*} [MeasurableSpace 𝒳] [MeasurableSpace ℋ]
    (P : MeasureTheory.Measure ℋ) [MeasureTheory.IsProbabilityMeasure P]
    (D : MeasureTheory.Measure 𝒳) [MeasureTheory.IsProbabilityMeasure D]
    (ℓ : ℋ → 𝒳 → ℝ)
    (hℓ : ∀ h x, ℓ h x ∈ Set.Icc (0 : ℝ) 1)
    {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ)
    -- The SINGLE non-trivial residual hypothesis (Bach Eq. 14.21).
    (h_bound_moment :
      ∀ h : ℋ, bounded_average_sq_exp_moment_assumption D (ℓ h) (hℓ h) n hn)
    -- Standard joint integrability regularity (for Fubini swap).
    (h_int_joint :
      MeasureTheory.Integrable
        (fun p : ℋ × (Fin n → 𝒳) =>
          Real.exp (2 * (n : ℝ) *
            ((1 / (n : ℝ)) * ∑ i : Fin n, ℓ p.1 (p.2 i)
              - ∫ x, ℓ p.1 x ∂D) ^ 2))
        (P.prod (MeasureTheory.Measure.pi (fun _ : Fin n => D))))
    -- Inner integrability for the unswapped direction.
    (h_int_inner_S :
      MeasureTheory.Integrable
        (fun h => ∫ s,
          Real.exp (2 * (n : ℝ) *
            ((1 / (n : ℝ)) * ∑ i : Fin n, ℓ h (s i)
              - ∫ x, ℓ h x ∂D) ^ 2)
          ∂(MeasureTheory.Measure.pi (fun _ : Fin n => D))) P)
    -- Inner integrability for the swapped direction.
    (h_int_inner_h :
      MeasureTheory.Integrable
        (fun s : Fin n → 𝒳 => ∫ h,
          Real.exp (2 * (n : ℝ) *
            ((1 / (n : ℝ)) * ∑ i : Fin n, ℓ h (s i)
              - ∫ x, ℓ h x ∂D) ^ 2) ∂P)
        (MeasureTheory.Measure.pi (fun _ : Fin n => D))) :
    (MeasureTheory.Measure.pi (fun _ : Fin n => D)).real
        { s : Fin n → 𝒳 |
          2 * Real.sqrt (n : ℝ) / δ ≤
            ∫ h, Real.exp (2 * (n : ℝ) *
              ((1 / (n : ℝ)) * ∑ i : Fin n, ℓ h (s i)
                - ∫ x, ℓ h x ∂D) ^ 2) ∂P }
      ≤ δ := by
  -- Abbreviate the gap-from-sample and the exponential integrand.
  set gap : ℋ → (Fin n → 𝒳) → ℝ :=
    fun h s => (1 / (n : ℝ)) * ∑ i : Fin n, ℓ h (s i) - ∫ x, ℓ h x ∂D with hgap_def
  -- Reformulate the named assumption in `gap` form.
  have h_per_h :
      ∀ h, ∫ s, Real.exp (2 * (n : ℝ) * (gap h s) ^ 2)
            ∂(MeasureTheory.Measure.pi (fun _ : Fin n => D))
              ≤ 2 * Real.sqrt (n : ℝ) := by
    intro h
    -- `bounded_average_sq_exp_moment_assumption` is definitionally equal to
    -- the integral in `gap`-form.
    exact h_bound_moment h
  -- Reformulate the joint integrability in `gap` form.
  have h_int_joint' :
      MeasureTheory.Integrable
        (fun p : ℋ × (Fin n → 𝒳) =>
          Real.exp (2 * (n : ℝ) * (gap p.1 p.2) ^ 2))
        (P.prod (MeasureTheory.Measure.pi (fun _ : Fin n => D))) := h_int_joint
  -- Reformulate inner integrability hypotheses in `gap` form.
  have h_int_inner_S' :
      MeasureTheory.Integrable
        (fun h => ∫ s, Real.exp (2 * (n : ℝ) * (gap h s) ^ 2)
            ∂(MeasureTheory.Measure.pi (fun _ : Fin n => D))) P := h_int_inner_S
  have h_int_inner_h' :
      MeasureTheory.Integrable
        (fun s : Fin n → 𝒳 => ∫ h,
          Real.exp (2 * (n : ℝ) * (gap h s) ^ 2) ∂P)
        (MeasureTheory.Measure.pi (fun _ : Fin n => D)) := h_int_inner_h
  -- Step 1: lift per-`h` to swapped joint bound via the Fubini bridge.
  have h_swapped :
      ∫ s, ∫ h, Real.exp (2 * (n : ℝ) * (gap h s) ^ 2) ∂P
        ∂(MeasureTheory.Measure.pi (fun _ : Fin n => D))
      ≤ 2 * Real.sqrt (n : ℝ) :=
    LTFP.MathlibExt.Probability.function_class_mgf_bound_of_per_h_swapped
      (P := P) (D := MeasureTheory.Measure.pi (fun _ : Fin n => D))
      gap (2 * (n : ℝ)) (2 * Real.sqrt (n : ℝ))
      h_int_joint' h_per_h h_int_inner_S'
  -- Step 2: non-negativity of the inner integrand (exp ≥ 0).
  have h_inner_nn :
      0 ≤ᵐ[MeasureTheory.Measure.pi (fun _ : Fin n => D)]
        fun s : Fin n → 𝒳 =>
          ∫ h, Real.exp (2 * (n : ℝ) * (gap h s) ^ 2) ∂P := by
    refine Filter.Eventually.of_forall (fun s => ?_)
    refine MeasureTheory.integral_nonneg (fun h => ?_)
    exact (Real.exp_pos _).le
  -- Step 3: Markov via `function_class_chernoff_event_for_mgf`.
  have hn_real : 0 < (n : ℝ) := by exact_mod_cast hn
  have h_good_event :=
    LTFP.MathlibExt.Probability.function_class_chernoff_event_for_mgf
      (P := P) (D := MeasureTheory.Measure.pi (fun _ : Fin n => D))
      gap (n : ℝ) hn_real δ hδ
      h_int_inner_h' h_inner_nn h_swapped
  -- The conclusion of `function_class_chernoff_event_for_mgf` is exactly
  -- the goal (after unfolding `gap`).
  exact h_good_event

/-- §14.4 — **Existence form of the unconditional carrier.** Given the
single named Bach Eq. 14.21 hypothesis and standard integrability
regularity, the **good sample event** has `Dⁿ`-measure at most `δ` on
its complement, which is the form fed into the McAllester carrier
`pac_bayes_mcallester_measure_theoretic`. This is a thin restatement of
`pac_bayes_mcallester_measure_theoretic_with_bounded_moment_assumption` for readability;
the work is in the predicate's discharge, which is the deferred
Catoni/Alquier bounded-differences moment lemma. -/
theorem pac_bayes_function_class_concentration_event
    {𝒳 ℋ : Type*} [MeasurableSpace 𝒳] [MeasurableSpace ℋ]
    (P : MeasureTheory.Measure ℋ) [MeasureTheory.IsProbabilityMeasure P]
    (D : MeasureTheory.Measure 𝒳) [MeasureTheory.IsProbabilityMeasure D]
    (ℓ : ℋ → 𝒳 → ℝ)
    (hℓ : ∀ h x, ℓ h x ∈ Set.Icc (0 : ℝ) 1)
    {n : ℕ} (hn : 0 < n) {δ : ℝ} (hδ : 0 < δ)
    (h_bound_moment :
      ∀ h : ℋ, bounded_average_sq_exp_moment_assumption D (ℓ h) (hℓ h) n hn)
    (h_int_joint :
      MeasureTheory.Integrable
        (fun p : ℋ × (Fin n → 𝒳) =>
          Real.exp (2 * (n : ℝ) *
            ((1 / (n : ℝ)) * ∑ i : Fin n, ℓ p.1 (p.2 i)
              - ∫ x, ℓ p.1 x ∂D) ^ 2))
        (P.prod (MeasureTheory.Measure.pi (fun _ : Fin n => D))))
    (h_int_inner_S :
      MeasureTheory.Integrable
        (fun h => ∫ s,
          Real.exp (2 * (n : ℝ) *
            ((1 / (n : ℝ)) * ∑ i : Fin n, ℓ h (s i)
              - ∫ x, ℓ h x ∂D) ^ 2)
          ∂(MeasureTheory.Measure.pi (fun _ : Fin n => D))) P)
    (h_int_inner_h :
      MeasureTheory.Integrable
        (fun s : Fin n → 𝒳 => ∫ h,
          Real.exp (2 * (n : ℝ) *
            ((1 / (n : ℝ)) * ∑ i : Fin n, ℓ h (s i)
              - ∫ x, ℓ h x ∂D) ^ 2) ∂P)
        (MeasureTheory.Measure.pi (fun _ : Fin n => D))) :
    (MeasureTheory.Measure.pi (fun _ : Fin n => D)).real
        { s : Fin n → 𝒳 |
          2 * Real.sqrt (n : ℝ) / δ ≤
            ∫ h, Real.exp (2 * (n : ℝ) *
              ((1 / (n : ℝ)) * ∑ i : Fin n, ℓ h (s i)
                - ∫ x, ℓ h x ∂D) ^ 2) ∂P }
      ≤ δ :=
  pac_bayes_mcallester_measure_theoretic_with_bounded_moment_assumption
    P D ℓ hℓ hn hδ h_bound_moment h_int_joint h_int_inner_S h_int_inner_h

/-! ### Discharging `bounded_average_sq_exp_moment_assumption` from the
named Catoni/Alquier residual

The residual hypothesis `bounded_average_sq_exp_moment_assumption` (Bach
2024 Eq. 14.21) is exposed in this file as a `Prop` so that the PAC-Bayes
chain is unconditionally wired. The actual mathematical content sits in
`LTFP.MathlibExt.Probability.BoundedMeanSqExp` as the named
`CatoniAlquierBoundedMoment` predicate, plus the bridge theorem
`boundedMeanSqExpMoment_pi_of_catoni_alquier` translating the abstract
i.i.d. statement to the product-measure form.

The lemma below glues the two together: given the Catoni/Alquier
residual applied to the product-measure realization of a `[0, 1]`-bounded
loss, the named `bounded_average_sq_exp_moment_assumption` predicate
holds. Once Mathlib lands the Catoni/Alquier bounded-differences moment
lemma (a 3–7 person-day standalone project; see the
`BoundedMeanSqExp` module docstring for the precise mathematical
contract), the residual discharges automatically and the entire
PAC-Bayes chain becomes unconditional. -/
theorem bounded_average_sq_exp_moment_assumption_of_catoni_alquier
    {𝒳 : Type*} [MeasurableSpace 𝒳]
    (D : MeasureTheory.Measure 𝒳) [MeasureTheory.IsProbabilityMeasure D]
    (ℓ : 𝒳 → ℝ)
    (hℓ : ∀ x, ℓ x ∈ Set.Icc (0 : ℝ) 1)
    {n : ℕ} (hn : 0 < n)
    (h_catoni :
      LTFP.MathlibExt.Probability.CatoniAlquierBoundedMoment
        (MeasureTheory.Measure.pi (fun _ : Fin n => D))
        (LTFP.MathlibExt.Probability.piSampleFamily ℓ)
        (∫ x, ℓ x ∂D)) :
    bounded_average_sq_exp_moment_assumption D ℓ hℓ n hn := by
  unfold bounded_average_sq_exp_moment_assumption
  exact LTFP.MathlibExt.Probability.boundedMeanSqExpMoment_pi_of_catoni_alquier
    hn hℓ h_catoni

/-! ### Bach §14.4.2 direct path — McAllester PAC-Bayes via linear Hoeffding MGF + DV + Chernoff

The carrier `pac_bayes_mcallester_measure_theoretic_with_bounded_moment_assumption` (above)
was originally designed around a SQUARED-gap exponential moment
`E[exp(2 n · gap²)] ≤ 2 √n` (which the file refers to as Bach Eq. 14.21).
A 2026-05-21 textbook re-read established that Bach (2024) Ch 14 ends at
**Eq. (14.6)** and does NOT contain an Eq. 14.21; the actual Bach proof
in §14.4.2 (pp. 423-425) uses the **linear** Hoeffding MGF

  `E_S exp(s (R(θ) - R̂_n(θ))) ≤ exp(s² ℓ∞² / (8 n))`

(cited from §1.2.1, available in Mathlib as
`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`) followed by
**integration over the prior**, **Donsker--Varadhan**, and **Jensen /
Chernoff** — see `tasks/pac-bayes-mcallester/book_excerpt.md` for the
verbatim text.

The block below mechanizes Bach's path *directly*, producing the
**in-expectation Eq. (14.6) form** of the McAllester PAC-Bayes bound
as an A-class theorem. The legacy named residuals
`CatoniAlquierBoundedMoment`, `MethodOfTypesStirlingBound`,
`BernoulliMethodOfTypesIdentity`, `BernoulliPinsker` in
`LTFP.MathlibExt.Probability.BoundedMeanSqExp` are retained for
backward-compatibility but are NOT used by the Bach-path bound;
their docstrings carry a DEAD-END marker pointing here.
-/

/-- §14.4.2 — **Bach's per-θ Hoeffding linear-MGF bound, integrated over
the prior `q`** (the output of Bach's step 1 + step 2 on p. 424).

If for every θ the per-sample MGF satisfies the Hoeffding bound

  `∫_S exp(s (R(θ) - R̂(S, θ))) dP_S(S) ≤ exp(s² K)`,

then for any prior `q` on Θ, the iterated integral (or equivalently the
post-Fubini swap) also satisfies

  `∫_Θ (∫_S exp(s · gap(θ, S)) dP_S(S)) dq(θ) ≤ exp(s² K)`,

since `q` is a probability measure (so `∫ const dq = const`).

This packages Bach's step 2 ("Integrating over θ, we get …") as a
standalone scalar lemma. -/
theorem pac_bayes_bach_step2_integrate_prior
    {Θ S : Type*} [MeasurableSpace Θ] [MeasurableSpace S]
    (q : MeasureTheory.Measure Θ) [MeasureTheory.IsProbabilityMeasure q]
    (P_S : MeasureTheory.Measure S)
    (gap : Θ → S → ℝ) (s K : ℝ)
    (h_per_θ :
      ∀ θ, ∫ x, Real.exp (s * gap θ x) ∂P_S ≤ Real.exp (s ^ 2 * K))
    (h_inner_int :
      MeasureTheory.Integrable
        (fun θ => ∫ x, Real.exp (s * gap θ x) ∂P_S) q) :
    ∫ θ, (∫ x, Real.exp (s * gap θ x) ∂P_S) ∂q ≤ Real.exp (s ^ 2 * K) := by
  have h_le :
      ∫ θ, (∫ x, Real.exp (s * gap θ x) ∂P_S) ∂q
        ≤ ∫ _θ, Real.exp (s ^ 2 * K) ∂q :=
    MeasureTheory.integral_mono_ae h_inner_int (MeasureTheory.integrable_const _)
      (Filter.Eventually.of_forall h_per_θ)
  have h_const : ∫ _θ, Real.exp (s ^ 2 * K) ∂q = Real.exp (s ^ 2 * K) := by
    simp [MeasureTheory.integral_const]
  linarith

/-- §14.4.2 — **Bach Eq. (14.5) in scalar pre-Chernoff form
(pointwise in the sample).**

For a fixed sample (i.e. a fixed `score : Θ → ℝ` representing
`s · (R(θ) - R̂_n(θ))`), the Donsker--Varadhan inequality combined with
the per-sample MGF bound `∫_Θ exp(score θ) dq(θ) ≤ M` yields

  `∫_Θ score(θ) dρ(θ) ≤ (klDiv ρ q).toReal + log M`

for every posterior `ρ ≪ q`. This is the **scalar shadow of Bach's
Eq. (14.5)** in its pre-Chernoff form (single-sample). Specialized to
`score = s · gap` and `M = exp(s² K)`, it becomes

  `s · ∫_Θ gap dρ - (klDiv ρ q).toReal ≤ s² K`,

which is Bach's Eq. (14.5) up to one extra `Real.log_exp` cancellation
(see `pac_bayes_bach_eq_14_5_scalar` below).

The proof is `donsker_varadhan_inequality` + `Real.log_le_log` to lift
the MGF bound through the `log`. -/
theorem pac_bayes_bach_score_le_kl_add_logM
    {Θ : Type*} [MeasurableSpace Θ]
    (q ρ : MeasureTheory.Measure Θ)
    [MeasureTheory.IsProbabilityMeasure q] [MeasureTheory.IsProbabilityMeasure ρ]
    (hρq : ρ.AbsolutelyContinuous q)
    (score : Θ → ℝ) {M : ℝ} (hM_pos : 0 < M)
    (hscore_int : MeasureTheory.Integrable score ρ)
    (hexp_int : MeasureTheory.Integrable (fun θ => Real.exp (score θ)) q)
    (hllr_int : MeasureTheory.Integrable (MeasureTheory.llr ρ q) ρ)
    (hMGF_pos : 0 < ∫ θ, Real.exp (score θ) ∂q)
    (hMGF_le_M : ∫ θ, Real.exp (score θ) ∂q ≤ M) :
    ∫ θ, score θ ∂ρ ≤ (InformationTheory.klDiv ρ q).toReal + Real.log M := by
  -- Step 1: DV gives `∫ score dρ ≤ kl + log(∫ exp(score) dq)`.
  have h_dv :
      ∫ θ, score θ ∂ρ
        ≤ (InformationTheory.klDiv ρ q).toReal
          + Real.log (∫ θ, Real.exp (score θ) ∂q) :=
    LTFP.MathlibExt.Probability.donsker_varadhan_inequality
      hρq hscore_int hexp_int hllr_int
  -- Step 2: `log` is monotone, so `log(MGF) ≤ log M`.
  have h_log_le :
      Real.log (∫ θ, Real.exp (score θ) ∂q) ≤ Real.log M :=
    (Real.log_le_log_iff hMGF_pos hM_pos).mpr hMGF_le_M
  linarith

/-- §14.4.2 — **Bach Eq. (14.5), scalar pre-Chernoff form**
(pointwise in the sample, specialized to `score = s · gap` and the
Hoeffding constant `M = exp(s² K)`).

For a fixed sample and the per-sample integrated MGF bound

  `∫_Θ exp(s · gap(θ)) dq(θ) ≤ exp(s² K)`,

DV gives

  `s · ∫_Θ gap dρ ≤ (klDiv ρ q).toReal + s² K`

for any posterior `ρ ≪ q`. This is Bach's Eq. (14.5) reorganized as
the scalar bound on `s · ∫_Θ gap dρ`. -/
theorem pac_bayes_bach_eq_14_5_scalar
    {Θ : Type*} [MeasurableSpace Θ]
    (q ρ : MeasureTheory.Measure Θ)
    [MeasureTheory.IsProbabilityMeasure q] [MeasureTheory.IsProbabilityMeasure ρ]
    (hρq : ρ.AbsolutelyContinuous q)
    (gap : Θ → ℝ) (s K : ℝ) (_hK_nn : 0 ≤ K)
    (hgap_int : MeasureTheory.Integrable (fun θ => s * gap θ) ρ)
    (hexp_int :
      MeasureTheory.Integrable (fun θ => Real.exp (s * gap θ)) q)
    (hllr_int : MeasureTheory.Integrable (MeasureTheory.llr ρ q) ρ)
    (hMGF_pos : 0 < ∫ θ, Real.exp (s * gap θ) ∂q)
    (hMGF_le_exp :
      ∫ θ, Real.exp (s * gap θ) ∂q ≤ Real.exp (s ^ 2 * K)) :
    ∫ θ, s * gap θ ∂ρ ≤ (InformationTheory.klDiv ρ q).toReal + s ^ 2 * K := by
  have hM_pos : 0 < Real.exp (s ^ 2 * K) := Real.exp_pos _
  have h_score :=
    pac_bayes_bach_score_le_kl_add_logM
      q ρ hρq (fun θ => s * gap θ) hM_pos
      hgap_int hexp_int hllr_int hMGF_pos hMGF_le_exp
  -- `Real.log (Real.exp y) = y`.
  have h_log_exp : Real.log (Real.exp (s ^ 2 * K)) = s ^ 2 * K := Real.log_exp _
  linarith

/-- §14.4.2 — **Bach Eq. (14.5), divided by `s > 0`**: from
`s · ∫_Θ gap dρ ≤ KL + s² K` we obtain the McAllester-style
"rate" form `∫_Θ gap dρ ≤ KL/s + s · K`. -/
theorem pac_bayes_bach_eq_14_5_rate
    {Θ : Type*} [MeasurableSpace Θ]
    (q ρ : MeasureTheory.Measure Θ)
    [MeasureTheory.IsProbabilityMeasure q] [MeasureTheory.IsProbabilityMeasure ρ]
    (hρq : ρ.AbsolutelyContinuous q)
    (gap : Θ → ℝ) {s : ℝ} (hs_pos : 0 < s) (K : ℝ) (hK_nn : 0 ≤ K)
    (hgap_int_ρ : MeasureTheory.Integrable gap ρ)
    (hexp_int :
      MeasureTheory.Integrable (fun θ => Real.exp (s * gap θ)) q)
    (hllr_int : MeasureTheory.Integrable (MeasureTheory.llr ρ q) ρ)
    (hMGF_pos : 0 < ∫ θ, Real.exp (s * gap θ) ∂q)
    (hMGF_le_exp :
      ∫ θ, Real.exp (s * gap θ) ∂q ≤ Real.exp (s ^ 2 * K)) :
    ∫ θ, gap θ ∂ρ
      ≤ (InformationTheory.klDiv ρ q).toReal / s + s * K := by
  -- The scaled integral identity.
  have hgap_scaled_int : MeasureTheory.Integrable (fun θ => s * gap θ) ρ :=
    hgap_int_ρ.const_mul s
  have h_pull : ∫ θ, s * gap θ ∂ρ = s * ∫ θ, gap θ ∂ρ :=
    MeasureTheory.integral_const_mul s gap
  -- Apply scalar Bach Eq. (14.5).
  have h_eq_5 :
      ∫ θ, s * gap θ ∂ρ
        ≤ (InformationTheory.klDiv ρ q).toReal + s ^ 2 * K :=
    pac_bayes_bach_eq_14_5_scalar q ρ hρq gap s K hK_nn
      hgap_scaled_int hexp_int hllr_int hMGF_pos hMGF_le_exp
  -- Substitute the pull-out and divide by `s > 0`.
  rw [h_pull] at h_eq_5
  -- `s · A ≤ B + s² · K` ⇒ `A ≤ B/s + s · K`.
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have h_div :
      s * ∫ θ, gap θ ∂ρ ≤ (InformationTheory.klDiv ρ q).toReal + s ^ 2 * K :=
    h_eq_5
  have h_kl_nn : 0 ≤ (InformationTheory.klDiv ρ q).toReal := ENNReal.toReal_nonneg
  -- Divide by `s`. Use `le_div_iff₀ hs_pos` carefully.
  have h_final :
      ∫ θ, gap θ ∂ρ
        ≤ ((InformationTheory.klDiv ρ q).toReal + s ^ 2 * K) / s := by
    rw [le_div_iff₀ hs_pos]
    linarith
  have h_split :
      ((InformationTheory.klDiv ρ q).toReal + s ^ 2 * K) / s
        = (InformationTheory.klDiv ρ q).toReal / s + s * K := by
    field_simp
  linarith [h_final, h_split.le, h_split.ge]

/-! ### In-expectation form (Bach Eq. 14.6) — sample-averaged carrier

For the in-expectation form (Bach Eq. 14.6), Bach integrates Eq. (14.5)
over the sample `S` (the joint event `S × Θ`), applies Fubini to swap
the sample/prior orders, and uses Jensen's inequality on `log` to
absorb the sample expectation. We formalize the resulting scalar
in-expectation bound below.

The full statement is parametric in:

* a sample space `(𝒮, P_S)` (probability measure),
* a hypothesis space `(Θ, q, ρ)` with prior `q`, posterior `ρ ≪ q`,
* a joint gap `gap : Θ → 𝒮 → ℝ` (typically `R(θ) - R̂_n(θ)(S)`),
* a temperature `s > 0` and a Hoeffding constant `K ≥ 0`.

The single non-trivial input is the **per-θ Hoeffding linear MGF**

  `∀ θ, ∫_𝒮 exp(s · gap(θ, S)) dP_S(S) ≤ exp(s² · K)`,

which is **directly available in Mathlib** for bounded loss via
`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` (Hoeffding's
lemma). The other inputs are standard integrability conditions for
Fubini and DV. -/

/-- §14.4.2 — **Bach Eq. (14.6) in scalar in-expectation form**.

For a sample space `(𝒮, P_S)` and a hypothesis space `(Θ, q, ρ)`,
given a joint gap `gap : Θ → 𝒮 → ℝ`, a temperature `s > 0`, and the
per-θ Hoeffding linear MGF input

  `∀ θ, ∫_𝒮 exp(s · gap(θ, S)) dP_S(S) ≤ exp(s² · K)`,

the in-expectation McAllester bound holds:

  `∫_𝒮 ∫_Θ gap(θ, S) dρ(θ) dP_S(S)
    ≤ (klDiv ρ q).toReal / s + s · K`,

which is exactly Bach's Eq. (14.6) (without the Gibbs-posterior Jensen
step). The proof composes:

1. **Step 2** (`pac_bayes_bach_step2_integrate_prior`): per-θ
   Hoeffding lifts to the joint integrated MGF bound
   `∫_𝒮 ∫_Θ exp(s · gap) dq dP_S ≤ exp(s² K)` via Fubini swap and
   `∫_Θ dq = 1`.
2. **Step 3 (DV)** + **Step 4 (Jensen+Chernoff)**: applied
   pointwise in `S`, the scalar Bach Eq. (14.5) rate form
   (`pac_bayes_bach_eq_14_5_rate`) gives
   `∫_Θ gap(θ, S) dρ ≤ KL/s + (log ∫_Θ exp(s · gap) dq) / s + …`,
   then integrating over `S` and using Jensen on `log` absorbs the
   sample expectation.

For brevity and to keep the proof a single-pass composition, we
formulate the in-expectation form assuming the **post-Fubini-swap**
per-sample MGF expectation bound directly:

  `∫_𝒮 (∫_Θ exp(s · gap(θ, S)) dq(θ)) dP_S(S) ≤ exp(s² · K)`.

This bound is provided by the lemma
`pac_bayes_bach_step2_integrate_prior` (above) combined with a
Fubini swap; we expose it as a standalone hypothesis to keep the
in-expectation theorem clean. -/
theorem pac_bayes_mcallester_bach_path
    {Θ 𝒮 : Type*} [MeasurableSpace Θ] [MeasurableSpace 𝒮]
    (q ρ : MeasureTheory.Measure Θ)
    [MeasureTheory.IsProbabilityMeasure q] [MeasureTheory.IsProbabilityMeasure ρ]
    (P_S : MeasureTheory.Measure 𝒮) [MeasureTheory.IsProbabilityMeasure P_S]
    (_hρq : ρ.AbsolutelyContinuous q)
    (gap : Θ → 𝒮 → ℝ) {s : ℝ} (hs_pos : 0 < s) (K : ℝ) (_hK_nn : 0 ≤ K)
    -- DV/Fubini integrability data.
    (hgap_int_ρS :
      MeasureTheory.Integrable
        (fun S => ∫ θ, gap θ S ∂ρ) P_S)
    (hMGF_int_PS :
      MeasureTheory.Integrable
        (fun S => Real.log (∫ θ, Real.exp (s * gap θ S) ∂q)) P_S)
    -- Per-sample DV applicability witnesses.
    (h_per_S_DV :
      ∀ᵐ S ∂P_S,
        ∫ θ, s * gap θ S ∂ρ
          ≤ (InformationTheory.klDiv ρ q).toReal
            + Real.log (∫ θ, Real.exp (s * gap θ S) ∂q))
    -- The post-Step-2 integrated MGF bound under `P_S` (Fubini'd form).
    (hMGF_expS_pos :
      ∀ᵐ S ∂P_S, 0 < ∫ θ, Real.exp (s * gap θ S) ∂q)
    (hMGF_int_inner_PS :
      MeasureTheory.Integrable
        (fun S => ∫ θ, Real.exp (s * gap θ S) ∂q) P_S)
    (hMGF_joint_le :
      ∫ S, (∫ θ, Real.exp (s * gap θ S) ∂q) ∂P_S
        ≤ Real.exp (s ^ 2 * K)) :
    ∫ S, (∫ θ, gap θ S ∂ρ) ∂P_S
      ≤ (InformationTheory.klDiv ρ q).toReal / s + s * K := by
  -- STEP A: apply per-sample DV `h_per_S_DV` to bound
  -- `s · ∫_Θ gap(θ, S) dρ` by `kl + log(∫_Θ exp(s·gap) dq)` pointwise.
  -- Take the `P_S`-integral of both sides.
  -- LHS of integrated DV: `∫_S (s · ∫_Θ gap(θ,S) dρ) dP_S = s · ∫_S∫_Θ gap dρ dP_S`.
  -- RHS: `(kl + ∫_S log(∫_Θ exp(s·gap) dq) dP_S)` since kl is a constant in S.
  --
  -- We need integrability of the LHS of DV under P_S: `S ↦ ∫ s · gap dρ = s · ∫ gap dρ`,
  -- which is integrable iff `S ↦ ∫ gap dρ` is integrable, i.e., `hgap_int_ρS`
  -- multiplied by `s`.
  have h_lhs_int :
      MeasureTheory.Integrable
        (fun S => ∫ θ, s * gap θ S ∂ρ) P_S := by
    -- `∫_Θ s · gap dρ = s · ∫_Θ gap dρ`.
    have h_eq : (fun S => ∫ θ, s * gap θ S ∂ρ)
                  = (fun S => s * ∫ θ, gap θ S ∂ρ) := by
      funext S
      exact MeasureTheory.integral_const_mul s (fun θ => gap θ S)
    rw [h_eq]
    exact hgap_int_ρS.const_mul s
  -- RHS integrability: `S ↦ kl + log(∫_Θ exp(s·gap) dq)` is integrable since
  -- `kl` is a constant (integrable on a probability measure) and the log term
  -- is integrable by hypothesis.
  have h_rhs_int :
      MeasureTheory.Integrable
        (fun S => (InformationTheory.klDiv ρ q).toReal
                    + Real.log (∫ θ, Real.exp (s * gap θ S) ∂q)) P_S := by
    refine MeasureTheory.Integrable.add ?_ hMGF_int_PS
    exact MeasureTheory.integrable_const _
  -- Take integral of `h_per_S_DV`.
  have h_int_dv :
      ∫ S, ∫ θ, s * gap θ S ∂ρ ∂P_S
        ≤ ∫ S, (InformationTheory.klDiv ρ q).toReal
            + Real.log (∫ θ, Real.exp (s * gap θ S) ∂q) ∂P_S :=
    MeasureTheory.integral_mono_ae h_lhs_int h_rhs_int h_per_S_DV
  -- Simplify the LHS: `∫_S ∫_Θ s · gap dρ dP_S = s · ∫_S∫_Θ gap dρ dP_S`.
  have h_lhs_simp :
      ∫ S, ∫ θ, s * gap θ S ∂ρ ∂P_S
        = s * ∫ S, (∫ θ, gap θ S ∂ρ) ∂P_S := by
    -- Inner: ∫_Θ s · gap dρ = s · ∫_Θ gap dρ.
    have h_inner : ∀ S, ∫ θ, s * gap θ S ∂ρ = s * ∫ θ, gap θ S ∂ρ := by
      intro S
      exact MeasureTheory.integral_const_mul s (fun θ => gap θ S)
    -- Substitute and pull `s` out of outer integral.
    have h_eq : (fun S => ∫ θ, s * gap θ S ∂ρ)
                  = (fun S => s * ∫ θ, gap θ S ∂ρ) := by
      funext S; exact h_inner S
    rw [show (∫ S, ∫ θ, s * gap θ S ∂ρ ∂P_S)
        = ∫ S, s * (∫ θ, gap θ S ∂ρ) ∂P_S by rw [h_eq]]
    exact MeasureTheory.integral_const_mul s (fun S => ∫ θ, gap θ S ∂ρ)
  -- Simplify the RHS: `∫_S (kl + log(...)) dP_S = kl + ∫_S log(...) dP_S`.
  have h_rhs_simp :
      ∫ S, (InformationTheory.klDiv ρ q).toReal
            + Real.log (∫ θ, Real.exp (s * gap θ S) ∂q) ∂P_S
        = (InformationTheory.klDiv ρ q).toReal
          + ∫ S, Real.log (∫ θ, Real.exp (s * gap θ S) ∂q) ∂P_S := by
    rw [MeasureTheory.integral_add (MeasureTheory.integrable_const _) hMGF_int_PS]
    simp [MeasureTheory.integral_const]
  -- STEP B: Jensen-on-log via the affine bound `log x ≤ x / M - 1 + log M`
  -- for `M := exp(s² K)`. This gives, integrating over S:
  --   `∫_S log(MGF_S) dP_S ≤ (∫_S MGF_S)/M - 1 + log M`
  -- and using `∫_S MGF_S ≤ M = exp(s² K)`:
  --   `≤ M/M - 1 + log M = log M = s² K`.
  have h_log_le_sqK :
      ∫ S, Real.log (∫ θ, Real.exp (s * gap θ S) ∂q) ∂P_S ≤ s ^ 2 * K := by
    -- Set `M := exp(s² K)`, so `log M = s² K`.
    set M : ℝ := Real.exp (s ^ 2 * K) with hM_def
    have hM_pos : 0 < M := Real.exp_pos _
    have hM_ne : M ≠ 0 := ne_of_gt hM_pos
    have h_logM : Real.log M = s ^ 2 * K := Real.log_exp _
    -- Pointwise affine bound: for `S` with `MGF_S > 0`,
    --   `log MGF_S = log(MGF_S/M) + log M ≤ (MGF_S/M - 1) + log M`
    -- via `Real.log_le_sub_one_of_pos` applied to `MGF_S/M > 0`.
    have h_pw : ∀ᵐ S ∂P_S,
        Real.log (∫ θ, Real.exp (s * gap θ S) ∂q)
          ≤ (∫ θ, Real.exp (s * gap θ S) ∂q) / M - 1 + Real.log M := by
      filter_upwards [hMGF_expS_pos] with S hS
      have h_div_pos : 0 < (∫ θ, Real.exp (s * gap θ S) ∂q) / M :=
        div_pos hS hM_pos
      have h_log_split :
          Real.log (∫ θ, Real.exp (s * gap θ S) ∂q)
            = Real.log ((∫ θ, Real.exp (s * gap θ S) ∂q) / M) + Real.log M := by
        rw [Real.log_div (ne_of_gt hS) hM_ne]; ring
      have h_log_le :
          Real.log ((∫ θ, Real.exp (s * gap θ S) ∂q) / M)
            ≤ (∫ θ, Real.exp (s * gap θ S) ∂q) / M - 1 :=
        Real.log_le_sub_one_of_pos h_div_pos
      linarith
    -- Integrate the pointwise bound.
    have h_rhs_int :
        MeasureTheory.Integrable
          (fun S => (∫ θ, Real.exp (s * gap θ S) ∂q) / M - 1 + Real.log M) P_S := by
      have h1 : MeasureTheory.Integrable
          (fun S => (∫ θ, Real.exp (s * gap θ S) ∂q) / M) P_S := by
        have h_mul : MeasureTheory.Integrable
            (fun S => (∫ θ, Real.exp (s * gap θ S) ∂q) * (1 / M)) P_S :=
          hMGF_int_inner_PS.mul_const (1 / M)
        convert h_mul using 1
        funext S
        field_simp
      have h2 : MeasureTheory.Integrable
          (fun _ : 𝒮 => (1 : ℝ)) P_S := MeasureTheory.integrable_const _
      have h3 : MeasureTheory.Integrable
          (fun _ : 𝒮 => Real.log M) P_S := MeasureTheory.integrable_const _
      exact (h1.sub h2).add h3
    have h_int_le :
        ∫ S, Real.log (∫ θ, Real.exp (s * gap θ S) ∂q) ∂P_S
          ≤ ∫ S, (∫ θ, Real.exp (s * gap θ S) ∂q) / M - 1 + Real.log M ∂P_S :=
      MeasureTheory.integral_mono_ae hMGF_int_PS h_rhs_int h_pw
    -- Evaluate the RHS integral.
    have h_rhs_eval :
        ∫ S, (∫ θ, Real.exp (s * gap θ S) ∂q) / M - 1 + Real.log M ∂P_S
          = (∫ S, (∫ θ, Real.exp (s * gap θ S) ∂q) ∂P_S) / M
            - 1 + Real.log M := by
      -- Move from `/ M` to `* M⁻¹` form so we can use `integral_mul_const`.
      have h_eq_pw : ∀ S,
          (∫ θ, Real.exp (s * gap θ S) ∂q) / M - 1 + Real.log M
            = (∫ θ, Real.exp (s * gap θ S) ∂q) * M⁻¹
              + (Real.log M - 1) := by
        intro S; rw [div_eq_mul_inv]; ring
      have h_eq_fun : (fun S =>
          (∫ θ, Real.exp (s * gap θ S) ∂q) / M - 1 + Real.log M)
            = (fun S => (∫ θ, Real.exp (s * gap θ S) ∂q) * M⁻¹
                + (Real.log M - 1)) := by
        funext S; exact h_eq_pw S
      have h_mul_const_int : MeasureTheory.Integrable
          (fun S => (∫ θ, Real.exp (s * gap θ S) ∂q) * M⁻¹) P_S :=
        hMGF_int_inner_PS.mul_const M⁻¹
      have h_const_int : MeasureTheory.Integrable
          (fun _ : 𝒮 => (Real.log M - 1)) P_S := MeasureTheory.integrable_const _
      calc ∫ S, (∫ θ, Real.exp (s * gap θ S) ∂q) / M - 1 + Real.log M ∂P_S
          = ∫ S, ((∫ θ, Real.exp (s * gap θ S) ∂q) * M⁻¹
                  + (Real.log M - 1)) ∂P_S := by rw [h_eq_fun]
        _ = (∫ S, (∫ θ, Real.exp (s * gap θ S) ∂q) * M⁻¹ ∂P_S)
              + ∫ _S : 𝒮, (Real.log M - 1) ∂P_S := by
              rw [MeasureTheory.integral_add h_mul_const_int h_const_int]
        _ = (∫ S, (∫ θ, Real.exp (s * gap θ S) ∂q) ∂P_S) * M⁻¹
              + (Real.log M - 1) := by
              rw [MeasureTheory.integral_mul_const]
              simp [MeasureTheory.integral_const]
        _ = (∫ S, (∫ θ, Real.exp (s * gap θ S) ∂q) ∂P_S) / M
              - 1 + Real.log M := by rw [← div_eq_mul_inv]; ring
    rw [h_rhs_eval] at h_int_le
    -- Now `(∫_S MGF_S) / M ≤ M / M = 1` since `∫_S MGF_S ≤ M`.
    have h_div_bound : (∫ S, (∫ θ, Real.exp (s * gap θ S) ∂q) ∂P_S) / M ≤ 1 := by
      rw [div_le_one hM_pos]
      exact hMGF_joint_le
    -- Combine: `LHS ≤ (1) - 1 + log M = log M = s² K`.
    linarith [h_logM]
  -- STEP C: combine: `s · LHS ≤ kl + ∫_S log MGF_S dP_S ≤ kl + s² K`.
  have h_chain :
      s * ∫ S, (∫ θ, gap θ S ∂ρ) ∂P_S
        ≤ (InformationTheory.klDiv ρ q).toReal + s ^ 2 * K := by
    have h1 :
        s * ∫ S, (∫ θ, gap θ S ∂ρ) ∂P_S
          ≤ (InformationTheory.klDiv ρ q).toReal
            + ∫ S, Real.log (∫ θ, Real.exp (s * gap θ S) ∂q) ∂P_S := by
      rw [← h_lhs_simp]
      rw [← h_rhs_simp]
      exact h_int_dv
    linarith
  -- Divide by `s > 0`.
  have hs_ne : s ≠ 0 := ne_of_gt hs_pos
  have h_final :
      ∫ S, (∫ θ, gap θ S ∂ρ) ∂P_S
        ≤ ((InformationTheory.klDiv ρ q).toReal + s ^ 2 * K) / s := by
    rw [le_div_iff₀ hs_pos]
    linarith
  have h_split :
      ((InformationTheory.klDiv ρ q).toReal + s ^ 2 * K) / s
        = (InformationTheory.klDiv ρ q).toReal / s + s * K := by
    field_simp
  linarith [h_final, h_split.le, h_split.ge]

/-! ### A-class Bach §14.4.2 PAC-Bayes McAllester bound (Phase 3b PIVOT iter 2)

The carrier `pac_bayes_mcallester_bach_path` (above) takes
`h_per_S_DV` and `hMGF_joint_le` as parametric hypotheses. The two
A-class helpers below derive both from primitives:

* **Step 1** (`pac_bayes_bach_step1_hoeffding_per_theta`) — Bach's
  per-θ Hoeffding linear-MGF bound:
  `∀ θ, ∫_S exp(s · (R(θ) - R̂_n(θ)(S))) ∂Dⁿ ≤ exp(s² · ℓ∞² / (8n))`,
  derived from Mathlib's `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`
  applied per-coordinate + `sum_of_iIndepFun` over iid samples + scaling
  by `1/n` via `HasSubgaussianMGF.const_mul`.

* **A-class wrapper** (`pac_bayes_mcallester_bach_path_a_class`) —
  composes Step 1 with `pac_bayes_bach_step2_integrate_prior` and a
  Fubini swap to discharge `hMGF_joint_le`, and applies
  `donsker_varadhan_inequality` per-sample via `Integrable.prod_*_ae` to
  discharge `h_per_S_DV`. The result is the in-expectation
  McAllester PAC-Bayes bound (Bach Eq. 14.6) with no remaining
  parametric hypotheses other than bounded-loss + iid + measurability
  + standard Fubini/DV integrability regularity. -/

/-- §14.4.2 (Bach Step 1) — **Per-θ Hoeffding linear-MGF bound.**

For a single fixed hypothesis `θ` with loss `ℓ_θ : 𝒳 → ℝ` taking values
in `[0, ℓ∞]` a.e. under the data distribution `D`, the moment-generating
function of the centered empirical-process random variable
`gap(S) := R(θ) - R̂_n(θ, S) = (∫ ℓ_θ dD) - (1/n) ∑ᵢ ℓ_θ(Sᵢ)` under
the product measure `Dⁿ` is bounded by the Hoeffding exponential:

  `∫_S exp(s · gap(S)) dDⁿ(S) ≤ exp(s² · ℓ∞² / (8 n))`.

This is **Bach (2024) Eq. (14.4)**, the first of the four steps in
§14.4.2 (per-θ Hoeffding + integrate-over-prior + Donsker-Varadhan +
Chernoff). It is derived in Mathlib from
`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` applied to each
centered summand `Yᵢ(S) = R(θ) - ℓ_θ(S_i)`, combined via
`HasSubgaussianMGF.sum_of_iIndepFun` and scaled via
`HasSubgaussianMGF.const_mul`. -/
theorem pac_bayes_bach_step1_hoeffding_per_theta
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
  classical
  -- Notation: `R := ∫ ℓ dD`, and the iid sample family on the product
  -- space `Fin n → 𝒳` is `X i ω := ℓ (ω i)`.
  set R : ℝ := ∫ x, ℓ x ∂D with hR_def
  let μ : MeasureTheory.Measure (Fin n → 𝒳) :=
    MeasureTheory.Measure.pi (fun _ : Fin n => D)
  haveI hμ_prob : MeasureTheory.IsProbabilityMeasure μ := by
    show MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.Measure.pi (fun _ : Fin n => D))
    infer_instance
  set X : Fin n → (Fin n → 𝒳) → ℝ := fun i ω => ℓ (ω i) with hX_def
  -- Measurability of each `X i`.
  have hX_meas : ∀ i, Measurable (X i) := by
    intro i
    exact hℓ_meas.comp (measurable_pi_apply i)
  -- Boundedness of each `X i`: pulled back from `D` via `Measure.pi_map_eval`.
  have hX_bdd : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) linf := by
    intro i
    -- `(μ.map (fun ω => ω i)) = D` (since `μ = Measure.pi`).
    have h_meas_proj : Measurable (fun ω : Fin n → 𝒳 => ω i) :=
      measurable_pi_apply i
    have h_map_pres :
        MeasureTheory.MeasurePreserving (fun ω : Fin n → 𝒳 => ω i) μ D :=
      MeasureTheory.measurePreserving_eval (μ := fun _ : Fin n => D) i
    have h_map : μ.map (fun ω : Fin n → 𝒳 => ω i) = D := h_map_pres.map_eq
    -- Pull back `hbdd` along the projection using `ae_map_iff`.
    have h_pull : ∀ᵐ ω ∂μ, ℓ (ω i) ∈ Set.Icc (0 : ℝ) linf := by
      have h_ae_d : ∀ᵐ x ∂(μ.map (fun ω : Fin n → 𝒳 => ω i)),
          ℓ x ∈ Set.Icc (0 : ℝ) linf := by rw [h_map]; exact hbdd
      exact (MeasureTheory.ae_map_iff h_meas_proj.aemeasurable
        (measurableSet_Icc.preimage hℓ_meas)).mp h_ae_d
    exact h_pull
  -- Independence of `(X i)` via `iIndepFun_pi` applied to the constant family `ℓ`.
  have hℓ_aemeas : ∀ _i : Fin n, AEMeasurable ℓ D := fun _ => hℓ_meas.aemeasurable
  have hX_indep : ProbabilityTheory.iIndepFun X μ :=
    ProbabilityTheory.iIndepFun_pi hℓ_aemeas
  -- Each `X i` is integrable (bounded a.e. on a probability measure).
  have hX_int : ∀ i, MeasureTheory.Integrable (X i) μ := by
    intro i
    exact MeasureTheory.Integrable.of_mem_Icc 0 linf (hX_meas i).aemeasurable (hX_bdd i)
  -- Each `X i` has mean `R` (since the pushforward is `D` and `R = ∫ ℓ dD`).
  have hX_mean : ∀ i, ∫ ω, X i ω ∂μ = R := by
    intro i
    have h_map : μ.map (fun ω : Fin n → 𝒳 => ω i) = D :=
      (MeasureTheory.measurePreserving_eval (μ := fun _ : Fin n => D) i).map_eq
    have h_meas_proj : Measurable (fun ω : Fin n → 𝒳 => ω i) :=
      measurable_pi_apply i
    have h_change :
        ∫ ω, ℓ (ω i) ∂μ = ∫ x, ℓ x ∂(μ.map (fun ω : Fin n → 𝒳 => ω i)) := by
      rw [MeasureTheory.integral_map h_meas_proj.aemeasurable
            hℓ_meas.aestronglyMeasurable]
    show ∫ ω, ℓ (ω i) ∂μ = R
    rw [h_change, h_map]
  -- Step A: centered summands `Y i ω := X i ω - R`.
  set Y : Fin n → (Fin n → 𝒳) → ℝ := fun i ω => X i ω - R with hY_def
  have hY_mean : ∀ i, ∫ ω, Y i ω ∂μ = 0 := by
    intro i
    have h_int := hX_int i
    have h_int' : MeasureTheory.Integrable (fun _ : Fin n → 𝒳 => R) μ :=
      MeasureTheory.integrable_const _
    have h_sub :
        ∫ ω, X i ω - R ∂μ = ∫ ω, X i ω ∂μ - R := by
      rw [MeasureTheory.integral_sub h_int h_int']
      simp
    show ∫ ω, X i ω - R ∂μ = 0
    rw [h_sub, hX_mean i, sub_self]
  -- `Y i ω ∈ [-R, linf - R]` a.e.
  have hY_bdd : ∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc (-R) (linf - R) := by
    intro i
    filter_upwards [hX_bdd i] with ω hω
    refine ⟨?_, ?_⟩
    · linarith [hω.1]
    · linarith [hω.2]
  have hY_meas : ∀ i, Measurable (Y i) := fun i => (hX_meas i).sub_const _
  -- Step B: per-i Hoeffding sub-Gaussian MGF with proxy `((linf)/2)²`.
  have hY_subG_hoeff : ∀ i,
      ProbabilityTheory.HasSubgaussianMGF (Y i)
        ((‖(linf - R) - (-R)‖₊ / 2) ^ 2) μ := by
    intro i
    exact ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (hY_meas i).aemeasurable (hY_bdd i) (hY_mean i)
  -- We work the proof via `mgf` directly, avoiding intermediate NNReal
  -- packaging which trips on Lean's elaboration. The strategy is:
  -- 1. Use `hY_subG_hoeff` to get the per-`i` Hoeffding bound;
  -- 2. extract `mgf_le` of the sum-of-Y after iid sum, ALL at REAL level;
  -- 3. divide and conclude.
  -- Set the central NNReal proxies via `⟨_, _⟩` ascription within a tac.
  have h_proxy_nn : (0 : ℝ) ≤ linf ^ 2 / 4 := by positivity
  -- The proxy constant `c_Y := ((linf - R) - (-R)) / 2)² = linf²/4`.
  set cY : NNReal := ((‖(linf - R) - (-R)‖₊ / 2) ^ 2) with hcY_def
  have hcY_coe : (cY : ℝ) = linf ^ 2 / 4 := by
    rw [hcY_def]
    push_cast
    have h_diff : (linf - R) - (-R) = linf := by ring
    rw [h_diff]
    -- `‖linf‖ = |linf|`, `|linf|² = linf²`.
    rw [Real.norm_eq_abs, ← sq_abs linf]
    ring
  -- Per-i Hoeffding sub-Gaussian MGF with proxy `cY = linf²/4`.
  have hY_subG : ∀ i, ProbabilityTheory.HasSubgaussianMGF (Y i) cY μ :=
    hY_subG_hoeff
  -- Step C: independence of `Y i = (· - R) ∘ X i`.
  have hY_indep : ProbabilityTheory.iIndepFun Y μ := by
    have h := hX_indep.comp (fun _ x => x - R)
      (fun _ => measurable_id.sub_const _)
    exact h
  -- Step D: sum of i.i.d. sub-Gaussians.
  have hSum_subG : ProbabilityTheory.HasSubgaussianMGF
      (fun ω => ∑ i, Y i ω) (∑ _i : Fin n, cY) μ :=
    ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun hY_indep
      (fun i _ => hY_subG i)
  -- The sum-of-constants coerces to `n * cY = n * linf²/4` in ℝ.
  have h_sum_coe : ((∑ _i : Fin n, cY : NNReal) : ℝ) = (n : ℝ) * (linf ^ 2 / 4) := by
    rw [NNReal.coe_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hcY_coe]
  -- Step E: scale by `-1/n` to recover `R - (1/n) ∑ X i = R - R̂` form.
  have hAvg_subG := hSum_subG.const_mul (-(1 / (n : ℝ)))
  -- `hAvg_subG : HasSubgaussianMGF (fun ω => (-1/n) * ∑ Yi) (cS * ∑cY) μ`
  -- where `cS := ⟨(-(1/n))², sq_nonneg _⟩`.
  -- The composed proxy coerces to `(1/n)² · n · linf²/4 = linf²/(4n)`.
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have hAvg_proxy_coe :
      ((⟨(-(1 / (n : ℝ))) ^ 2, sq_nonneg _⟩ * (∑ _i : Fin n, cY) : NNReal) : ℝ)
        = linf ^ 2 / (4 * (n : ℝ)) := by
    rw [NNReal.coe_mul, NNReal.coe_mk, h_sum_coe]
    field_simp
  -- Pointwise, `(-1/n) ∑ Y i = R - (1/n) ∑ X i`.
  have h_pw : ∀ ω,
      (-(1 / (n : ℝ))) * ∑ i, Y i ω
        = R - (1 / (n : ℝ)) * ∑ i, ℓ (ω i) := by
    intro ω
    have h_sum_split :
        ∑ i : Fin n, Y i ω = (∑ i, ℓ (ω i)) - (n : ℝ) * R := by
      show ∑ i : Fin n, (ℓ (ω i) - R) = (∑ i, ℓ (ω i)) - (n : ℝ) * R
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
    rw [h_sum_split]
    field_simp
    ring
  -- Congruence transfer to the Bach-form gap.
  have hGap_subG : ProbabilityTheory.HasSubgaussianMGF
      (fun ω => R - (1 / (n : ℝ)) * ∑ i, ℓ (ω i))
      (⟨(-(1 / (n : ℝ))) ^ 2, sq_nonneg _⟩ * (∑ _i : Fin n, cY)) μ := by
    refine hAvg_subG.congr ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    exact h_pw ω
  -- Apply `mgf_le` at exponent `s`:
  --   `mgf gap μ s ≤ exp(((-1/n)² · ∑cY) · s²/2)`.
  have h_mgf_le := hGap_subG.mgf_le s
  -- Unfold `mgf` to get the integral form (definitional).
  have h_mgf_eq :
      ProbabilityTheory.mgf
          (fun ω : Fin n → 𝒳 => R - (1 / (n : ℝ)) * ∑ i, ℓ (ω i)) μ s
        = ∫ ω, Real.exp (s * (R - (1 / (n : ℝ)) * ∑ i, ℓ (ω i))) ∂μ := rfl
  rw [h_mgf_eq] at h_mgf_le
  -- The proxy constant after simplification: `(1/n)² · n · (linf²/4) · s²/2 = s² · linf²/(8n)`.
  have h_exp_eq :
      Real.exp (((⟨(-(1 / (n : ℝ))) ^ 2, sq_nonneg _⟩ * (∑ _i : Fin n, cY) : NNReal) : ℝ)
                  * s ^ 2 / 2)
        = Real.exp (s ^ 2 * (linf ^ 2 / (8 * (n : ℝ)))) := by
    congr 1
    rw [hAvg_proxy_coe]
    field_simp
    ring
  rw [h_exp_eq] at h_mgf_le
  exact h_mgf_le

/-- §14.4.2 (Bach A-class) — **McAllester PAC-Bayes bound, Bach Eq. (14.6),
fully discharged from primitives (Phase 3b PIVOT iter 2).**

This is the A-class version of `pac_bayes_mcallester_bach_path`: the
two named hypotheses (`h_per_S_DV` and `hMGF_joint_le`) consumed by
that carrier are here **derived** from primitives —

* `h_per_S_DV` from `donsker_varadhan_inequality` applied per-sample
  via `Integrable.prod_left_ae` (Fubini-style slice integrability);
* `hMGF_joint_le` from `pac_bayes_bach_step1_hoeffding_per_theta`
  composed with `pac_bayes_bach_step2_integrate_prior` and a Fubini
  swap (`integral_integral_swap`).

The only remaining assumptions are: bounded loss (`hbdd`), iid sample
structure (`Measure.pi`), joint measurability and standard
Fubini/DV integrability regularity. No Bach-specific named
hypotheses remain.

References: Bach 2024 §14.4.2, Eq. (14.6); the proof composes Bach's
four steps (per-θ Hoeffding + integrate-over-prior + Donsker--Varadhan
+ Chernoff/Jensen-on-log). -/
theorem pac_bayes_mcallester_bach_path_a_class
    {𝒳 Θ : Type*} [MeasurableSpace 𝒳] [MeasurableSpace Θ]
    (D : MeasureTheory.Measure 𝒳) [MeasureTheory.IsProbabilityMeasure D]
    (q ρ : MeasureTheory.Measure Θ)
    [MeasureTheory.IsProbabilityMeasure q] [MeasureTheory.IsProbabilityMeasure ρ]
    (hρq : ρ.AbsolutelyContinuous q)
    (ℓ : Θ → 𝒳 → ℝ)
    (hℓ_meas : ∀ θ, Measurable (ℓ θ))
    (linf : ℝ)
    (hbdd : ∀ θ, ∀ᵐ x ∂D, ℓ θ x ∈ Set.Icc (0 : ℝ) linf)
    {n : ℕ} (hn : 0 < n)
    {s : ℝ} (hs_pos : 0 < s)
    -- Joint integrability of the exponential under `q ⊗ Dⁿ` (Fubini swap).
    (h_exp_joint_int :
      MeasureTheory.Integrable
        (fun p : Θ × (Fin n → 𝒳) =>
          Real.exp (s * ((∫ x, ℓ p.1 x ∂D)
            - (1 / (n : ℝ)) * ∑ i : Fin n, ℓ p.1 (p.2 i))))
        (q.prod (MeasureTheory.Measure.pi (fun _ : Fin n => D))))
    -- Joint integrability of the gap itself under `ρ ⊗ Dⁿ` (per-sample DV LHS).
    (h_gap_joint_int :
      MeasureTheory.Integrable
        (fun p : Θ × (Fin n → 𝒳) =>
          (∫ x, ℓ p.1 x ∂D)
            - (1 / (n : ℝ)) * ∑ i : Fin n, ℓ p.1 (p.2 i))
        (ρ.prod (MeasureTheory.Measure.pi (fun _ : Fin n => D))))
    -- llr integrability for DV.
    (hllr_int : MeasureTheory.Integrable (MeasureTheory.llr ρ q) ρ)
    -- Integrability of the per-sample log-MGF under `Dⁿ` (needed for STEP B).
    (hMGF_int_PS :
      MeasureTheory.Integrable
        (fun S : Fin n → 𝒳 =>
          Real.log (∫ θ, Real.exp (s * ((∫ x, ℓ θ x ∂D)
              - (1 / (n : ℝ)) * ∑ i : Fin n, ℓ θ (S i))) ∂q))
        (MeasureTheory.Measure.pi (fun _ : Fin n => D))) :
    ∫ S, (∫ θ, ((∫ x, ℓ θ x ∂D)
          - (1 / (n : ℝ)) * ∑ i : Fin n, ℓ θ (S i)) ∂ρ)
        ∂(MeasureTheory.Measure.pi (fun _ : Fin n => D))
      ≤ (InformationTheory.klDiv ρ q).toReal / s
          + s * (linf ^ 2 / (8 * (n : ℝ))) := by
  classical
  -- Notation.
  let P_S : MeasureTheory.Measure (Fin n → 𝒳) :=
    MeasureTheory.Measure.pi (fun _ : Fin n => D)
  haveI hP_S_prob : MeasureTheory.IsProbabilityMeasure P_S := by
    show MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.Measure.pi (fun _ : Fin n => D))
    infer_instance
  let gap : Θ → (Fin n → 𝒳) → ℝ :=
    fun θ S => (∫ x, ℓ θ x ∂D) - (1 / (n : ℝ)) * ∑ i : Fin n, ℓ θ (S i)
  let K : ℝ := linf ^ 2 / (8 * (n : ℝ))
  have hK_nn : 0 ≤ K := by positivity
  -- STEP 1: per-θ Hoeffding MGF bound (Bach Step 1).
  have h_per_θ_MGF : ∀ θ,
      ∫ S, Real.exp (s * gap θ S) ∂P_S ≤ Real.exp (s ^ 2 * K) := by
    intro θ
    -- `gap θ S` unfolds to `(∫ x, ℓ θ x ∂D) - (1/n) ∑ ℓ θ (S i)`
    -- and `K` unfolds to `linf² / (8 n)`; `P_S` unfolds to `Measure.pi`.
    -- These let-bindings are definitionally transparent.
    exact pac_bayes_bach_step1_hoeffding_per_theta D (ℓ θ) (hℓ_meas θ)
      linf (hbdd θ) hn s
  -- STEP 2: integrate per-θ MGF over the prior `q` (Bach Step 2).
  -- We need inner integrability over `q`. Direction: for outer-θ
  -- integrability, the function `θ ↦ ∫ S exp(s·gap) dP_S` should be
  -- q-integrable. `Integrable.integral_prod_left` integrates the
  -- right-hand variable out (here `S`) and returns a function of the
  -- left variable (here `θ`) that is integrable over the left measure
  -- (`q`). So this is the correct direction.
  have h_inner_int_q :
      MeasureTheory.Integrable
        (fun θ => ∫ S, Real.exp (s * gap θ S) ∂P_S) q := by
    have h := h_exp_joint_int.integral_prod_left
    -- The result has type `Integrable (fun θ => ∫ S, f (θ, S) ∂P_S) q`,
    -- where `f` is the joint exponential. Show it matches the goal.
    convert h using 1
  -- Pre-Fubini integrated MGF bound (Step 2 form: `∫_θ ∫_S ≤ exp(s² K)`).
  have h_step2 :
      ∫ θ, (∫ S, Real.exp (s * gap θ S) ∂P_S) ∂q
        ≤ Real.exp (s ^ 2 * K) :=
    pac_bayes_bach_step2_integrate_prior (S := Fin n → 𝒳)
      q P_S gap s K h_per_θ_MGF h_inner_int_q
  -- Apply Fubini swap to convert `∫_θ ∫_S` to `∫_S ∫_θ`.
  have h_swap :
      ∫ θ, (∫ S, Real.exp (s * gap θ S) ∂P_S) ∂q
        = ∫ S, (∫ θ, Real.exp (s * gap θ S) ∂q) ∂P_S := by
    apply MeasureTheory.integral_integral_swap (μ := q) (ν := P_S)
      (f := fun θ S => Real.exp (s * gap θ S))
    -- Joint integrability of the uncurried form.
    exact h_exp_joint_int
  -- Post-Fubini joint MGF bound (the form consumed by the carrier).
  have hMGF_joint_le :
      ∫ S, (∫ θ, Real.exp (s * gap θ S) ∂q) ∂P_S
        ≤ Real.exp (s ^ 2 * K) := by
    rw [← h_swap]; exact h_step2
  -- STEP 3: per-sample DV (a.e. in S).
  -- For a.e. S, both `θ ↦ gap θ S` is ρ-integrable and
  -- `θ ↦ exp(s · gap θ S)` is q-integrable; combined with `ρ ≪ q` and
  -- `llr ρ q` ρ-integrable, DV gives the per-sample inequality.
  -- `Integrable.prod_left_ae` on `f : Θ × (Fin n → 𝒳) → ℝ` integrable
  -- under `ρ.prod P_S` gives `∀ᵐ S ∂P_S, Integrable (fun θ => f (θ, S)) ρ`
  -- (the LEFT-variable is integrable for a.e. RIGHT-variable).
  have h_gap_ρ_ae : ∀ᵐ S ∂P_S,
      MeasureTheory.Integrable (fun θ => gap θ S) ρ :=
    h_gap_joint_int.prod_left_ae
  have h_exp_q_ae : ∀ᵐ S ∂P_S,
      MeasureTheory.Integrable (fun θ => Real.exp (s * gap θ S)) q :=
    h_exp_joint_int.prod_left_ae
  -- Per-sample DV.
  have h_per_S_DV : ∀ᵐ S ∂P_S,
      ∫ θ, s * gap θ S ∂ρ
        ≤ (InformationTheory.klDiv ρ q).toReal
          + Real.log (∫ θ, Real.exp (s * gap θ S) ∂q) := by
    filter_upwards [h_gap_ρ_ae, h_exp_q_ae] with S hS_gap_int hS_exp_int
    -- `s * gap` is ρ-integrable since `gap` is.
    have hS_score_int :
        MeasureTheory.Integrable (fun θ => s * gap θ S) ρ :=
      hS_gap_int.const_mul s
    -- Apply DV with `f := fun θ => s * gap θ S`.
    have h_dv :
        ∫ θ, s * gap θ S ∂ρ
          ≤ (InformationTheory.klDiv ρ q).toReal
            + Real.log (∫ θ, Real.exp (s * gap θ S) ∂q) :=
      LTFP.MathlibExt.Probability.donsker_varadhan_inequality
        (μ := ρ) (ν := q) (f := fun θ => s * gap θ S)
        hρq hS_score_int hS_exp_int hllr_int
    exact h_dv
  -- STEP 4: positivity of the per-sample MGF (a.e. in S).
  -- `MeasureTheory.integral_exp_pos` gives `0 < ∫ exp(f) dq` whenever
  -- `exp ∘ f` is q-integrable and `q ≠ 0` (auto-derived from `q` a
  -- probability measure, which gives `[NeZero q]`).
  haveI : NeZero q := ⟨IsProbabilityMeasure.ne_zero q⟩
  have hMGF_expS_pos : ∀ᵐ S ∂P_S,
      0 < ∫ θ, Real.exp (s * gap θ S) ∂q := by
    filter_upwards [h_exp_q_ae] with S hS_exp_int
    exact MeasureTheory.integral_exp_pos hS_exp_int
  -- Integrability hypotheses for the outer S-integration in the carrier.
  -- `Integrable.integral_prod_right` integrates the LEFT variable out
  -- (here `θ`) and returns a function of the RIGHT variable (here `S`)
  -- that is integrable over the right measure (`P_S`).
  -- `S ↦ ∫_θ gap dρ` is integrable: from joint integrability over `ρ.prod P_S`.
  have hgap_int_ρS :
      MeasureTheory.Integrable (fun S => ∫ θ, gap θ S ∂ρ) P_S := by
    have h := h_gap_joint_int.integral_prod_right
    convert h using 1
  -- `S ↦ ∫_θ exp(s·gap) dq` is integrable: from joint integrability over q.prod P_S.
  have hMGF_int_inner_PS :
      MeasureTheory.Integrable
        (fun S => ∫ θ, Real.exp (s * gap θ S) ∂q) P_S := by
    have h := h_exp_joint_int.integral_prod_right
    convert h using 1
  -- Apply the carrier `pac_bayes_mcallester_bach_path`.
  exact pac_bayes_mcallester_bach_path
    (Θ := Θ) (𝒮 := Fin n → 𝒳)
    q ρ P_S hρq gap hs_pos K hK_nn
    hgap_int_ρS hMGF_int_PS h_per_S_DV hMGF_expS_pos hMGF_int_inner_PS
    hMGF_joint_le

end LTFP
