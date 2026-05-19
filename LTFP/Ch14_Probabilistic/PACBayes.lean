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

end LTFP
