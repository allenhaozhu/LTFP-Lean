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
import Mathlib.Analysis.SpecialFunctions.Pow.Real

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

end LTFP
