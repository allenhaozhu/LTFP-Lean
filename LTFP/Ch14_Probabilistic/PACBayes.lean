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

end LTFP
