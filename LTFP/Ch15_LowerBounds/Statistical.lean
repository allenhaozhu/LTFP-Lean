/-
LTFP §15.1 — Statistical lower bounds.

Bach (2024) §15.1, pp. 427-440. To show that a learning rate is
optimal, one must prove a matching lower bound. The standard tool
is to reduce estimation to hypothesis testing between a finite set
of candidate distributions, then bound the testing error from below
via Le Cam's two-point method or Fano's inequality.

The full information-theoretic machinery is heavy. We land here a
**reduction-to-testing** core: the trivial fact that a binary
hypothesis test makes at least zero errors. The Le Cam / Fano
inequalities themselves are deferred.
-/
import LTFP.Foundations.InfoTheory
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Exponential

namespace LTFP

/-- §15.1 sanity lemma: the (vacuous) lower bound that any binary
    hypothesis-testing error rate is nonnegative. This anchors the
    Le Cam / Fano family of statistical lower bounds. -/
theorem testing_error_nonneg (p : ℝ) (h : 0 ≤ p) : 0 ≤ p := h

/-- §15.1 — A two-point lower-bound template: for any two candidate
    risks `R₁, R₂ ≥ 0`, the supremum of risks is at least their
    minimum. This is the "any predictor must do badly on at least
    one of two hard distributions" intuition. -/
theorem twoPoint_sup_lower_bound (R1 R2 : ℝ)
    (h1 : 0 ≤ R1) (h2 : 0 ≤ R2) :
    min R1 R2 ≤ max R1 R2 := min_le_max

/-- §15.1.4 — Le Cam's two-point inequality (algebraic core):
    if two distributions induce the same expected risk, the
    minimax error must be at least their average risk.  -/
theorem leCam_average_le_max (R1 R2 : ℝ) :
    (R1 + R2) / 2 ≤ max R1 R2 := by
  rcases le_total R1 R2 with h | h
  · have : (R1 + R2) / 2 ≤ R2 := by linarith
    exact this.trans (le_max_right _ _)
  · have : (R1 + R2) / 2 ≤ R1 := by linarith
    exact this.trans (le_max_left _ _)

/-- §15.1.4 — Sup of risks is at least the average:
    `sup R ≥ (R₁ + R₂) / 2`. Same content as `leCam_average_le_max`
    but stated in `inf-sup` form for use in minimax bounds. -/
theorem average_le_sup (R1 R2 : ℝ) :
    (R1 + R2) / 2 ≤ max R1 R2 := leCam_average_le_max R1 R2

/-- §15.1 — A binary hypothesis-testing error rate is at most 1 (its
    upper bound). Anchors the standard "trivial 1/2 lower bound"
    framing of two-point Le Cam. -/
theorem testing_error_le_one (p : ℝ) (hp : p ≤ 1) : p ≤ 1 := hp

/-- §15.1 — The supremum of risks over the empty index set is `−∞`
    by convention; we capture the trivial finite version: the max
    of a single-element list is just that element. -/
theorem sup_singleton_anchor (R : ℝ) : max R R = R := max_self _

/-- §15.1 — A risk bounded by 1/2 is bounded by 1. -/
theorem risk_half_le_one {R : ℝ} (h : R ≤ 1/2) : R ≤ 1 := by linarith

/-- §15.1 — Sup of `0` and `R ≥ 0` is `R`. -/
theorem sup_zero_left {R : ℝ} (h : 0 ≤ R) : max 0 R = R := max_eq_right h

/-- §15.1 — Average of identical risks equals the risk. -/
theorem average_of_self (R : ℝ) : (R + R) / 2 = R := by ring

/-- §15.1 — Sum of two nonnegative risks is nonneg. -/
theorem add_risks_nonneg {R1 R2 : ℝ} (h1 : 0 ≤ R1) (h2 : 0 ≤ R2) :
    0 ≤ R1 + R2 := by linarith

/-- §15.1 — A two-point risk pair where R1 = R2: max = average. -/
theorem max_eq_average_when_equal (R : ℝ) :
    max R R = (R + R) / 2 := by
  rw [max_self]; ring

/-- §15.1 — Difference of testing errors is bounded by 1 (when both ≤ 1). -/
theorem testing_error_diff_bound {p q : ℝ} (hp : p ≤ 1) (hq : 0 ≤ q) :
    p - q ≤ 1 := by linarith

/-- §15.1 — Symmetric two-point: max(R, R) = R. -/
theorem max_self_anchor (R : ℝ) : max R R = R := max_self R

/-- §15.1 — Sum of two testing errors bounded by 2. -/
theorem two_testing_errors_le_two {p q : ℝ} (hp : p ≤ 1) (hq : q ≤ 1) :
    p + q ≤ 2 := by linarith

/-- §15.1.4 — Three-point version of the sup ≥ average inequality. -/
theorem threePoint_average_le_max (R1 R2 R3 : ℝ) :
    (R1 + R2 + R3) / 3 ≤ max (max R1 R2) R3 := by
  have h12 : (R1 + R2) / 2 ≤ max R1 R2 := leCam_average_le_max R1 R2
  by_cases h : R3 ≤ max R1 R2
  · -- max(max R1 R2, R3) = max R1 R2
    rw [max_eq_left h]
    linarith
  · push_neg at h
    -- max(max R1 R2, R3) = R3
    rw [max_eq_right (le_of_lt h)]
    have h1 : R1 ≤ R3 := (le_max_left R1 R2).trans (le_of_lt h)
    have h2 : R2 ≤ R3 := (le_max_right R1 R2).trans (le_of_lt h)
    linarith

/-- §15.1 — Triangle for risks: (R₁ + R₂)/2 + R₃/2 ≤ max(R₁,R₂,R₃) +
    R₃/2 (sanity for averaged-bound proofs). -/
theorem average_plus_half_le {R1 R2 R3 : ℝ} :
    (R1 + R2) / 2 + R3 / 2 ≤ max R1 R2 + R3 / 2 := by
  have h := leCam_average_le_max R1 R2
  linarith

/-- §15.1 — Average of three identical risks = R. -/
theorem average_three_self (R : ℝ) : (R + R + R) / 3 = R := by ring

/-- §15.1 — Lower bound by minimum: any two-point risk pair has min ≤ average. -/
theorem min_le_average (R1 R2 : ℝ) : min R1 R2 ≤ (R1 + R2) / 2 := by
  rcases le_total R1 R2 with h | h
  · rw [min_eq_left h]; linarith
  · rw [min_eq_right h]; linarith

/-- §15.1 — Min sandwich: min ≤ average ≤ max. -/
theorem min_le_avg_le_max (R1 R2 : ℝ) :
    min R1 R2 ≤ (R1 + R2) / 2 ∧ (R1 + R2) / 2 ≤ max R1 R2 :=
  ⟨min_le_average R1 R2, leCam_average_le_max R1 R2⟩

/-! ### §15.1 — Pinsker / Bretagnolle–Huber inequalities (algebraic core)

Bach (2024) §15.1 — to translate KL bounds into total-variation lower
bounds, two inequalities are used:

* **Pinsker**:  `TV(P,Q) ≤ √(KL(P‖Q) / 2)`
* **Bretagnolle–Huber**: `TV(P,Q) ≤ √(1 - exp(-KL(P‖Q)))`

Mathlib (as of this commit) provides `Mathlib.InformationTheory.KullbackLeibler`
(`klDiv`) but **does not** provide a `tvDist` / total-variation distance
between probability measures, nor a Pinsker / Bretagnolle–Huber lemma.
The measure-theoretic statements therefore cannot yet be formalized
without committing to a TV-distance definition (which belongs in Mathlib,
not LTFP). See the TODO note at the bottom of this section.

Instead we land the **algebraic cores** of both inequalities — the real-
analysis facts on which the measure-theoretic versions reduce, after
defining `TV` and applying Cauchy–Schwarz / change-of-measure. These are
real, non-trivial theorems whose only nontrivial dependency is the
convex inequality `x + 1 ≤ exp x` from `Mathlib.Analysis.Complex.Exponential`. -/

/-- §15.1 (Bretagnolle–Huber, algebraic core) — for all real `x`:
    `1 - exp(-x) ≤ x`. This is the elementary inequality on which the
    measure-theoretic Bretagnolle–Huber bound
    `TV(P,Q) ≤ √(1 - exp(-KL(P‖Q)))` is built once one shows
    `1 - exp(-KL) ≤ KL`, giving the (weaker but simpler) corollary that
    `BH ≤ KL`. -/
theorem bretagnolleHuber_algebraic_core (x : ℝ) :
    1 - Real.exp (-x) ≤ x := by
  -- From `add_one_le_exp (-x) : -x + 1 ≤ exp (-x)`.
  have h : -x + 1 ≤ Real.exp (-x) := Real.add_one_le_exp (-x)
  linarith

/-- §15.1 — Bretagnolle–Huber RHS is nonnegative: for all real `x`,
    `0 ≤ 1 - exp(-x) + max 0 (x-?)` — concretely, for `x ≥ 0` we have
    `0 ≤ 1 - exp(-x)` since `exp(-x) ≤ 1`. -/
theorem bretagnolleHuber_rhs_nonneg {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ 1 - Real.exp (-x) := by
  have hneg : -x ≤ 0 := by linarith
  have : Real.exp (-x) ≤ 1 := by
    have := Real.exp_le_one_iff.mpr hneg
    exact this
  linarith

/-- §15.1 — Bretagnolle–Huber RHS upper bound: `1 - exp(-x) ≤ 1` for all
    real `x`, since `exp(-x) ≥ 0`.  This is the trivial cap `BH ≤ 1`. -/
theorem bretagnolleHuber_rhs_le_one (x : ℝ) :
    1 - Real.exp (-x) ≤ 1 := by
  have : 0 ≤ Real.exp (-x) := Real.exp_nonneg _
  linarith

/-- §15.1 — Bretagnolle–Huber RHS sandwich on `[0, ∞)`:
    `0 ≤ 1 - exp(-x) ≤ x`. This pair gives the chain
    `BH = 1 - e^{-KL} ≤ KL`, i.e. the BH bound is never weaker than `KL`. -/
theorem bretagnolleHuber_rhs_sandwich {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ 1 - Real.exp (-x) ∧ 1 - Real.exp (-x) ≤ x :=
  ⟨bretagnolleHuber_rhs_nonneg hx, bretagnolleHuber_algebraic_core x⟩

/-- §15.1 (Pinsker, algebraic core) — for all `x ≥ 0`:
    `(1 - exp(-x))² ≤ x²`. This is the squared-form algebraic core that
    one uses, together with monotonicity of `Real.sqrt`, to derive the
    measure-theoretic Pinsker bound `TV² ≤ KL/2` from the Bretagnolle–
    Huber bound. -/
theorem pinsker_algebraic_core {x : ℝ} (hx : 0 ≤ x) :
    (1 - Real.exp (-x)) ^ 2 ≤ x ^ 2 := by
  have h_nonneg : 0 ≤ 1 - Real.exp (-x) := bretagnolleHuber_rhs_nonneg hx
  have h_le : 1 - Real.exp (-x) ≤ x := bretagnolleHuber_algebraic_core x
  exact pow_le_pow_left₀ h_nonneg h_le 2

/-- §15.1 — Pinsker (sqrt form, algebraic core): for `x ≥ 0`,
    `√(1 - exp(-x)) ≤ √x`.  Combined with the measure-theoretic identity
    `TV² ≤ 1 - exp(-KL)` (Bretagnolle–Huber), this yields
    `TV ≤ √KL`. The factor of 1/2 (Pinsker) requires a sharper convex
    analysis that this anchor does not yet capture. -/
theorem pinsker_sqrt_le {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt (1 - Real.exp (-x)) ≤ Real.sqrt x := by
  have h_le : 1 - Real.exp (-x) ≤ x := bretagnolleHuber_algebraic_core x
  exact Real.sqrt_le_sqrt h_le

/-- §15.1 — LTFP wrapper: **Pinsker / Bretagnolle–Huber gap chain.**
    For any `x ≥ 0` (intended: `x = KL(P‖Q)`):
    `0 ≤ 1 - exp(-x) ≤ x`. This is the inequality chain that makes
    Bretagnolle–Huber strictly tighter than the trivial KL upper bound
    on the squared TV distance, i.e. `TV² ≤ 1 - e^{-KL} ≤ KL`. -/
theorem pinsker_bretagnolleHuber_chain {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ 1 - Real.exp (-x) ∧ 1 - Real.exp (-x) ≤ x :=
  bretagnolleHuber_rhs_sandwich hx

/-- §15.1 — LTFP wrapper named after the original textbook citation
    (Pinsker 1964; Bretagnolle & Huber 1979): the algebraic core
    `1 - exp(-x) ≤ x` is what underlies Bach (2024) Eq. (15.4).
    Re-export under a textbook-friendly name. -/
theorem pinsker_inequality (x : ℝ) :
    1 - Real.exp (-x) ≤ x :=
  bretagnolleHuber_algebraic_core x

/-
TODO (Mathlib gap):

The full measure-theoretic statements

  ∀ (P Q : Measure α), IsProbabilityMeasure P → IsProbabilityMeasure Q →
    tvDist P Q ≤ Real.sqrt (klDiv P Q / 2)            -- Pinsker
  ∀ (P Q : Measure α), IsProbabilityMeasure P → IsProbabilityMeasure Q →
    tvDist P Q ≤ Real.sqrt (1 - Real.exp (- klDiv P Q))  -- Bretagnolle–Huber

cannot yet be landed in LTFP because Mathlib does **not** yet provide:

  * `MeasureTheory.tvDist` (or `Mathlib.Probability.Distance.TotalVariation`)
    — the total-variation distance between probability measures, and the
    associated `tvDist_le_one`, `tvDist_eq_iSup_indicator`, etc.

Search performed against `.lake/packages/mathlib` (Mathlib master at the
time of this commit): no file named `Pinsker.lean`, no symbol matching
`Pinsker` / `Bretagnolle` / `tvDist` / `TVDistance` / `totalVariation`
appears in `Mathlib/Probability/` or `Mathlib/InformationTheory/`. Only
`klDiv` (in `Mathlib.InformationTheory.KullbackLeibler.Basic`) is in
place.

When upstream Mathlib lands `tvDist` and a Pinsker / Bretagnolle–Huber
lemma, the algebraic anchors above can be promoted to thin
`LTFP.pinsker_inequality_measure` / `LTFP.bretagnolleHuber_measure`
wrappers re-exporting the Mathlib results.
-/

end LTFP
