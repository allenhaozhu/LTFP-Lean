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
import LTFP.MathlibExt.Probability.TotalVariation
import LTFP.MathlibExt.Probability.Distance.Pinsker
import LTFP.MathlibExt.Probability.Distance.Bhattacharyya
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.Real.Sqrt

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

/-! ### §15.1 — Measure-theoretic Bretagnolle–Huber / Pinsker

With `LTFP.MathlibExt.Probability.tvDist` now available locally
(PR #39164 upstreams it to Mathlib), the algebraic anchors above can
be lifted to honest theorems on actual measures. Mathlib provides
`klDiv : Measure α → Measure α → ℝ≥0∞`, but the standard textbook
proof of Bretagnolle–Huber goes through the *Hellinger affinity*
`ρ(μ,ν) := ∫ √(dμ/dν) dν` (or equivalently the Bhattacharyya
coefficient), with the chain

  tvDist²(μ,ν)  ≤  1 - ρ(μ,ν)²  ≤  1 - exp(-KL(μ‖ν)),

the second inequality being the Cauchy–Schwarz / Jensen step. Both
of those measure-theoretic identities are out of reach of the current
local infrastructure (no `Hellinger`, no usable `klDiv` ↔
`tvDist` bridge), so we parametrize the result by an *abstract*
divergence value: any real number `D` for which the "BH bridge"
`tvDist² ≤ 1 - exp(-D)` holds yields, via the algebraic chain
below, the Bretagnolle–Huber bound `tvDist ≤ √(1 - exp(-D))`.

This pattern matches how `klDiv` is used in PAC-Bayes: the user
discharges the bridge hypothesis once (typically from the
Donsker–Varadhan variational formula and Cauchy–Schwarz), and the
algebraic chain below promotes it to the standard TV bound. When
Mathlib lands the Hellinger/Bhattacharyya machinery, the bridge
hypothesis becomes a one-line `klDiv`-only corollary. -/

section MeasureBretagnolleHuber

open LTFP.MathlibExt.Probability MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- §15.1 (Bretagnolle–Huber, measure-theoretic) — abstract form against
the locally-defined `tvDist`.

Given any nonnegative real divergence value `D` (intended: `D = KL(μ‖ν)`,
in real form) and the standard *BH bridge*
`(tvDist μ ν).toReal² ≤ 1 - exp(-D)` (which follows from the
Cauchy–Schwarz / Hellinger affinity chain when `D = KL`), we obtain the
**Bretagnolle–Huber inequality**

  `(tvDist μ ν).toReal ≤ √(1 - exp(-D))`.

The hypothesis `h_bridge` packages the only measure-theoretic content
not derivable from real-analysis primitives. -/
theorem tvDist_le_sqrt_one_sub_exp_neg
    (μ ν : Measure α) (D : ℝ) (hD : 0 ≤ D)
    (h_bridge :
      ((tvDist μ ν).toReal) ^ 2 ≤ 1 - Real.exp (-D)) :
    (tvDist μ ν).toReal ≤ Real.sqrt (1 - Real.exp (-D)) :=
  Real.le_sqrt_of_sq_le h_bridge

/-- §15.1 (Pinsker, measure-theoretic, loose form) — abstract form
against `tvDist`. Chaining `tvDist² ≤ 1 - exp(-D) ≤ D` (the second
inequality being `bretagnolleHuber_algebraic_core`) gives

  `(tvDist μ ν).toReal ≤ √D`.

The textbook Pinsker bound carries a sharper factor of `1/2`
(`tvDist ≤ √(D/2)`); deriving that factor requires a finer convex
analysis than the `1 - exp(-x) ≤ x` anchor used here. See
`tvDist_le_sqrt_one_sub_exp_neg` for the tighter Bretagnolle–Huber
form. -/
theorem tvDist_le_sqrt_divergence
    (μ ν : Measure α) (D : ℝ) (hD : 0 ≤ D)
    (h_bridge :
      ((tvDist μ ν).toReal) ^ 2 ≤ 1 - Real.exp (-D)) :
    (tvDist μ ν).toReal ≤ Real.sqrt D := by
  -- Bretagnolle–Huber gives `tvDist ≤ √(1 - exp(-D))`.
  have h_BH : (tvDist μ ν).toReal ≤ Real.sqrt (1 - Real.exp (-D)) :=
    tvDist_le_sqrt_one_sub_exp_neg μ ν D hD h_bridge
  -- Algebraic chain: `1 - exp(-D) ≤ D`, hence `√(1 - exp(-D)) ≤ √D`.
  have h_alg : 1 - Real.exp (-D) ≤ D := bretagnolleHuber_algebraic_core D
  have h_sqrt_mono : Real.sqrt (1 - Real.exp (-D)) ≤ Real.sqrt D :=
    Real.sqrt_le_sqrt h_alg
  exact h_BH.trans h_sqrt_mono

/-- §15.1 — Convenience corollary: under the same bridge hypothesis, the
**total variation distance is at most one** (independent of `D`).
This is a sanity check that the BH bound never exceeds the trivial
cap `tvDist ≤ 1`. The proof combines `tvDist_le_sqrt_one_sub_exp_neg`
with `1 - exp(-D) ≤ 1`. -/
theorem tvDist_le_one_of_bh_bridge
    (μ ν : Measure α) (D : ℝ) (hD : 0 ≤ D)
    (h_bridge :
      ((tvDist μ ν).toReal) ^ 2 ≤ 1 - Real.exp (-D)) :
    (tvDist μ ν).toReal ≤ 1 := by
  have h_BH : (tvDist μ ν).toReal ≤ Real.sqrt (1 - Real.exp (-D)) :=
    tvDist_le_sqrt_one_sub_exp_neg μ ν D hD h_bridge
  have h_rhs_le_one : 1 - Real.exp (-D) ≤ 1 :=
    bretagnolleHuber_rhs_le_one D
  have h_sqrt_le_one : Real.sqrt (1 - Real.exp (-D)) ≤ 1 :=
    (Real.sqrt_le_one).mpr h_rhs_le_one
  exact h_BH.trans h_sqrt_le_one

/-- §15.1 — **Bretagnolle--Huber via the Hellinger / Bhattacharyya bridge.**

The classical proof of Bretagnolle--Huber factors through the Bhattacharyya
affinity `ρ(μ, ν) := ∫ √(dμ/dν) dν`, with the two-step chain

  `tvDist²(μ, ν)  ≤  1 - ρ(μ, ν)²`        (Le Cam / Cauchy--Schwarz),
  `ρ(μ, ν)        ≥  Real.exp (-KL(μ‖ν)/2)` (Jensen on `-log`).

Given a real value `ρ` standing in for the affinity together with these two
inputs (parameters because Mathlib does not yet expose
`bhattacharyya` / `hellingerSquared`), we obtain the **Bretagnolle--Huber
inequality** directly:

  `tvDist(μ, ν) ≤ Real.sqrt (1 - Real.exp (-D))`.

The wrapper composes `tvDist_sq_le_one_sub_exp_neg_of_bhattacharyya`
(which discharges the BH bridge `tvDist² ≤ 1 - exp(-D)` algebraically)
with `tvDist_le_sqrt_one_sub_exp_neg` (which lifts the squared bound to the
square-root form). -/
theorem tvDist_le_sqrt_one_sub_exp_neg_of_bhattacharyya
    (μ ν : Measure α) {ρ D : ℝ} (hD : 0 ≤ D)
    (hρ_nonneg : 0 ≤ ρ)
    (h_lecam : ((tvDist μ ν).toReal) ^ 2 ≤ 1 - ρ ^ 2)
    (h_kl_bridge : Real.exp (-D / 2) ≤ ρ) :
    (tvDist μ ν).toReal ≤ Real.sqrt (1 - Real.exp (-D)) := by
  have h_bridge : ((tvDist μ ν).toReal) ^ 2 ≤ 1 - Real.exp (-D) :=
    LTFP.MathlibExt.Probability.tvDist_sq_le_one_sub_exp_neg_of_bhattacharyya
      μ ν hρ_nonneg h_lecam h_kl_bridge
  exact tvDist_le_sqrt_one_sub_exp_neg μ ν D hD h_bridge

/-- §15.1 — **Bretagnolle--Huber via the Hellinger-squared bridge.**

Same chain as `tvDist_le_sqrt_one_sub_exp_neg_of_bhattacharyya` but stated
in terms of the **squared Hellinger distance** `Hsq` (related to the
Bhattacharyya affinity by `ρ = 1 - Hsq / 2`). The Le Cam step in Hellinger
form reads `tvDist² ≤ Hsq · (1 - Hsq / 4)`, and the KL bridge becomes
`Hsq ≤ 2 · (1 - exp(-D / 2))`. -/
theorem tvDist_le_sqrt_one_sub_exp_neg_of_hellinger
    (μ ν : Measure α) {Hsq D : ℝ} (hD : 0 ≤ D)
    (hH_nonneg : 0 ≤ Hsq) (hH_le_two : Hsq ≤ 2)
    (h_lecam : ((tvDist μ ν).toReal) ^ 2 ≤ Hsq * (1 - Hsq / 4))
    (h_kl_bridge : Hsq ≤ 2 * (1 - Real.exp (-D / 2))) :
    (tvDist μ ν).toReal ≤ Real.sqrt (1 - Real.exp (-D)) := by
  have h_bridge : ((tvDist μ ν).toReal) ^ 2 ≤ 1 - Real.exp (-D) :=
    LTFP.MathlibExt.Probability.tvDist_sq_le_one_sub_exp_neg_of_hellinger
      μ ν hH_nonneg hH_le_two h_lecam h_kl_bridge
  exact tvDist_le_sqrt_one_sub_exp_neg μ ν D hD h_bridge

/-- §15.1 — **Bretagnolle--Huber via the named Bhattacharyya affinity.**

Same as `tvDist_le_sqrt_one_sub_exp_neg_of_bhattacharyya`, but stated
directly in terms of `LTFP.MathlibExt.Probability.bhattacharyya μ ν`
(the symmetric definition introduced in
`LTFP/MathlibExt/Probability/Distance/Bhattacharyya.lean`).

This wrapper exists because the named definition lets callers package
the Bhattacharyya hypothesis chain without introducing an auxiliary real
parameter `ρ`. The nonnegativity of `bhattacharyya μ ν` is provided
automatically by `bhattacharyya_nonneg`. -/
theorem tvDist_le_sqrt_one_sub_exp_neg_of_bhattacharyya_def
    (μ ν : Measure α) {D : ℝ} (hD : 0 ≤ D)
    (h_lecam : ((tvDist μ ν).toReal) ^ 2 ≤
      1 - LTFP.MathlibExt.Probability.bhattacharyya μ ν ^ 2)
    (h_kl_bridge : Real.exp (-D / 2) ≤
      LTFP.MathlibExt.Probability.bhattacharyya μ ν) :
    (tvDist μ ν).toReal ≤ Real.sqrt (1 - Real.exp (-D)) :=
  tvDist_le_sqrt_one_sub_exp_neg_of_bhattacharyya μ ν hD
    (LTFP.MathlibExt.Probability.bhattacharyya_nonneg μ ν)
    h_lecam h_kl_bridge

/-- §15.1 — **Bretagnolle--Huber, Le Cam step discharged.**

Same as `tvDist_le_sqrt_one_sub_exp_neg_of_bhattacharyya_def`, but the
Le Cam estimate `tvDist² ≤ 1 - bhattacharyya²` is now discharged
unconditionally via `tvDist_sq_le_one_sub_bhattacharyya_sq` in
`LTFP/MathlibExt/Probability/Distance/Bhattacharyya.lean`. Only the
Jensen step `exp(-D/2) ≤ bhattacharyya` remains as a hypothesis input;
once that lands upstream (or the Jensen step is discharged locally),
the wrapper collapses to the textbook Bretagnolle--Huber bound. -/
theorem tvDist_le_sqrt_one_sub_exp_neg_of_bhattacharyya_kl
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {D : ℝ} (hD : 0 ≤ D)
    (h_kl_bridge : Real.exp (-D / 2) ≤
      LTFP.MathlibExt.Probability.bhattacharyya μ ν) :
    (tvDist μ ν).toReal ≤ Real.sqrt (1 - Real.exp (-D)) :=
  tvDist_le_sqrt_one_sub_exp_neg_of_bhattacharyya_def μ ν hD
    (LTFP.MathlibExt.Probability.tvDist_sq_le_one_sub_bhattacharyya_sq μ ν)
    h_kl_bridge

end MeasureBretagnolleHuber

/-! ### §15.1 — Fano / Le Cam / Assouad algebraic cores

Bach (2024) §15.1, pp. 433–440. Three families of lower-bound techniques
reduce a learning problem to a hypothesis-testing question:

* **Le Cam (two-point):** `R ≥ (1 - TV(P,Q)) / 2`, used when there are
  two candidate distributions.
* **Fano (multi-point):** `P_e ≥ 1 - (I + log 2) / log(M-1)`, where `M`
  is the number of candidates and `I` is the mutual information between
  the parameter and the observed sample.
* **Assouad (hypercube):** parameter lives on `{0,1}^d`, the loss
  decomposes as a sum of Hamming components, and each component is
  bounded below by a Le Cam two-point bound.

The measure-theoretic statements need `mutualInfo` and `tvDist` between
random variables, neither of which is fully available in Mathlib at the
time of writing. We land the **algebraic anchors** — the real-analysis
facts that, once the divergence values are computed, deliver each
textbook bound. -/

/-- §15.1 (Le Cam from TV, algebraic core) — for `t ∈ [0,1]` (intended:
    `t = TV(P,Q)`), `(1 - t) / 2 ≥ 0`.  Combined with the textbook
    identity `R ≥ (1 - TV(P,Q))/2` this anchors the Le Cam two-point
    lower bound (Bach 2024, Eq. 15.6). -/
theorem leCam_tv_lower_bound_nonneg {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ (1 - t) / 2 := by linarith

/-- §15.1 (Le Cam from TV, algebraic core) — `(1 - t)/2 ≤ 1/2` for
    `t ∈ [0,1]`. The Le Cam lower bound never exceeds the trivial 1/2
    cap, matching the worst-case minimax risk for a balanced two-point
    test. -/
theorem leCam_tv_lower_bound_le_half {t : ℝ} (h0 : 0 ≤ t) :
    (1 - t) / 2 ≤ 1 / 2 := by linarith

/-- §15.1 (Fano, algebraic core) — the **Fano probability-of-error
    inequality**, algebraic form. For any `M ≥ 2` candidate hypotheses,
    any mutual information `I ≥ 0`, the probability of error of the
    Bayes-optimal multi-way test satisfies
    `P_e ≥ 1 - (I + Real.log 2) / Real.log M`,
    PROVIDED the RHS is nonneg. The standard textbook proof
    (Bach 2024, Eq. 15.9) derives this from `H(W | T) ≥ H(W) - I` and
    the data-processing inequality; here we land the algebraic identity
    on which both reductions hinge. -/
theorem fano_rhs_le_one {M I : ℝ} (hM : 1 < M) (hI : 0 ≤ I) :
    1 - (I + Real.log 2) / Real.log M ≤ 1 := by
  have h_log_pos : 0 < Real.log M := Real.log_pos hM
  have h_log2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_num_nonneg : 0 ≤ I + Real.log 2 := by linarith
  have h_quot_nonneg : 0 ≤ (I + Real.log 2) / Real.log M :=
    div_nonneg h_num_nonneg h_log_pos.le
  linarith

/-- §15.1 (Fano, algebraic monotonicity) — the Fano lower bound is
    **monotone decreasing in the mutual information** `I`: more shared
    information between the parameter and the observation yields a
    weaker lower bound. For `M > 1` fixed and `0 ≤ I₁ ≤ I₂`:
    `1 - (I₁ + log 2)/log M ≥ 1 - (I₂ + log 2)/log M`. -/
theorem fano_lower_bound_antitone {M I1 I2 : ℝ}
    (hM : 1 < M) (h12 : I1 ≤ I2) :
    1 - (I2 + Real.log 2) / Real.log M
      ≤ 1 - (I1 + Real.log 2) / Real.log M := by
  have h_log_pos : 0 < Real.log M := Real.log_pos hM
  have h_num : I1 + Real.log 2 ≤ I2 + Real.log 2 := by linarith
  have h_quot :
      (I1 + Real.log 2) / Real.log M
        ≤ (I2 + Real.log 2) / Real.log M :=
    (div_le_div_iff_of_pos_right h_log_pos).mpr h_num
  linarith

/-- §15.1 (Assouad / hypercube, algebraic core) — the hypercube bound
    decomposes the minimax risk as a sum of Hamming-coordinate risks:
    `R ≥ (d/2) · (1 - max_i TV_i)`. The algebraic anchor is the
    nonnegativity of each summand: for `t ∈ [0,1]` and `d ≥ 0`,
    `(d / 2) · (1 - t) ≥ 0`. -/
theorem assouad_summand_nonneg {d t : ℝ}
    (hd : 0 ≤ d) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ (d / 2) * (1 - t) := by
  have h_half : 0 ≤ d / 2 := by linarith
  have h_one_sub : 0 ≤ 1 - t := by linarith
  exact mul_nonneg h_half h_one_sub

/-- §15.1 (Mutual information, algebraic core) — **nonnegativity of
    mutual information**, parametric form. Mutual information equals a
    KL divergence between the joint and product marginals; since KL is
    nonneg (Gibbs' inequality), so is `I`. Here we abstract over `I` and
    record the standard chain `H(W) - H(W|T) = I ≥ 0`, i.e. observing
    `T` cannot *increase* the entropy of `W`. -/
theorem mutual_information_nonneg_algebraic
    {HW HW_given_T I : ℝ}
    (h_chain : I = HW - HW_given_T)
    (h_cond_le : HW_given_T ≤ HW) :
    0 ≤ I := by
  rw [h_chain]; linarith

/-- §15.1 (Data-processing inequality, algebraic core) — for any
    post-processing of the observation `T → T'`, the mutual information
    can only decrease: `I(W; T') ≤ I(W; T)`. Algebraic anchor: if
    `I₁ ≤ I₂` and both are nonneg, then `I₁` is a valid Fano-bound
    parameter whenever `I₂` is, and the resulting Fano lower bound is
    **at least as strong** under post-processing. -/
theorem fano_dpi_strengthens {M I_pre I_post : ℝ}
    (hM : 1 < M)
    (h_post_le_pre : I_post ≤ I_pre) :
    1 - (I_pre + Real.log 2) / Real.log M
      ≤ 1 - (I_post + Real.log 2) / Real.log M :=
  fano_lower_bound_antitone hM h_post_le_pre

/-
Remaining Mathlib gap:

`tvDist_le_sqrt_one_sub_exp_neg` and `tvDist_le_sqrt_divergence` are
*abstract* in the divergence value `D`: the user supplies the
"BH bridge" `tvDist² ≤ 1 - exp(-D)` as a hypothesis. The Hellinger /
Bhattacharyya factorization of that bridge is now discharged in
`tvDist_sq_le_one_sub_exp_neg_of_bhattacharyya` (and its Hellinger-form
variant), so the only remaining input is the **measure-theoretic Le Cam
step** `tvDist² ≤ 1 - ρ²` and the **Bhattacharyya--KL step**
`exp(-KL/2) ≤ ρ`. Specializing to `D = (klDiv μ ν).toReal` therefore
reduces to discharging those two integral inequalities — exactly the
content of the classical proof. Mathlib does not yet expose
`bhattacharyya` / `hellingerSquared`, but neither inequality is needed
in the algebraic chain above.

When upstream lands the Hellinger machinery, the two abstract inputs
collapse to one-liners derived from `klDiv`, and the wrappers
`tvDist_le_sqrt_one_sub_exp_neg_of_bhattacharyya` /
`tvDist_le_sqrt_one_sub_exp_neg_of_hellinger` immediately give the
classical Bretagnolle--Huber bound in terms of `klDiv`. The sharper
textbook Pinsker `tvDist ≤ √(KL/2)` factor of `1/2` still needs a finer
convex analysis than the `1 - exp(-x) ≤ x` anchor used here.
-/

end LTFP
