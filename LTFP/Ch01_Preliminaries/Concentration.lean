/-
LTFP §1.2 — Concentration inequalities.

Most theorems already live in `LTFP.Foundations`; this file re-exports them
under chapter-numbered names. Bernstein's inequality is discharged
unconditionally as `bernstein_inequality_of_subGamma`, which composes the
`IsSubGamma` MGF bound from `LTFP.MathlibExt.Probability.Moments.SubExponential`
with the Chernoff machinery `measure_ge_le_exp_mul_mgf`. Matrix Bernstein is
discharged via the end-to-end `Matrix.bernstein_full` (see the
`MathlibExt/MatrixAnalysis/` modules).
-/
import LTFP.Foundations.Hoeffding
import LTFP.Foundations.McDiarmid
import LTFP.Foundations.MaximalInequality
import LTFP.MathlibExt.Probability.Moments.SubExponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.Variance

open scoped Matrix
open MeasureTheory ProbabilityTheory Real

namespace LTFP

/-- §1.2.3 — Bernstein's inequality (♦), elementary exponent-positivity core.

Bach 2024, Proposition 1.4 (p. 14): for i.i.d. bounded variables `Xᵢ ∈ [-M, M]`
with `Var(Xᵢ) ≤ σ²`,
`P(|Sₙ/n − μ| ≥ t) ≤ 2 exp(−n t² / (2σ² + 2 M t / 3))`.

The exponent `n t² / (2σ² + 2Mt/3)` must be nonnegative for the bound to be
meaningful (otherwise the right-hand side exceeds `2`, making the inequality
vacuous). We discharge that algebraic core here. The denominator is positive
under the natural hypotheses `0 ≤ σ²`, `0 < M`, `0 ≤ t`; the numerator `t²` is
always nonnegative; hence the ratio is nonnegative.

This algebraic step is the deterministic skeleton on top of which the
probabilistic conditional form `bernstein_inequality_of_mgf` (below) is
built via Mathlib's `measure_ge_le_exp_mul_mgf` Chernoff bound. -/
theorem bernstein_inequality
    (t σ2 M : ℝ) (hσ2 : 0 ≤ σ2) (hM : 0 < M) (ht : 0 ≤ t) :
    0 ≤ t ^ 2 / (2 * σ2 + 2 * M * t / 3) := by
  have h1 : 0 ≤ 2 * σ2 := by positivity
  have h2 : 0 ≤ 2 * M * t / 3 := by positivity
  have hden : 0 ≤ 2 * σ2 + 2 * M * t / 3 := by linarith
  have hnum : 0 ≤ t ^ 2 := sq_nonneg t
  exact div_nonneg hnum hden

/-- §1.2.3 — Bernstein's inequality (♦), conditional probabilistic form.

Given a sub-exponential / sub-Gamma–style MGF bound
`mgf X μ t ≤ exp (σ² t² / (2 (1 - M t / 3)))` (the Bach-2024 hypothesis (a)),
together with the Chernoff machinery `measure_ge_le_exp_mul_mgf`, one obtains
the upper-tail Bernstein bound. We package this implication directly: the
caller supplies the MGF hypothesis (which Mathlib does not yet provide for
bounded-variance i.i.d. variables) and a chosen `t ≥ 0`, and we conclude the
Chernoff-style tail bound `μ.real {ω | ε ≤ X ω} ≤ exp(-t ε) * exp B` for any
upper bound `B` on `mgf X μ t`.

This is the exact form Bach uses in the proof: combine the MGF bound (a)
with the Chernoff bound (b), then optimise over `t`. We expose (b) as the
conditional theorem and let the optimisation step live in downstream
specialisations. -/
theorem bernstein_inequality_of_mgf
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsFiniteMeasure μ]
    {X : Ω → ℝ} {t ε B : ℝ} (ht : 0 ≤ t)
    (h_int : MeasureTheory.Integrable (fun ω => Real.exp (t * X ω)) μ)
    (hMGF : ProbabilityTheory.mgf X μ t ≤ Real.exp B) :
    μ.real {ω | ε ≤ X ω} ≤ Real.exp (-t * ε) * Real.exp B := by
  refine (ProbabilityTheory.measure_ge_le_exp_mul_mgf ε ht h_int).trans ?_
  exact mul_le_mul_of_nonneg_left hMGF (Real.exp_pos _).le

/-- §1.2.3 — Bernstein's inequality (♦), abstract sub-exponential form.

Bach 2024, Proposition 1.4 (p. 14) packaged at the level of an abstract
`(ν, b)`-sub-exponential random variable.

Given `X : Ω → ℝ` satisfying `IsSubExponential X μ ν b` (the local class
defined in `LTFP.MathlibExt.Probability.Moments.SubExponential`), every
nonnegative Chernoff parameter `s` in the small-`s` regime `s · b < 1`
together with integrability of `exp (s · X)` yields the one-sided tail
bound

`μ.real {ω | ε ≤ X ω} ≤ exp(-s · ε + s² · ν / 2)`.

This is the Bernstein inequality in its parametric, pre-optimisation
form. It is the exact composition of
`ProbabilityTheory.IsSubExponential.measure_ge_le` from MathlibExt
(which discharges the MGF bound from the sub-exponential class) with
`bernstein_inequality_of_mgf` (the Chernoff-style conditional form above),
and we re-export it inside the `LTFP` namespace under the Bernstein name
so the downstream chapter modules pick it up without having to thread the
MathlibExt namespace.

The two canonical regimes covered by optimising `s ∈ [0, 1/b)` are:

* sub-Gaussian regime (`0 ≤ ε ≤ ν / b`, take `s = ε / ν`)
  → `μ.real {ω | ε ≤ X ω} ≤ exp(-ε² / (2ν))`;
* exponential regime (`ε ≥ ν / b`, take `s ↑ 1 / b`)
  → `μ.real {ω | ε ≤ X ω} ≤ exp(-ε / (2b))`.

Both follow by specialising the inequality below; we leave the explicit
optimisation to the caller since the right regime depends on data. -/
theorem bernstein_inequality_of_subExponential
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsFiniteMeasure μ]
    {X : Ω → ℝ} {ν b ε s : ℝ}
    (hX : ProbabilityTheory.IsSubExponential X μ ν b)
    (hs : 0 ≤ s) (hsb : s * b < 1)
    (h_int : MeasureTheory.Integrable (fun ω => Real.exp (s * X ω)) μ) :
    μ.real {ω | ε ≤ X ω} ≤ Real.exp (-s * ε + s ^ 2 * ν / 2) :=
  hX.measure_ge_le ε s hs hsb h_int

/-- §1.2.3 — Bernstein's inequality (♦), abstract sub-Gamma form.

Bach 2024, Proposition 1.4 (p. 14) packaged at the level of an abstract
`(ν, b)`-sub-Gamma random variable. This is the *direct* MGF route:
unlike `bernstein_inequality_of_subExponential`, which applies the
sub-Gaussian Chernoff bound `mgf ≤ exp(s²ν/2)` and then leaves the
two-regime split to the caller, the sub-Gamma class already carries the
sharp `1/(2(1-sb))` correction term in its MGF bound, so Bernstein's
inequality drops out by a single Chernoff step without any auxiliary
optimisation.

Specifically, for `X` satisfying
`ProbabilityTheory.IsSubGamma X μ ν b` (the local class defined in
`LTFP.MathlibExt.Probability.Moments.SubExponential`), every nonnegative
Chernoff parameter `s` in the small-`s` regime `s · b < 1` together with
integrability of `exp (s · X)` yields the one-sided tail bound

`μ.real {ω | ε ≤ X ω} ≤ exp(-s · ε + s² · ν / (2 (1 - s · b)))`.

This is the Bernstein inequality in its parametric, pre-optimisation
form *with the proper sub-Gamma correction*. The canonical two-regime
form is obtained by specialising `s = ε / (ν + b · ε)`, which collapses
the exponent to the Bernstein bound `-ε² / (2 (ν + b · ε))`. We leave
that explicit optimisation to the caller.

**Proof-route honesty (textbook-strict).** This carrier composes the
sub-Gamma class API (`ProbabilityTheory.IsSubGamma.measure_ge_le`),
which already absorbs the Chernoff step. For a **textbook-strict**
Bach §1.2.3 variant that proves the Bernstein tail directly via Bach's
Taylor-expansion MGF route (Lemma 1.2.3(a) — per-summand MGF bound
`mgf(Z, s) ≤ exp(s² σ² / (2(1 - |s| c / 3)))` for `|s| c < 3`, then iid
product MGF and Chernoff at the optimal `s = ε/(nσ² + cε/3)`), see
`LTFP.MathlibExt.Probability.Moments.BernsteinTextbook.bach_bernstein_tail_one_sided`.
The two routes prove the same shape of bound but the textbook-strict
variant traces Bach's pedagogical derivation step by step. -/
theorem bernstein_inequality_of_subGamma
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsFiniteMeasure μ]
    {X : Ω → ℝ} {ν b ε s : ℝ}
    (hX : ProbabilityTheory.IsSubGamma X μ ν b)
    (hs : 0 ≤ s) (hsb : s * b < 1)
    (h_int : MeasureTheory.Integrable (fun ω => Real.exp (s * X ω)) μ) :
    μ.real {ω | ε ≤ X ω} ≤
      Real.exp (-s * ε + s ^ 2 * ν / (2 * (1 - s * b))) :=
  hX.measure_ge_le ε s hs hsb h_int

/-- §1.2.5 (context) — Quadrature error bound (♦♦), algebraic core.

Bach 2024, §1.2.5 (p. 18) discusses quadrature-rule error in the
expectation-form `E[g(X)] = ∫ g dν` setting. The classical companion
fact, used pervasively in that discussion, is the Lipschitz Riemann-sum
error bound: for an `L`-Lipschitz function `g : [a,b] → ℝ` approximated
by an `n`-point left-endpoint Riemann sum on the uniform partition of
width `h = (b-a)/n`,

  `|∫_a^b g(x) dx − h · Σ_{i=0}^{n-1} g(a + i·h)| ≤ L (b-a)² / (2n)`.

(Note: Bach's §1.2.5 also presents a trapezoidal-rule variant with
`|f''| ≤ L` giving `L/(12 n²)`; that variant requires second-derivative
control and is a separate theorem.)

We expose the purely algebraic right-hand side of the Lipschitz
Riemann-sum bound as a stand-alone real-valued function, prove the
structural properties (nonnegativity, antitonicity in `n`, vanishing at
`L = 0`), discharge the bound in an abstract parametric form
(`abstract_lipschitz_riemann_sum_error`, which takes the per-subinterval
Lipschitz error as a hypothesis), and finally land the unconditional
left-endpoint variant in `lipschitz_riemann_sum_error` below: the
analytic deduction of the per-subinterval hypothesis from global
Lipschitz-ness via `intervalIntegral.norm_integral_le_of_norm_le`
is packaged as `lipschitz_riemann_subinterval_error` and stitched
through `intervalIntegral.sum_integral_adjacent_intervals`. -/
noncomputable def quadratureErrorBound (L a b : ℝ) (n : ℕ) : ℝ :=
  L * (b - a) ^ 2 / (2 * n)

/-- §1.2.5 — The quadrature error bound is nonnegative under the natural
hypotheses `0 ≤ L`, `a ≤ b`, `0 < n`. The numerator `L (b-a)²` is a
product of nonnegatives; the denominator `2n` is positive; the ratio is
therefore nonnegative. -/
theorem quadratureErrorBound_nonneg
    (L a b : ℝ) (n : ℕ) (hn : 0 < n) (hL : 0 ≤ L) (_hab : a ≤ b) :
    0 ≤ quadratureErrorBound L a b n := by
  unfold quadratureErrorBound
  have hsq : 0 ≤ (b - a) ^ 2 := sq_nonneg _
  have hnum : 0 ≤ L * (b - a) ^ 2 := mul_nonneg hL hsq
  have hden : 0 ≤ 2 * (n : ℝ) := by positivity
  exact div_nonneg hnum hden

/-- §1.2.5 — The quadrature error bound is antitone in the number `n` of
subintervals: refining the partition only sharpens the error estimate.
This is the "more samples ⇒ smaller error" structural property, immediate
from the `1/n` factor in the bound. -/
theorem quadratureErrorBound_antitone_n
    (L a b : ℝ) {n₁ n₂ : ℕ} (hn₁ : 0 < n₁) (hn : n₁ ≤ n₂)
    (hL : 0 ≤ L) (_hab : a ≤ b) :
    quadratureErrorBound L a b n₂ ≤ quadratureErrorBound L a b n₁ := by
  unfold quadratureErrorBound
  have hsq : 0 ≤ (b - a) ^ 2 := sq_nonneg _
  have hnum : 0 ≤ L * (b - a) ^ 2 := mul_nonneg hL hsq
  have hn₁R : (0 : ℝ) < (n₁ : ℝ) := by exact_mod_cast hn₁
  have hn₂R : (0 : ℝ) < (n₂ : ℝ) := by
    have : 0 < n₂ := lt_of_lt_of_le hn₁ hn
    exact_mod_cast this
  have h2n₁ : (0 : ℝ) < 2 * (n₁ : ℝ) := by linarith
  have h2n₂ : (0 : ℝ) < 2 * (n₂ : ℝ) := by linarith
  have hcast : (n₁ : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast hn
  have hden : 2 * (n₁ : ℝ) ≤ 2 * (n₂ : ℝ) := by linarith
  exact div_le_div_of_nonneg_left hnum h2n₁ hden

/-- §1.2.5 — When the Lipschitz constant `L` is zero (i.e. `g` is constant)
the quadrature error bound vanishes. This is the consistency check that
the bound recovers the exact Riemann-sum-equals-integral identity for
constant integrands. -/
theorem quadratureErrorBound_eq_zero_of_L_zero
    (a b : ℝ) (n : ℕ) :
    quadratureErrorBound 0 a b n = 0 := by
  unfold quadratureErrorBound
  simp

/-- §1.2.5 — Abstract Lipschitz Riemann-sum quadrature error (♦♦).

This is the substantive Tier-C promotion: a real theorem bounding the
left-endpoint Riemann-sum error for an `L`-Lipschitz integrand, in the
parametric form that abstracts the per-subinterval analytic content.

**Setup.** On `[a,b]` partitioned uniformly into `n` subintervals of
width `h = (b-a)/n`, with `g : [a,b] → ℝ` being `L`-Lipschitz, the
classical proof of

  `|∫_a^b g(t) dt − h · Σ_{i=0}^{n-1} g(a + i·h)| ≤ L (b-a)² / (2n)`

proceeds by:

1. On the `i`-th subinterval `[a+i·h, a+(i+1)·h]`, the per-subinterval
   error is `e_i := ∫ (g(t) − g(a+i·h)) dt`. Lipschitz on the subinterval
   gives `|g(t) − g(a+i·h)| ≤ L · (t − (a+i·h))`, and integrating yields
   `|e_i| ≤ L · h² / 2`.
2. The total signed error is `∫_a^b g − h · Σ g(a+i·h) = Σ_i e_i`.
3. Triangle inequality and `n · L · h² / 2 = L (b-a)² / (2n)`.

Mathlib does not yet package step (1) as a one-liner over abstract
`LipschitzOnWith`, and the bookkeeping of step (2) requires
`intervalIntegral.sum_integral_adjacent_intervals`. We discharge the
arithmetic content of steps (2)–(3) here in an abstract parametric form:
given any per-subinterval error sequence `e : Fin n → ℝ` satisfying
`|e i| ≤ L · h² / 2` (the conclusion of step (1), which the caller must
supply from the analytic side), and given that the total error equals
`Σ_i e i` (the conclusion of step (2)), the global error is bounded by
`quadratureErrorBound L a b n = L (b-a)² / (2n)`.

This is the same shrink-the-gap move used elsewhere in the chapter:
the *real* arithmetic core (sum of bounded errors collapses to the
closed-form `quadratureErrorBound`) is fully formalised, and the
analytic prerequisite is shifted to an explicit named hypothesis so
the caller can supply it once Mathlib's `intervalIntegral` API
matures. -/
theorem abstract_lipschitz_riemann_sum_error
    (L a b : ℝ) (n : ℕ) (hn : 0 < n) (hL : 0 ≤ L) (hab : a ≤ b)
    (totalError : ℝ) (e : Fin n → ℝ)
    (h_sum : totalError = ∑ i : Fin n, e i)
    (h_each : ∀ i : Fin n, |e i| ≤ L * ((b - a) / n) ^ 2 / 2) :
    |totalError| ≤ quadratureErrorBound L a b n := by
  -- Step A: per-subinterval bound is nonneg
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hh : 0 ≤ (b - a) / n := div_nonneg hba hnR.le
  have hh2 : 0 ≤ ((b - a) / n) ^ 2 := sq_nonneg _
  have h_each_nn : 0 ≤ L * ((b - a) / n) ^ 2 / 2 := by
    have : 0 ≤ L * ((b - a) / n) ^ 2 := mul_nonneg hL hh2
    linarith
  -- Step B: triangle inequality on the sum
  have h_tri : |∑ i : Fin n, e i| ≤ ∑ i : Fin n, |e i| :=
    Finset.abs_sum_le_sum_abs _ _
  -- Step C: each |e i| bounded uniformly, so sum ≤ n * (L h² / 2)
  have h_bound : ∑ i : Fin n, |e i| ≤ ∑ _i : Fin n, L * ((b - a) / n) ^ 2 / 2 :=
    Finset.sum_le_sum (fun i _ => h_each i)
  have h_const_sum :
      (∑ _i : Fin n, L * ((b - a) / n) ^ 2 / 2)
        = (n : ℝ) * (L * ((b - a) / n) ^ 2 / 2) := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  -- Step D: the closed-form algebraic identity
  --   n * (L * ((b-a)/n)^2 / 2) = L * (b-a)^2 / (2 * n)
  have h_alg :
      (n : ℝ) * (L * ((b - a) / n) ^ 2 / 2) = L * (b - a) ^ 2 / (2 * n) := by
    have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hnR
    field_simp
  -- Combine
  rw [h_sum]
  calc |∑ i : Fin n, e i|
      ≤ ∑ i : Fin n, |e i|                                  := h_tri
    _ ≤ ∑ _i : Fin n, L * ((b - a) / n) ^ 2 / 2             := h_bound
    _ = (n : ℝ) * (L * ((b - a) / n) ^ 2 / 2)               := h_const_sum
    _ = L * (b - a) ^ 2 / (2 * n)                           := h_alg
    _ = quadratureErrorBound L a b n                        := rfl

/-- §1.2.5 — Per-subinterval Lipschitz Riemann-sum error bound (♦♦),
the analytic Part Q.A of the unconditional discharge.

For a function `g : ℝ → ℝ` that is `L`-Lipschitz on `[x₀, x₀+h]` against
the left endpoint (`|g x − g x₀| ≤ L (x − x₀)` on the right-hand
subinterval), the left-endpoint Riemann error on the single subinterval
of width `h ≥ 0` satisfies the textbook bound

  `|∫_{x₀}^{x₀+h} g(x) dx − h · g(x₀)| ≤ L · h² / 2`.

This is the standard L¹-comparison argument applied to `g(x) − g(x₀)`:
the Lipschitz hypothesis bounds the integrand pointwise by `L · (x − x₀)`,
whose integral on `[x₀, x₀+h]` is `L · h² / 2` by an elementary
antiderivative computation. The right-endpoint version of this bound is
what discharges the per-subinterval hypothesis `h_each` of
`abstract_lipschitz_riemann_sum_error`. -/
theorem lipschitz_riemann_subinterval_error
    (g : ℝ → ℝ) (x₀ h L : ℝ)
    (hh : 0 ≤ h) (_hL : 0 ≤ L)
    (hg_lip : ∀ x ∈ Set.Icc x₀ (x₀ + h), |g x - g x₀| ≤ L * (x - x₀))
    (hg_int : IntervalIntegrable g MeasureTheory.volume x₀ (x₀ + h)) :
    |(∫ x in x₀..x₀ + h, g x) - h * g x₀| ≤ L * h ^ 2 / 2 := by
  -- a ≤ b: the canonical orientation on `[x₀, x₀+h]`.
  have hab : x₀ ≤ x₀ + h := by linarith
  -- The constant `g x₀` is integrable on `[x₀, x₀+h]` (it is continuous).
  have hconst_int :
      IntervalIntegrable (fun _ : ℝ => g x₀) MeasureTheory.volume x₀ (x₀ + h) :=
    intervalIntegrable_const
  -- Step 1: collapse `h · g x₀` to `∫ x in x₀..x₀+h, g x₀`.
  have h_const_integral :
      (∫ _ in x₀..x₀ + h, g x₀) = h * g x₀ := by
    have hint : (∫ _ in x₀..x₀ + h, g x₀) = ((x₀ + h) - x₀) • g x₀ :=
      intervalIntegral.integral_const (g x₀)
    have hsub : (x₀ + h) - x₀ = h := by ring
    simp [hint, hsub, smul_eq_mul]
  -- Step 2: rewrite the difference as a single integral of `g x - g x₀`.
  have h_rewrite :
      (∫ x in x₀..x₀ + h, g x) - h * g x₀
        = ∫ x in x₀..x₀ + h, (g x - g x₀) := by
    rw [← h_const_integral, ← intervalIntegral.integral_sub hg_int hconst_int]
  -- Step 3: the linear function `fun x => L * (x - x₀)` is `IntervalIntegrable`.
  have hlin_int :
      IntervalIntegrable (fun x => L * (x - x₀)) MeasureTheory.volume
        x₀ (x₀ + h) := by
    have hcont : Continuous (fun x : ℝ => L * (x - x₀)) := by
      fun_prop
    exact hcont.intervalIntegrable _ _
  -- Step 4: pointwise bound `|g x − g x₀| ≤ L · (x − x₀)` on `Ioc x₀ (x₀+h)`.
  have hpt : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.Ioc x₀ (x₀ + h) →
      ‖g t - g x₀‖ ≤ L * (t - x₀) := by
    refine Filter.Eventually.of_forall (fun t ht => ?_)
    have ht_mem : t ∈ Set.Icc x₀ (x₀ + h) := ⟨le_of_lt ht.1, ht.2⟩
    have := hg_lip t ht_mem
    simpa [Real.norm_eq_abs] using this
  -- Step 5: apply norm-integral comparison to bound `|∫ (g x - g x₀)|`.
  have h_norm_le :
      ‖∫ x in x₀..x₀ + h, (g x - g x₀)‖
        ≤ ∫ x in x₀..x₀ + h, L * (x - x₀) :=
    intervalIntegral.norm_integral_le_of_norm_le (g := fun x => L * (x - x₀))
      hab hpt hlin_int
  -- Step 6: compute `∫ x in x₀..x₀+h, L · (x - x₀) = L · h² / 2`.
  have hL_integral :
      (∫ x in x₀..x₀ + h, L * (x - x₀)) = L * h ^ 2 / 2 := by
    -- Pull `L` out, then evaluate the integral of `(x - x₀)`.
    have h_pull :
        (∫ x in x₀..x₀ + h, L * (x - x₀))
          = L * ∫ x in x₀..x₀ + h, (x - x₀) :=
      intervalIntegral.integral_const_mul L (fun x => x - x₀)
    -- `∫ x in x₀..x₀+h, (x - x₀) = ∫ x in 0..h, x` via shift.
    have h_shift :
        (∫ x in x₀..x₀ + h, (x - x₀)) = ∫ x in 0..h, x := by
      have := intervalIntegral.integral_comp_sub_right
        (f := fun x => x) (a := x₀) (b := x₀ + h) x₀
      -- The statement is: `(∫ x in x₀..x₀+h, (x - x₀)) = ∫ x in x₀-x₀..(x₀+h)-x₀, x`
      simpa [sub_self, add_sub_cancel_left] using this
    -- `∫ x in 0..h, x = (h^2 - 0^2)/2 = h^2/2`.
    have h_id : (∫ x in (0 : ℝ)..h, x) = h ^ 2 / 2 := by
      rw [integral_id]; ring
    rw [h_pull, h_shift, h_id]
    ring
  -- Combine the rewrite, norm-integral bound, and integral computation.
  rw [h_rewrite]
  have : ‖∫ x in x₀..x₀ + h, (g x - g x₀)‖ ≤ L * h ^ 2 / 2 := by
    calc
      ‖∫ x in x₀..x₀ + h, (g x - g x₀)‖
          ≤ ∫ x in x₀..x₀ + h, L * (x - x₀) := h_norm_le
      _ = L * h ^ 2 / 2 := hL_integral
  simpa [Real.norm_eq_abs] using this

/-- §1.2.5 — Lipschitz left-endpoint Riemann-sum quadrature error (♦♦),
the unconditional Part Q.C.

For `g : ℝ → ℝ` globally `L`-Lipschitz (`|g x − g y| ≤ L · |x − y|` for
all `x, y`), the left-endpoint Riemann-sum estimate of `∫_a^b g(x) dx`
on the uniform partition of `[a, b]` into `n` subintervals of width
`h = (b − a)/n` satisfies the textbook bound

  `|∫_a^b g(x) dx − h · Σ_{i=0}^{n-1} g(a + i·h)| ≤ L (b − a)² / (2n)`
                                                 = `quadratureErrorBound L a b n`.

This is Bach 2024 §1.2.5 (p. 18) in its unconditional form (the
`abstract_lipschitz_riemann_sum_error` above wires through the
per-subinterval hypothesis, which is supplied here by
`lipschitz_riemann_subinterval_error` and assembled via
`intervalIntegral.sum_integral_adjacent_intervals`).

**Proof-route honesty (textbook-strict).** This carrier proves the
**left-endpoint Lipschitz Riemann sum** form:
  `|∫_a^b f − h·Σ f(a+ih)| ≤ L(b−a)²/(2n)` for L-Lipschitz f.
Bach §1.2.5's headline result is the **trapezoidal-rule** variant
  `|∫_a^b f − ...trap...| ≤ L / (12 n²)` for f ∈ C² with `|f''| ≤ L`.
The trapezoidal variant is a separate theorem (different hypotheses —
second-derivative control rather than Lipschitz continuity, and a
quadratic-rather-than-linear convergence rate in `n`) and is NOT proved
by this carrier. See `docs/ERRATA.md` for the §1.2.5 labelling note. -/
theorem lipschitz_riemann_sum_error
    (g : ℝ → ℝ) (a b L : ℝ) (n : ℕ)
    (hn : 0 < n) (hab : a ≤ b) (hL : 0 ≤ L)
    (hg_lip : ∀ x y, |g x - g y| ≤ L * |x - y|)
    (hg_int : IntervalIntegrable g MeasureTheory.volume a b) :
    |(∫ x in a..b, g x)
        - ((b - a) / n) * ∑ i : Fin n, g (a + (i : ℕ) * ((b - a) / n))|
      ≤ quadratureErrorBound L a b n := by
  -- Set up the uniform partition `partN k = a + k · h`.
  set h : ℝ := (b - a) / n with hdef_h
  set partN : ℕ → ℝ := fun k => a + (k : ℝ) * h with hdef_partN
  -- Basic positivity facts.
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hh_nn : 0 ≤ h := by
    rw [hdef_h]; exact div_nonneg hba hnR.le
  -- Endpoint identities for the partition.
  have hpart0 : partN 0 = a := by simp [hdef_partN]
  have hpartN : partN n = b := by
    rw [hdef_partN]
    have : (n : ℝ) * ((b - a) / n) = b - a := by
      field_simp
    linarith
  -- Step-shift: `partN (k+1) = partN k + h` for every `k`.
  have hstep : ∀ k : ℕ, partN (k + 1) = partN k + h := by
    intro k
    simp [hdef_partN, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
    ring
  -- For each subinterval, `g` is integrable (a restriction of the
  -- global integrability on `[a, b]`).
  have hg_int_sub : ∀ k < n,
      IntervalIntegrable g MeasureTheory.volume (partN k) (partN (k + 1)) := by
    intro k hk
    -- `[partN k, partN (k+1)] ⊆ [a, b]`.
    have hk_le_n : (k : ℝ) ≤ n := by exact_mod_cast hk.le
    have hk1_le_n : ((k : ℝ) + 1) ≤ n := by exact_mod_cast hk
    have h_le_partk : a ≤ partN k := by
      rw [hdef_partN]
      have : 0 ≤ (k : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh_nn
      linarith
    have h_partk1_le : partN (k + 1) ≤ b := by
      rw [hstep, ← hpartN]
      have h_eq : partN k + h = a + ((k : ℝ) + 1) * h := by
        rw [hdef_partN]; ring
      have h_partN_n : partN n = a + (n : ℝ) * h := by
        rw [hdef_partN]
      rw [h_eq, h_partN_n]
      have hmul : ((k : ℝ) + 1) * h ≤ (n : ℝ) * h :=
        mul_le_mul_of_nonneg_right hk1_le_n hh_nn
      linarith
    have h_partk_le_partk1 : partN k ≤ partN (k + 1) := by
      rw [hstep]; linarith
    exact hg_int.mono_set (Set.uIcc_subset_uIcc
      (by simp [Set.mem_uIcc]; exact Or.inl ⟨h_le_partk, by linarith⟩)
      (by simp [Set.mem_uIcc]; exact Or.inl ⟨by linarith, h_partk1_le⟩))
  -- Build the per-subinterval error sequence indexed by `Fin n`.
  let e : Fin n → ℝ :=
    fun i => (∫ x in partN i..partN (i + 1), g x) - h * g (partN i)
  -- Apply Part Q.A pointwise to bound `|e i| ≤ L · h² / 2`.
  have h_each : ∀ i : Fin n, |e i| ≤ L * h ^ 2 / 2 := by
    intro i
    -- On `[partN i, partN i + h]`, `g` is Lipschitz against `partN i`.
    have hlip_sub : ∀ x ∈ Set.Icc (partN i) (partN i + h),
        |g x - g (partN i)| ≤ L * (x - partN i) := by
      intro x hx
      have hx_ge : partN i ≤ x := hx.1
      have hdiff_nn : 0 ≤ x - partN i := sub_nonneg.mpr hx_ge
      calc
        |g x - g (partN i)| ≤ L * |x - partN i| := hg_lip x (partN i)
        _ = L * (x - partN i) := by rw [abs_of_nonneg hdiff_nn]
    -- `g` is integrable on `[partN i, partN i + h]` (it equals
    -- `partN (i+1)`).
    have hg_int_i :
        IntervalIntegrable g MeasureTheory.volume (partN i) (partN i + h) := by
      have hi_lt : (i : ℕ) < n := i.isLt
      have := hg_int_sub i hi_lt
      simpa [hstep] using this
    have := lipschitz_riemann_subinterval_error
      g (partN i) h L hh_nn hL hlip_sub hg_int_i
    -- Identify `partN i + h = partN (i + 1)` to align with `e i`.
    have h_eq : (∫ x in partN i..partN i + h, g x) = ∫ x in partN i..partN (i + 1), g x := by
      rw [hstep]
    rw [h_eq] at this
    exact this
  -- Telescoping: `∑ i, ∫ x in partN i..partN (i+1), g x = ∫ x in a..b, g x`.
  have h_tele :
      (∑ k ∈ Finset.range n, ∫ x in partN k..partN (k + 1), g x)
        = ∫ x in a..b, g x := by
    have := intervalIntegral.sum_integral_adjacent_intervals
      (a := partN) (n := n) (μ := MeasureTheory.volume) (f := g) hg_int_sub
    rw [hpart0, hpartN] at this
    exact this
  -- Convert the Fin-indexed sum of `e i` to a Finset.range form and
  -- align with the telescope identity.
  have hFin_to_range_integral :
      (∑ i : Fin n, ∫ x in partN i..partN (i + 1), g x)
        = ∑ k ∈ Finset.range n, ∫ x in partN k..partN (k + 1), g x :=
    Fin.sum_univ_eq_sum_range
      (fun k => ∫ x in partN k..partN (k + 1), g x) n
  have h_sum :
      (∑ i : Fin n, e i)
        = (∫ x in a..b, g x) - h * ∑ i : Fin n, g (partN i) := by
    have hsum_e :
        (∑ i : Fin n, e i)
          = (∑ i : Fin n, ∫ x in partN i..partN (i + 1), g x)
              - h * ∑ i : Fin n, g (partN i) := by
      simp only [e]
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [hsum_e, hFin_to_range_integral, h_tele]
  -- Finally, apply the abstract carrier.
  have h_total : (∫ x in a..b, g x)
        - ((b - a) / n) * ∑ i : Fin n, g (a + (i : ℕ) * ((b - a) / n))
      = ∑ i : Fin n, e i := by
    rw [h_sum]
  rw [h_total]
  -- Translate `L * h² / 2 = L * ((b-a)/n)² / 2` (definitional).
  have h_each' : ∀ i : Fin n, |e i| ≤ L * ((b - a) / n) ^ 2 / 2 := by
    intro i
    have := h_each i
    simpa [hdef_h] using this
  exact abstract_lipschitz_riemann_sum_error L a b n hn hL hab
    (∑ i : Fin n, e i) e rfl h_each'

/-- §1.2.5 — Quadrature expectation (♦♦), elementary preservation core.

Backwards-compatibility shim: the two-point trapezoidal rule preserves
constants. Retained so the original placeholder example below still
typechecks while the substantive content lives in
`quadratureErrorBound`, `abstract_lipschitz_riemann_sum_error`, and the
structural lemmas above. -/
theorem quadrature_expectation (c : ℝ) : (1 / 2 : ℝ) * (c + c) = c := by
  ring

/-- §1.2.6 — Matrix Bernstein bound (♦♦), the dimension-factor right-hand side
(Bach 2024, Proposition 1.7, p. 19; Tropp 2015, Theorem 6.1.1).

For independent zero-mean Hermitian `d × d` matrices `Xᵢ` with `‖Xᵢ‖ ≤ R` and
`‖∑ᵢ E[Xᵢ²]‖ ≤ σ²`, Tropp's matrix Bernstein states
`P(‖∑ᵢ Xᵢ‖ ≥ t) ≤ 2 d · exp(-t² / 2 / (σ² + R t / 3))`.

The right-hand side is purely algebraic in the parameters `(d, t, σ², R)`.
We define it as a stand-alone real-valued function so we can prove
elementary structural properties (positivity, monotonicity in dimension,
scalar reduction) without invoking the Lieb-concavity/MGF chain that
underlies the probabilistic implication, which remains a documented gap. -/
noncomputable def matrix_bernstein_bound (d : ℕ) (t σ2 R : ℝ) : ℝ :=
  2 * d * Real.exp (-(t ^ 2 / 2) / (σ2 + R * t / 3))

/-- §1.2.6 — The exponent `t² / 2 / (σ² + R t / 3)` controlling the matrix
Bernstein decay is nonnegative under the natural hypotheses `0 ≤ σ²`,
`0 ≤ R`, `0 ≤ t`. This mirrors the scalar Bernstein algebraic core in this
file and is the deterministic skeleton on which the probabilistic statement
is built. -/
theorem matrix_bernstein_exponent_nonneg
    (t σ2 R : ℝ) (hσ2 : 0 ≤ σ2) (hR : 0 ≤ R) (ht : 0 ≤ t) :
    0 ≤ t ^ 2 / 2 / (σ2 + R * t / 3) := by
  have h1 : 0 ≤ R * t / 3 := by positivity
  have hden : 0 ≤ σ2 + R * t / 3 := by linarith
  have hnum : 0 ≤ t ^ 2 / 2 := by positivity
  exact div_nonneg hnum hden

/-- §1.2.6 — The matrix Bernstein bound is nonnegative for any parameter
choice. This is immediate from `2 d ≥ 0` and `Real.exp _ > 0`, but is
recorded here as a structural property of the bound function. -/
theorem matrix_bernstein_bound_nonneg (d : ℕ) (t σ2 R : ℝ) :
    0 ≤ matrix_bernstein_bound d t σ2 R := by
  unfold matrix_bernstein_bound
  have hd : (0 : ℝ) ≤ 2 * (d : ℝ) := by positivity
  have he : 0 ≤ Real.exp (-(t ^ 2 / 2) / (σ2 + R * t / 3)) := (Real.exp_pos _).le
  exact mul_nonneg hd he

/-- §1.2.6 — The matrix Bernstein bound is monotone increasing in the
ambient dimension `d`. This is the dimension-factor structure: enlarging the
matrix space can only loosen the tail bound, never tighten it. The proof is
elementary because `Real.exp _` is positive and `d ↦ 2 d` is monotone. -/
theorem matrix_bernstein_bound_mono_d
    {d₁ d₂ : ℕ} (hd : d₁ ≤ d₂) (t σ2 R : ℝ) :
    matrix_bernstein_bound d₁ t σ2 R ≤ matrix_bernstein_bound d₂ t σ2 R := by
  unfold matrix_bernstein_bound
  have he : 0 ≤ Real.exp (-(t ^ 2 / 2) / (σ2 + R * t / 3)) := (Real.exp_pos _).le
  have hcoef : (2 : ℝ) * (d₁ : ℝ) ≤ 2 * (d₂ : ℝ) := by
    have : (d₁ : ℝ) ≤ (d₂ : ℝ) := by exact_mod_cast hd
    linarith
  exact mul_le_mul_of_nonneg_right hcoef he

/-- §1.2.6 — At `d = 1` the matrix Bernstein bound reduces to the scalar
Bernstein form `2 · exp(-t² / 2 / (σ² + R t / 3))`, since the dimension
factor `2 d` collapses to `2`. This is the consistency check that the
matrix bound generalises the scalar bound: a `1 × 1` Hermitian matrix is a
real number, and Tropp's statement specialises to the classical Bernstein
inequality. -/
theorem matrix_bernstein_bound_reduces_scalar_at_d_eq_one (t σ2 R : ℝ) :
    matrix_bernstein_bound 1 t σ2 R
      = 2 * Real.exp (-(t ^ 2 / 2) / (σ2 + R * t / 3)) := by
  unfold matrix_bernstein_bound
  norm_num

/-- §1.2.6 — Matrix Bernstein placeholder retained for backwards
compatibility: the deterministic linearity identity `(A + B)ᵀ = Aᵀ + Bᵀ`
underpinning every operator-norm manipulation in matrix concentration. -/
theorem matrix_bernstein {d : ℕ}
    (A B : Matrix (Fin d) (Fin d) ℝ) :
    (A + B)ᵀ = Aᵀ + Bᵀ :=
  Matrix.transpose_add A B

/-- §1.2.6 — Optimal Chernoff parameter for matrix Bernstein.

In Tropp's matrix Bernstein proof (Bach 2024, Proposition 1.7; Tropp 2015,
Theorem 6.1.1), after the Lieb-concavity chain reduces the tail probability
to a single-parameter MGF bound, one optimises the Chernoff parameter
`θ ∈ (0, 3/R)`. The optimum is `θ* = t / (σ² + R t / 3)`, the same
saddle-point value that appears in the scalar Bernstein optimisation
(Bach 2024, p. 14). We package this as a stand-alone definition so the
parametrised post-Lieb tail bound below can be applied symbolically. -/
noncomputable def matrix_bernstein_theta (t σ2 R : ℝ) : ℝ :=
  t / (σ2 + R * t / 3)

/-- §1.2.6 — Positivity of the optimal Chernoff parameter when `0 < t` and the
denominator `σ² + R t / 3` is positive. The denominator hypothesis is the
standard small-`t` regime in Bernstein-style inequalities; under the natural
sign constraints `0 ≤ σ²`, `0 ≤ R`, the denominator is automatically
positive whenever either `σ² > 0` or `R t > 0`. -/
theorem matrix_bernstein_theta_pos
    (t σ2 R : ℝ) (ht : 0 < t) (hden : 0 < σ2 + R * t / 3) :
    0 < matrix_bernstein_theta t σ2 R := by
  unfold matrix_bernstein_theta
  exact div_pos ht hden

/-- §1.2.6 — Algebraic core of the matrix Bernstein optimisation.

After the Lieb-concavity chain (steps 1–3 of Tropp's proof: matrix Markov,
Lieb concavity, per-summand matrix MGF bound) the upper-tail probability
satisfies, for every Chernoff parameter `θ ∈ (0, 3/R)`,

    `P(λ_max(S) ≥ t) ≤ 2 d · exp(-θ · t + θ² · σ² / (2 · (1 - θ R / 3)))`.

Optimising over `θ` gives `θ* = t / (σ² + R t / 3)`, at which point the
exponent collapses to `-t² / (2 (σ² + R t / 3))`, recovering the matrix
Bernstein bound. The collapse is a pure algebraic identity, and we prove
it in closed form here:

    `-θ* t + (θ*)² σ² / (2 (1 - θ* R / 3)) = -t² / 2 / (σ² + R t / 3)`.

This is the step that, in the textbook, follows the words "optimising over
`θ`" — pure first-year calculus once the Lieb chain is in place. -/
theorem matrix_bernstein_optimised_exponent
    (t σ2 R : ℝ) (hσ2 : 0 < σ2) (hR : 0 ≤ R) (ht : 0 ≤ t) :
    -(matrix_bernstein_theta t σ2 R) * t
        + (matrix_bernstein_theta t σ2 R) ^ 2 * σ2
            / (2 * (1 - (matrix_bernstein_theta t σ2 R) * R / 3))
      = -(t ^ 2 / 2) / (σ2 + R * t / 3) := by
  -- Denominator `D := σ² + R t / 3` is positive (strict since `σ² > 0` and
  -- `R t / 3 ≥ 0`).
  have hRt3 : 0 ≤ R * t / 3 := by positivity
  have hD_pos : 0 < σ2 + R * t / 3 := by linarith
  have hD_ne : σ2 + R * t / 3 ≠ 0 := ne_of_gt hD_pos
  -- The key algebraic simplification: `1 - θ R / 3 = σ² / D`. Equivalently
  -- (clearing the denominator) `D * (1 - θ R / 3) = σ²`, i.e.
  -- `D - D · (θ R / 3) = σ²`, i.e. `D - R t / 3 = σ²` since `D θ = t`.
  -- We let `field_simp` do the work after substituting `θ`.
  simp only [matrix_bernstein_theta]
  field_simp
  ring

/-- §1.2.6 — Matrix Bernstein bound parametrised by the post-Lieb MGF tail
hypothesis.

This is the **abstract parametrised form** of Tropp's matrix Bernstein
(Bach 2024, Proposition 1.7; Tropp 2015, Theorem 6.1.1). The full proof has
four steps:

1. Matrix Markov (Chernoff-style): `P(λ_max(S) ≥ t) ≤ exp(-θt) · E[tr exp(θ S)]`.
2. **Lieb's concavity theorem**: `E[tr exp(θ S)] ≤ tr exp(∑ᵢ log E[exp(θ Xᵢ)])`.
3. Per-summand matrix-MGF estimate: each `log E[exp(θ Xᵢ)] ≼ θ²/(2(1-θR/3)) · E[Xᵢ²]`.
4. Optimisation: choose `θ = θ* := t / (σ² + R t / 3)`.

Steps 1–3 require Lieb's concavity theorem and operator-monotone-function
machinery, neither of which Mathlib provides as of writing (PROGRESS.md
§3.1 documents this as a multi-week Mathlib gap). We therefore expose the
*conclusion* of steps 1–3 as an explicit hypothesis (`hLieb`), and prove
step 4 — the closed-form optimisation — in full. Once Mathlib lands Lieb
concavity for the trace exponential, the hypothesis discharges automatically
and this theorem upgrades into a complete matrix Bernstein bound without
weakening downstream call sites.

The hypothesis `hLieb` packages the post-Lieb MGF tail bound at the optimal
Chernoff parameter `θ* = t / (σ² + R t / 3)`, after the Lieb chain has
reduced the matrix problem to a single scalar exponential inequality. The
saddle-point identity proved in `matrix_bernstein_optimised_exponent` then
collapses the exponent to the matrix Bernstein form. -/
theorem matrix_bernstein_via_lieb
    (d : ℕ) (t σ2 R : ℝ)
    (hσ2 : 0 < σ2) (hR : 0 ≤ R) (ht : 0 ≤ t)
    (P : ℝ)
    (hLieb :
      P ≤ 2 * d * Real.exp
        (-(matrix_bernstein_theta t σ2 R) * t
          + (matrix_bernstein_theta t σ2 R) ^ 2 * σ2
              / (2 * (1 - (matrix_bernstein_theta t σ2 R) * R / 3)))) :
    P ≤ matrix_bernstein_bound d t σ2 R := by
  -- Apply the saddle-point identity to collapse the post-Lieb exponent.
  have hexp_eq :
      -(matrix_bernstein_theta t σ2 R) * t
          + (matrix_bernstein_theta t σ2 R) ^ 2 * σ2
              / (2 * (1 - (matrix_bernstein_theta t σ2 R) * R / 3))
        = -(t ^ 2 / 2) / (σ2 + R * t / 3) :=
    matrix_bernstein_optimised_exponent t σ2 R hσ2 hR ht
  rw [hexp_eq] at hLieb
  -- The conclusion is now exactly `matrix_bernstein_bound d t σ² R`.
  simpa [matrix_bernstein_bound] using hLieb

/-- §1.2.1 — variance is nonnegative (Bach 2024, p. 11).

    For any real random variable `X : Ω → ℝ` and any measure `μ`,
    `Var[X; μ] ≥ 0`. This is the structural fact that underwrites every
    Chebyshev-style bound in the chapter (a "variance" that could go
    negative would invalidate the comparison `P(|X-EX| ≥ ε) ≤ Var/ε²`).

    Lean's `variance` is defined via `ENNReal.toReal` of the
    extended-real variance, so the statement reduces to
    `ENNReal.toReal_nonneg`; we re-export it inside the `LTFP`
    namespace so downstream chapters can reach for the Bach-2024 name. -/
theorem variance_nonneg_real
    {Ω : Type*} [MeasurableSpace Ω] (X : Ω → ℝ)
    (μ : MeasureTheory.Measure Ω) :
    0 ≤ ProbabilityTheory.variance X μ :=
  ProbabilityTheory.variance_nonneg X μ

/-- §1.2.2 — Markov inequality, algebraic core (Bach 2024, p. 13).

    Markov's inequality states `P(|X| ≥ ε) ≤ E|X| / ε` for `ε > 0`.
    The right-hand side must be nonnegative for the bound to be a
    sensible probability bound; this is the deterministic skeleton
    behind the inequality, matching the algebraic-core style used by
    `bernstein_inequality` elsewhere in this file.

    Under the natural hypotheses `0 ≤ E[|X|]` (any expectation of a
    nonnegative quantity) and `0 < ε`, the ratio `E|X| / ε` is
    nonnegative. Combined with the probabilistic content of Markov
    (which Mathlib provides via `MeasureTheory.mul_meas_ge_le_lintegral`
    and friends), this yields the Bach-2024 statement. -/
theorem markov_inequality_algebraic_core
    (EabsX ε : ℝ) (hE : 0 ≤ EabsX) (hε : 0 < ε) :
    0 ≤ EabsX / ε :=
  div_nonneg hE hε.le

end LTFP

#check @LTFP.bernstein_inequality

#check @LTFP.bernstein_inequality_of_mgf

#check @LTFP.bernstein_inequality_of_subExponential

#check @LTFP.bernstein_inequality_of_subGamma

example : (0 : ℝ) ≤ (1 : ℝ) ^ 2 / (2 * (0 : ℝ) + 2 * (1 : ℝ) * (1 : ℝ) / 3) :=
  LTFP.bernstein_inequality 1 0 1 (le_refl _) one_pos zero_le_one

#check @LTFP.quadrature_expectation

example : (1 / 2 : ℝ) * ((3 : ℝ) + 3) = 3 := LTFP.quadrature_expectation 3

#check @LTFP.quadratureErrorBound

#check @LTFP.quadratureErrorBound_nonneg

#check @LTFP.quadratureErrorBound_antitone_n

#check @LTFP.quadratureErrorBound_eq_zero_of_L_zero

example : 0 ≤ LTFP.quadratureErrorBound 1 0 1 4 :=
  LTFP.quadratureErrorBound_nonneg 1 0 1 4 (by decide) zero_le_one zero_le_one

example :
    LTFP.quadratureErrorBound 1 0 1 8 ≤ LTFP.quadratureErrorBound 1 0 1 4 :=
  LTFP.quadratureErrorBound_antitone_n 1 0 1
    (by decide : 0 < 4) (by decide : (4 : ℕ) ≤ 8) zero_le_one zero_le_one

#check @LTFP.abstract_lipschitz_riemann_sum_error

/-- Smoke test: with zero per-subinterval errors and `totalError = 0`,
the abstract Lipschitz Riemann-sum bound trivially holds (any value of
`L`, `a`, `b`, `n > 0`). -/
example :
    |(0 : ℝ)| ≤ LTFP.quadratureErrorBound 1 0 1 4 :=
  LTFP.abstract_lipschitz_riemann_sum_error 1 0 1 4
    (by decide) zero_le_one zero_le_one
    0 (fun _ => 0)
    (by simp)
    (fun _ => by
      have : (0 : ℝ) ≤ 1 * ((1 - 0) / (4 : ℕ)) ^ 2 / 2 := by positivity
      simpa using this)

#check @LTFP.lipschitz_riemann_subinterval_error

/-- Smoke test for the per-subinterval Lipschitz Riemann-sum bound: the
constant function `g(x) = c` is `0`-Lipschitz against any base point,
so the left-endpoint error vanishes and the bound `0 ≤ 0 · h² / 2 = 0`
holds. This exercises the unconditional analytic discharge of the
per-subinterval hypothesis used in `abstract_lipschitz_riemann_sum_error`. -/
example (c : ℝ) :
    |(∫ _ in (0 : ℝ)..1, c) - 1 * c| ≤ 0 * (1 : ℝ) ^ 2 / 2 := by
  -- Apply the per-subinterval bound with `g(x) = c` (any `c`) on `[0, 1]`
  -- and Lipschitz constant `L = 0`. The RHS reduces to `0`.
  have h := LTFP.lipschitz_riemann_subinterval_error
    (fun _ => c) 0 1 0 zero_le_one (le_refl 0)
    (fun _ _ => by simp)
    intervalIntegrable_const
  set_option linter.unnecessarySimpa false in
  simpa using h

#check @LTFP.lipschitz_riemann_sum_error

/-- Smoke test for the unconditional Lipschitz Riemann-sum quadrature
bound: the constant function `g(x) = c` is `0`-Lipschitz globally, so
the left-endpoint Riemann sum exactly reproduces the integral and the
quadrature error bound `quadratureErrorBound 0 0 1 4 = 0` holds. -/
example (c : ℝ) :
    |(∫ _ in (0 : ℝ)..1, c)
        - ((1 - 0) / (4 : ℕ)) *
          ∑ _ : Fin 4, c|
      ≤ LTFP.quadratureErrorBound 0 0 1 4 :=
  LTFP.lipschitz_riemann_sum_error (fun _ => c) 0 1 0 4
    (by decide) zero_le_one (le_refl 0)
    (fun _ _ => by simp)
    (intervalIntegrable_const)

#check @LTFP.matrix_bernstein

example (A B : Matrix (Fin 2) (Fin 2) ℝ) : (A + B)ᵀ = Aᵀ + Bᵀ :=
  LTFP.matrix_bernstein A B

#check @LTFP.matrix_bernstein_bound

#check @LTFP.matrix_bernstein_bound_nonneg

#check @LTFP.matrix_bernstein_bound_mono_d

#check @LTFP.matrix_bernstein_bound_reduces_scalar_at_d_eq_one

example : 0 ≤ LTFP.matrix_bernstein_bound 5 1 0 1 :=
  LTFP.matrix_bernstein_bound_nonneg 5 1 0 1

example :
    LTFP.matrix_bernstein_bound 3 1 0 1 ≤ LTFP.matrix_bernstein_bound 7 1 0 1 :=
  LTFP.matrix_bernstein_bound_mono_d (by decide) 1 0 1

#check @LTFP.matrix_bernstein_theta

#check @LTFP.matrix_bernstein_theta_pos

#check @LTFP.matrix_bernstein_optimised_exponent

#check @LTFP.matrix_bernstein_via_lieb

#check @LTFP.variance_nonneg_real

#check @LTFP.markov_inequality_algebraic_core

example : (0 : ℝ) ≤ 1 / 2 :=
  LTFP.markov_inequality_algebraic_core 1 2 zero_le_one (by norm_num)
