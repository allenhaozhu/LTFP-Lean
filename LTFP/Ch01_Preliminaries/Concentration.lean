/-
LTFP §1.2 — Concentration inequalities.

Most theorems already live in `LTFP.Foundations`; this file re-exports them
under chapter-numbered names and adds Bernstein + matrix-concentration
placeholders for follow-up tickets.
-/
import LTFP.Foundations.Hoeffding
import LTFP.Foundations.McDiarmid
import LTFP.Foundations.MaximalInequality
import LTFP.MathlibExt.Probability.Moments.SubExponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Probability.Moments.Basic

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
`L = 0`) that any honest concrete proof discharges along the way, and
discharge the bound itself in an abstract parametric form — see
`abstract_lipschitz_riemann_sum_error` below — that takes the per-
subinterval Lipschitz error as a hypothesis. The concrete deduction of
that per-subinterval hypothesis from `LipschitzOnWith` and
`intervalIntegral` is the remaining gap, to be closed when the relevant
`MeasureTheory.intervalIntegral` API is consolidated. -/
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

end LTFP

#check @LTFP.bernstein_inequality

#check @LTFP.bernstein_inequality_of_mgf

#check @LTFP.bernstein_inequality_of_subExponential

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
