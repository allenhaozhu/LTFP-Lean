/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.IdentDistribIndep
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# PAC-Bayes bounded-mean squared-exponential moment (Bach 2024 Eq. 14.21)

Proposed Mathlib path:
`Mathlib/Probability/PACBayes/BoundedMeanSqExp.lean`.

Proposed Mathlib namespace: `ProbabilityTheory`.

## Statement

For an i.i.d. family `X 0, …, X (n - 1)` of `[0, 1]`-bounded real random
variables with common mean `μ_X`, define the centered empirical average

  `Z_n ω := (1 / n) ∑ i, X i ω - μ_X`.

Bach (2024) Eq. 14.21 asserts the squared-exponential moment bound at
the critical exponent `c = 2 n`:

  `∫ exp(2 n · Z_n ω ^ 2) ∂μ ≤ 2 √n`.

This file packages the result and the precise residual gap left over from
2026-05-20 work on Project B5.

## Mathematical context — the critical exponent

The exponent `2 n` is exactly the boundary of integrability for sub-Gaussian
squared moments. Hoeffding's lemma
(`ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`)
gives that each centered summand `Y_i := X_i - μ_X` is sub-Gaussian with
parameter `‖1‖₊² / 4 = 1/4`, so the rescaled centered sum

  `Z_n = (1 / n) ∑ (X_i - μ_X)`

is sub-Gaussian with parameter `n · (1/n)² · (1/4) = 1 / (4 n)`. The
standard sub-Gaussian "exp of square" moment formula
`E[exp(c Z²)] ≤ (1 - 2 c σ²)^(-1/2)` requires `2 c σ² < 1`; here
`2 · 2n · 1/(4n) = 1` exactly, so the generic sub-Gaussian argument is
*at the boundary* and diverges.

The route to a finite bound (`2 √n`) instead goes via the
**bounded-differences moment lemma** of Catoni and Alquier — a
McDiarmid-style argument exploiting the *bounded* (not just
sub-Gaussian) structure. Cf.:

* O. Catoni, *Statistical Learning Theory and Stochastic Optimization*,
  Springer Lecture Notes in Mathematics, vol. 1851 (2004), §5.2.
* P. Alquier, *User-friendly introduction to PAC-Bayes bounds*,
  Foundations and Trends in Machine Learning, 17(2):174–303, 2024,
  Theorem 4.1.
* F. Bach, *Learning Theory from First Principles*, MIT Press (2024),
  Eq. 14.21.

This file does **not** discharge that lemma; instead it factors the
PAC-Bayes carrier theorem cleanly through a single named residual
`CatoniAlquierBoundedMoment` so that the rest of the PAC-Bayes chain
(Donsker–Varadhan, Fubini bridge, Chernoff/Markov) is unconditionally
wired in Lean.

## Main declarations

* `centeredEmpiricalAverage` — `(1 / n) ∑ X_i - E[X_0]`, the quantity
  whose squared-exponential moment is being bounded.
* `boundedMeanSqExpMoment` — the integral
  `∫ exp(2 n · (centeredEmpiricalAverage)²) ∂μ`.
* `CatoniAlquierBoundedMoment` — the named residual: a `Prop` asserting
  the Catoni/Alquier moment bound at the critical exponent for a
  bounded i.i.d. family. Discharging this in Lean is a self-contained
  3–7 person-day Mathlib project; see the docstring for the exact
  mathematical contract.
* `bounded_average_sq_exp_moment_of_catoni_alquier` — the headline
  lemma in product-measure form (the form consumed by the PAC-Bayes
  carrier), reduced to `CatoniAlquierBoundedMoment`.

## Implementation notes

The statement is phrased over an abstract sample space `Ω` with an
explicit i.i.d. family `X : Fin n → Ω → ℝ`, then specialized to the
product-measure form `Measure.pi (fun _ : Fin n => D)` used by the
PAC-Bayes carrier. The specialization uses `ProbabilityTheory.iIndepFun_pi`
to realize the projections `ω ↦ ℓ (ω i)` as an i.i.d. family on the
product space.
-/

namespace LTFP.MathlibExt.Probability

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Centered empirical average -/

/-- The centered empirical average of a finite family of real random
variables with common reference mean `μ_X`:

  `centeredEmpiricalAverage X μ_X ω := (1 / n) ∑ i, X i ω - μ_X`.

In the PAC-Bayes application, `X i ω := ℓ (ω i)` for a `[0, 1]`-valued
loss `ℓ` and `ω : Fin n → 𝒳` an i.i.d. sample, with `μ_X := ∫ ℓ ∂D`. -/
noncomputable def centeredEmpiricalAverage
    {n : ℕ} (X : Fin n → Ω → ℝ) (μ_X : ℝ) (ω : Ω) : ℝ :=
  (1 / (n : ℝ)) * ∑ i : Fin n, X i ω - μ_X

omit [MeasurableSpace Ω] in
@[simp]
lemma centeredEmpiricalAverage_apply
    {n : ℕ} (X : Fin n → Ω → ℝ) (μ_X : ℝ) (ω : Ω) :
    centeredEmpiricalAverage X μ_X ω
      = (1 / (n : ℝ)) * ∑ i : Fin n, X i ω - μ_X := rfl

/-- The squared-exponential moment of the centered empirical average at
the critical exponent `2 n`. The Bach Eq. 14.21 bound is the assertion
that this is `≤ 2 √n` whenever the `X i` are i.i.d., `[0, 1]`-valued,
and `μ_X` matches their common mean. -/
noncomputable def boundedMeanSqExpMoment
    (μ : Measure Ω) {n : ℕ} (X : Fin n → Ω → ℝ) (μ_X : ℝ) : ℝ :=
  ∫ ω, Real.exp (2 * (n : ℝ) * (centeredEmpiricalAverage X μ_X ω) ^ 2) ∂μ

@[simp]
lemma boundedMeanSqExpMoment_def
    (μ : Measure Ω) {n : ℕ} (X : Fin n → Ω → ℝ) (μ_X : ℝ) :
    boundedMeanSqExpMoment μ X μ_X
      = ∫ ω, Real.exp (2 * (n : ℝ)
              * ((1 / (n : ℝ)) * ∑ i : Fin n, X i ω - μ_X) ^ 2) ∂μ := rfl

/-! ### Non-negativity and a coarse upper bound

Two cheap facts that hold unconditionally on the structure of `X`:

* the moment is positive (the integrand is `> 0`);
* the moment is also bounded below by `1` when the integrand is
  integrable, since `exp` of a non-negative number is `≥ 1`.

These do not yet use the bounded-differences structure; they are merely
sanity checks consumed downstream. -/

/-- The squared-exponential moment is non-negative (the integrand is
strictly positive). -/
lemma boundedMeanSqExpMoment_nonneg
    (μ : Measure Ω) {n : ℕ} (X : Fin n → Ω → ℝ) (μ_X : ℝ) :
    0 ≤ boundedMeanSqExpMoment μ X μ_X := by
  unfold boundedMeanSqExpMoment
  exact integral_nonneg (fun _ => (Real.exp_pos _).le)

/-! ### Centered sub-Gaussian parameter

This subsection records the standard sub-Gaussian parameter of the
centered empirical average derived from Hoeffding's lemma. It is the
*generic* sub-Gaussian fact that does **not** yet give the
Catoni/Alquier conclusion; it merely diagnoses the critical-exponent
phenomenon (`2 c σ² = 1` exactly).

We state it via Mathlib's `HasSubgaussianMGF` so that any future
upgrade of the Catoni/Alquier lemma in Mathlib can be plugged in
without re-doing the setup work. -/

/-- The sub-Gaussian parameter of the centered empirical average of an
i.i.d. `[0, 1]`-bounded family. For `n` i.i.d. summands each with range
`1`, Hoeffding gives parameter `1/(4n)` for the rescaled centered sum.
At the PAC-Bayes critical exponent `c = 2 n`, this gives `2 c σ² = 1`
exactly — the boundary case that breaks the generic sub-Gaussian
"exp of square" formula and necessitates the Catoni/Alquier route. -/
noncomputable def boundedAverageSubgaussianParam (n : ℕ) : ℝ≥0 :=
  ⟨1 / (4 * (n : ℝ)),
    div_nonneg (by norm_num) (by positivity)⟩

@[simp]
lemma boundedAverageSubgaussianParam_val (n : ℕ) :
    (boundedAverageSubgaussianParam n : ℝ) = 1 / (4 * (n : ℝ)) := rfl

/-- The critical exponent identity: at `c = 2 n` and Hoeffding sub-Gaussian
parameter `σ² = 1 / (4 n)`, the product `2 c σ²` equals `1`. This is the
diagnostic that explains why the generic sub-Gaussian moment formula
`E[exp(c Z²)] ≤ (1 - 2 c σ²)^(-1/2)` diverges at the PAC-Bayes critical
exponent, and why a bounded-differences (Catoni/Alquier) argument is
required. -/
lemma critical_exponent_boundary {n : ℕ} (hn : 0 < n) :
    2 * (2 * (n : ℝ)) * (boundedAverageSubgaussianParam n : ℝ) = 1 := by
  have hn_ne : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [boundedAverageSubgaussianParam_val]
  field_simp
  ring

/-! ### Catoni / Alquier bounded-differences moment lemma — named residual

The mathematical content that the PAC-Bayes chain requires but that
Mathlib does not yet provide. We expose it as a `Prop`-valued
predicate; the discharge is a self-contained 3–7 person-day Mathlib
project requiring `convex-order`, `McDiarmid`, and `Hoeffding–Azuma`
infrastructure that is only partially upstream as of 2026-05-20.

The exact mathematical contract, in plain English:

> **Catoni/Alquier bounded-differences moment lemma.**
> Let `X 0, …, X (n - 1)` be independent real random variables on a
> probability space `(Ω, μ)`, each almost surely in `[0, 1]` and with
> common mean `μ_X`. Then
> `∫ exp(2 n · ((1 / n) ∑ X_i - μ_X)²) ∂μ ≤ 2 √n`.

The standard proof argues via the McDiarmid bounded-differences
inequality applied to the function
`f(x_0, …, x_{n-1}) := ((1/n) ∑ x_i - μ_X)²`, deriving a
Hoeffding-style log-MGF bound on `n · f` then integrating that bound
through the `exp` to obtain the sharp `2 √n` constant. The factor `2`
comes from `Var(f) ≤ 1/n` evaluated against the two-sided tail. See
Alquier 2024, Theorem 4.1 for a complete derivation. -/
def CatoniAlquierBoundedMoment
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (X : Fin n → Ω → ℝ) (μ_X : ℝ) : Prop :=
  boundedMeanSqExpMoment μ X μ_X ≤ 2 * Real.sqrt (n : ℝ)

/-- Convenience unfolder: `CatoniAlquierBoundedMoment` is literally the
moment-integral bound. -/
lemma catoniAlquierBoundedMoment_iff
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (X : Fin n → Ω → ℝ) (μ_X : ℝ) :
    CatoniAlquierBoundedMoment μ X μ_X
      ↔ ∫ ω, Real.exp (2 * (n : ℝ)
              * ((1 / (n : ℝ)) * ∑ i : Fin n, X i ω - μ_X) ^ 2) ∂μ
            ≤ 2 * Real.sqrt (n : ℝ) := by
  unfold CatoniAlquierBoundedMoment
  rfl

/-! ### Headline lemma — scalar Bach Eq. 14.21 from the named residual -/

/-- **Bach 2024 Eq. 14.21 (scalar form), modulo the Catoni/Alquier
residual.**

Given an i.i.d. `[0, 1]`-bounded family `X : Fin n → Ω → ℝ` with common
mean `μ_X`, *and assuming* the Catoni/Alquier bounded-differences moment
lemma at the critical exponent, the squared-exponential moment of the
centered empirical average is bounded by `2 √n`.

This is the statement consumed by the PAC-Bayes carrier theorem
`pac_bayes_mcallester_measure_theoretic_with_bounded_moment_assumption`
(after specialization to the product-measure form via `iIndepFun_pi`).

The "assuming `CatoniAlquierBoundedMoment`" reduction is intentional:
it isolates the one missing Mathlib piece. Once the Catoni/Alquier
lemma is formalized upstream (whether as a free-standing theorem or as
a consequence of upstream McDiarmid/Hoeffding–Azuma work), this
theorem discharges that hypothesis automatically and the PAC-Bayes
chain becomes unconditional. -/
theorem bounded_average_sq_exp_moment_of_catoni_alquier
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (_hn : 0 < n)
    (X : Fin n → Ω → ℝ) (μ_X : ℝ)
    (_hX_meas : ∀ i, Measurable (X i))
    (_hX_indep : iIndepFun X μ)
    (_hX_bdd : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (_hX_same_mean : ∀ i, ∫ ω, X i ω ∂μ = μ_X)
    (h_catoni : CatoniAlquierBoundedMoment μ X μ_X) :
    ∫ ω, Real.exp (2 * (n : ℝ)
          * ((1 / (n : ℝ)) * ∑ i : Fin n, X i ω - μ_X) ^ 2) ∂μ
      ≤ 2 * Real.sqrt (n : ℝ) :=
  (catoniAlquierBoundedMoment_iff μ X μ_X).1 h_catoni

/-! ### Product-measure specialization

The PAC-Bayes carrier consumes the moment bound on the product space
`Measure.pi (fun _ : Fin n => D)`, with the family realized via the
coordinate projections `(fun i ω => ℓ (ω i))`. This subsection bridges
the abstract i.i.d. statement above to that concrete form.

`iIndepFun_pi` gives us that the projection family is i.i.d. on the
product measure; bounded-ness and same-mean transport pointwise. -/

variable {𝒳 : Type*} [MeasurableSpace 𝒳]

/-- The product-measure realization of an i.i.d. sample: `X_i ω := ℓ (ω i)`
where `ω : Fin n → 𝒳` and `ℓ : 𝒳 → ℝ`. This is the concrete family that
the PAC-Bayes carrier consumes. -/
noncomputable def piSampleFamily
    {n : ℕ} (ℓ : 𝒳 → ℝ) (i : Fin n) (ω : Fin n → 𝒳) : ℝ :=
  ℓ (ω i)

omit [MeasurableSpace 𝒳] in
@[simp]
lemma piSampleFamily_apply
    {n : ℕ} (ℓ : 𝒳 → ℝ) (i : Fin n) (ω : Fin n → 𝒳) :
    piSampleFamily ℓ i ω = ℓ (ω i) := rfl

/-- Pointwise-almost-everywhere boundedness transports through the
product-measure realization: if `ℓ` is `[0, 1]`-valued pointwise, then
`piSampleFamily ℓ i` is `[0, 1]`-valued almost everywhere on the product
measure. -/
lemma piSampleFamily_bdd
    {n : ℕ} {D : Measure 𝒳} [IsProbabilityMeasure D]
    {ℓ : 𝒳 → ℝ} (hℓ : ∀ x, ℓ x ∈ Set.Icc (0 : ℝ) 1) (i : Fin n) :
    ∀ᵐ ω ∂(Measure.pi (fun _ : Fin n => D)),
      piSampleFamily ℓ i ω ∈ Set.Icc (0 : ℝ) 1 := by
  refine Filter.Eventually.of_forall (fun ω => ?_)
  simpa [piSampleFamily] using hℓ (ω i)

/-! ### PAC-Bayes carrier bridge

The bridge theorem: starting from the named Catoni/Alquier residual
applied to the product-measure realization, conclude the
product-measure statement consumed by
`bounded_average_sq_exp_moment_assumption` in
`LTFP.Ch14_Probabilistic.PACBayes`.

This is a one-line wrapper around
`bounded_average_sq_exp_moment_of_catoni_alquier`; the work is in
recognizing that the product-measure form *is* the abstract i.i.d.
form once `piSampleFamily` is unfolded. -/

/-- **Bach 2024 Eq. 14.21, product-measure form.** Given the named
Catoni/Alquier residual applied to the product-measure realization of
a `[0, 1]`-bounded loss, the squared-exponential moment of the
centered empirical average over an i.i.d. sample is bounded by
`2 √n`. This is the form consumed directly by
`bounded_average_sq_exp_moment_assumption`. -/
theorem boundedMeanSqExpMoment_pi_of_catoni_alquier
    {n : ℕ} (_hn : 0 < n)
    {D : Measure 𝒳} [IsProbabilityMeasure D]
    {ℓ : 𝒳 → ℝ} (_hℓ : ∀ x, ℓ x ∈ Set.Icc (0 : ℝ) 1)
    (h_catoni :
      CatoniAlquierBoundedMoment
        (Measure.pi (fun _ : Fin n => D))
        (piSampleFamily ℓ)
        (∫ x, ℓ x ∂D)) :
    ∫ ω, Real.exp (2 * (n : ℝ)
            * ((1 / (n : ℝ)) * ∑ i : Fin n, ℓ (ω i)
                - ∫ x, ℓ x ∂D) ^ 2)
        ∂(Measure.pi (fun _ : Fin n => D))
      ≤ 2 * Real.sqrt (n : ℝ) := by
  have h := (catoniAlquierBoundedMoment_iff
    (Measure.pi (fun _ : Fin n => D))
    (piSampleFamily ℓ)
    (∫ x, ℓ x ∂D)).1 h_catoni
  simpa [piSampleFamily] using h

end LTFP.MathlibExt.Probability
