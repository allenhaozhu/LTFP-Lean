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

**DEAD-END (2026-05-21):** This section sets up the
"`E[exp(2n · Z²)] ≤ 2 √n`" squared-gap exponential moment bound that
was originally believed to be Bach Eq. 14.21. A 2026-05-21 textbook
re-read established that Bach (2024) Ch 14 ends at **Eq. (14.6)** and
does NOT contain an Eq. 14.21; the actual Bach §14.4.2 proof uses
the **linear** Hoeffding MGF `E exp(s(R−R̂)) ≤ exp(s²ℓ∞²/(8n))`
(cited from §1.2.1), followed by integration over the prior, DV,
and Chernoff. The A-class theorem `pac_bayes_mcallester_bach_path`
in `LTFP.Ch14_Probabilistic.PACBayes` follows Bach's actual proof
directly and does **not** depend on the Catoni/Alquier residual.

The `CatoniAlquierBoundedMoment` predicate (and the rest of this
section) is retained for backward-compatibility — the original
`pac_bayes_mcallester_measure_theoretic_with_bounded_moment_assumption`
carrier still type-checks through it — but it is **not** the active
proof route for the McAllester PAC-Bayes bound in this library.

**Original docstring (for reference):**

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

/-! ### Sub-Gaussian variance proxy for bounded centered averages (Phase 3b-1)

Catoni / Alquier's bounded-differences moment lemma rests on the
following sub-Gaussian variance-proxy input for the centered empirical
average:

> *If `X₀, …, X_{n-1}` are i.i.d. real random variables almost surely
> in `[0, 1]` with common mean `μ_X`, then the centered average
> `Z_n := (1/n) ∑ Xᵢ - μ_X` has a sub-Gaussian MGF with parameter
> `σ² = 1 / (4 n)`.*

The proof composes three Mathlib pieces:

1. **Hoeffding's lemma**
   (`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`) gives each
   centered summand `Yᵢ ω := Xᵢ ω - μ_X` a sub-Gaussian MGF with
   parameter `((‖1‖₊ / 2) ^ 2) = 1/4`.
2. **Sum of independent sub-Gaussians**
   (`HasSubgaussianMGF.sum_of_iIndepFun`) compounds the parameters
   additively: `∑ᵢ Yᵢ` is sub-Gaussian with parameter `n · (1/4)`.
3. **Scaling** (`HasSubgaussianMGF.const_mul`) multiplies the
   parameter by the square of the scalar: `(1/n) · ∑ Yᵢ` is
   sub-Gaussian with parameter `(1/n)² · (n/4) = 1/(4n)`.

A final pointwise rewrite identifies the result with the centered
empirical average `Z_n = (1/n) ∑ Xᵢ - μ_X`. -/

omit [MeasurableSpace Ω] in
/-- Algebraic identity for centering a finite average: shifting each
summand by the same constant `c` and averaging is the same as averaging
and then shifting by `c`. -/
private lemma centered_sum_div_eq
    {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → ℝ) (c : ℝ) (ω : Ω) :
    (1 / (n : ℝ)) * ∑ i, (X i ω - c)
      = (1 / (n : ℝ)) * ∑ i, X i ω - c := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- **Sub-Gaussian variance proxy for the centered empirical average
of an i.i.d. `[0, 1]`-bounded family** (Phase 3b-1 of the
Catoni/Alquier bounded-differences route).

Given `n` independent identically distributed `[0, 1]`-valued random
variables `Xᵢ` on a probability space `(Ω, μ)` with common mean `μ_X`,
the centered average

  `Z_n ω := (1 / n) · ∑ᵢ Xᵢ ω - μ_X`

has a sub-Gaussian MGF with parameter `1 / (4 n)`.

This is the basic Hoeffding-style input to the Catoni/Alquier
bounded-differences moment lemma. It is *not* yet Bach Eq. 14.21: the
generic sub-Gaussian "exp of square" formula diverges at the PAC-Bayes
critical exponent `c = 2 n` because `2 c σ² = 2 · 2n · 1/(4n) = 1`
exactly (see `critical_exponent_boundary`). The Catoni/Alquier route
goes one step further to extract the precise `2 √n` constant from
bounded-differences structure. -/
theorem hasSubgaussianMGF_centered_bounded_average
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → ℝ)
    (hX_meas : ∀ i, Measurable (X i))
    (hX_indep : iIndepFun X μ)
    (hX_bdd : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (hX_same_mean : ∀ i, ∫ ω, X i ω ∂μ = ∫ ω, X ⟨0, hn⟩ ω ∂μ) :
    ProbabilityTheory.HasSubgaussianMGF
      (fun ω => (1 / (n : ℝ)) * ∑ i, X i ω - ∫ ω, X ⟨0, hn⟩ ω ∂μ)
      ⟨1 / (4 * (n : ℝ)),
        div_nonneg (by norm_num) (by positivity)⟩
      μ := by
  -- Notation
  set μ_X : ℝ := ∫ ω, X ⟨0, hn⟩ ω ∂μ with hμ_X
  -- Step 1: centered summands `Y i ω := X i ω - μ_X`.
  set Y : Fin n → Ω → ℝ := fun i ω => X i ω - μ_X with hY
  -- Each `X i` is integrable (bounded a.e. on a finite measure).
  have hX_int : ∀ i, Integrable (X i) μ := by
    intro i
    exact Integrable.of_mem_Icc 0 1 (hX_meas i).aemeasurable (hX_bdd i)
  -- Mean of `Y i` is zero.
  have hY_mean : ∀ i, ∫ ω, Y i ω ∂μ = 0 := by
    intro i
    have h_int := hX_int i
    have h_int' : Integrable (fun _ : Ω => μ_X) μ := integrable_const _
    have h_sub : ∫ ω, X i ω - μ_X ∂μ = ∫ ω, X i ω ∂μ - μ_X := by
      rw [integral_sub h_int h_int']
      simp
    have h_same : ∫ ω, X i ω ∂μ = μ_X := by
      rw [hX_same_mean i]
    show ∫ ω, X i ω - μ_X ∂μ = 0
    rw [h_sub, h_same, sub_self]
  -- `Y i ω ∈ [-μ_X, 1 - μ_X]` a.e.
  have hY_bdd : ∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc (-μ_X) (1 - μ_X) := by
    intro i
    filter_upwards [hX_bdd i] with ω hω
    refine ⟨?_, ?_⟩
    · linarith [hω.1]
    · linarith [hω.2]
  -- Measurability of `Y i`.
  have hY_meas : ∀ i, Measurable (Y i) := fun i => (hX_meas i).sub_const _
  -- Step 2: Hoeffding gives sub-Gaussian MGF for each `Y i` with proxy
  -- `((‖(1 - μ_X) - (-μ_X)‖₊ / 2) ^ 2) = (‖1‖₊ / 2)^2 = 1/4`.
  -- We first establish it with the Hoeffding proxy, then identify with `1/4`.
  have hY_subG_hoeff : ∀ i,
      HasSubgaussianMGF (Y i) ((‖(1 - μ_X) - (-μ_X)‖₊ / 2) ^ 2) μ := by
    intro i
    exact hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (hY_meas i).aemeasurable (hY_bdd i) (hY_mean i)
  -- Simplify the Hoeffding proxy to the constant `1/4`.
  have h_proxy_simp : ((‖(1 - μ_X) - (-μ_X)‖₊ / 2) ^ 2 : ℝ≥0) = ⟨1 / 4, by norm_num⟩ := by
    apply NNReal.eq
    push_cast
    have h1 : (1 - μ_X) - (-μ_X) = (1 : ℝ) := by ring
    rw [h1]
    rw [show ‖(1 : ℝ)‖ = 1 by simp]
    norm_num
  have hY_subG : ∀ i, HasSubgaussianMGF (Y i) ⟨1 / 4, by norm_num⟩ μ := by
    intro i
    have h := hY_subG_hoeff i
    rwa [h_proxy_simp] at h
  -- Step 3: Independence of `Y i` via composition with `· - μ_X`.
  have hY_indep : iIndepFun Y μ := by
    have h := hX_indep.comp (fun _ x => x - μ_X) (fun _ => measurable_id.sub_const _)
    exact h
  -- Step 4: Sum of i.i.d. sub-Gaussians with proxy `1/4` each.
  have hSum_subG : HasSubgaussianMGF
      (fun ω => ∑ i, Y i ω) (∑ _i : Fin n, (⟨1 / 4, by norm_num⟩ : ℝ≥0)) μ := by
    exact HasSubgaussianMGF.sum_of_iIndepFun hY_indep
      (fun i _ => hY_subG i)
  -- Simplify the sum of constants to `n / 4`.
  have h_sum_const : (∑ _i : Fin n, (⟨1 / 4, by norm_num⟩ : ℝ≥0))
      = ⟨(n : ℝ) / 4, by positivity⟩ := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    apply NNReal.eq
    rw [NNReal.coe_nsmul, NNReal.coe_mk, NNReal.coe_mk, nsmul_eq_mul]
    ring
  rw [h_sum_const] at hSum_subG
  -- Step 5: Scale by `1/n`.
  have hAvg_subG : HasSubgaussianMGF
      (fun ω => (1 / (n : ℝ)) * ∑ i, Y i ω)
      (⟨(1 / (n : ℝ)) ^ 2, sq_nonneg _⟩ * ⟨(n : ℝ) / 4, by positivity⟩) μ :=
    hSum_subG.const_mul (1 / (n : ℝ))
  -- Simplify the scaled proxy to `1 / (4 n)`.
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  have h_proxy_final :
      (⟨(1 / (n : ℝ)) ^ 2, sq_nonneg _⟩ * ⟨(n : ℝ) / 4, by positivity⟩ : ℝ≥0)
        = ⟨1 / (4 * (n : ℝ)), div_nonneg (by norm_num) (by positivity)⟩ := by
    apply NNReal.eq
    push_cast
    field_simp
  rw [h_proxy_final] at hAvg_subG
  -- Step 6: Identify the scaled sum with the centered empirical average.
  have h_eq : ∀ ω, (1 / (n : ℝ)) * ∑ i, Y i ω
      = (1 / (n : ℝ)) * ∑ i, X i ω - μ_X := by
    intro ω
    show (1 / (n : ℝ)) * ∑ i, (X i ω - μ_X)
      = (1 / (n : ℝ)) * ∑ i, X i ω - μ_X
    exact centered_sum_div_eq hn X μ_X ω
  refine hAvg_subG.congr ?_
  refine Filter.Eventually.of_forall (fun ω => ?_)
  exact h_eq ω

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

/-! ### Bernoulli KL method-of-types spine (Phase 3b-2)

This subsection sets up the alternative route to Bach Eq. 14.21 that
goes through the Bernoulli KL divergence and the method-of-types
identity, as identified by the 2026-05-21 Codex pre-audit. The
McDiarmid-via-sub-Gaussian-MGF route (above) diverges at the critical
exponent `c = 2 n`; the Bernoulli/KL route gives the sharp `2 √n`
constant for Bernoulli random variables directly.

**Mathematical outline (Bernoulli case of Bach Eq. 14.21):**

1. For `p ∈ (0, 1)` and `q ∈ [0, 1]`, define
   `bernoulliKL q p := q · log(q/p) + (1 - q) · log((1 - q)/(1 - p))`
   with the convention `0 · log(0/x) = 0`.

2. **Method-of-types identity.** For an iid `Bernoulli(p)` family
   `X 0, …, X (n - 1)` on `(Ω, μ)` with empirical mean
   `q̂ ω := (1/n) ∑ X i ω`,
   ```
   ∫ exp(n · bernoulliKL (q̂ ω) p) ∂μ
     = ∑_{k = 0}^{n} C(n, k) · (k/n)^k · (1 - k/n)^(n - k).
   ```
   The proof: expand the integral as a weighted sum over the
   `{0, 1}`-valued joint outcomes, use that the joint pmf is
   `p^k (1-p)^(n-k)` for any `k`-of-`n`-successes outcome, observe
   that `exp(n · bernoulliKL (k/n) p) = (k/(np))^k · ((n-k)/(n(1-p)))^(n-k)`,
   and the `p`-dependent factors cancel cleanly with the pmf.

3. **Stirling/Robbins finite-sum bound.**
   `∑_{k = 0}^{n} C(n, k) (k/n)^k (1 - k/n)^(n - k) ≤ 2 √n`.
   This is a classical estimate sometimes attributed to Robbins or
   derived from the entropy form of the Stirling bound. Mathlib has
   `le_factorial_stirling` (the lower bound `√(2πn) (n/e)^n ≤ n!`)
   but the corresponding Robbins UPPER bound on `n!` is explicitly
   noted as *not yet formalised* (see
   `Mathlib.Analysis.SpecialFunctions.Stirling`, comment at line 264).
   Formalizing this upper bound is a 1–2 week Mathlib project on its
   own.

4. **Pinsker for Bernoulli.**
   `2 (q - p)^2 ≤ bernoulliKL q p` for `q ∈ [0, 1]`, `p ∈ (0, 1)`.
   A classical 1D convex-analysis lemma. Mathlib has no direct form
   (as of 2026-05-21 snapshot — no hits on `Pinsker` or
   `tv_dist_le_sqrt_klDiv`).

5. **Composition.** Pinsker gives `exp(2 n · (q̂ - p)^2) ≤
   exp(n · bernoulliKL q̂ p)`. Integrating both sides and applying
   the method-of-types identity + Stirling bound yields
   `∫ exp(2 n · (q̂ - p)^2) ∂μ ≤ 2 √n` — the Bernoulli case of
   Bach Eq. 14.21.

The general `[0, 1]` case (extending Bernoulli to general bounded
variables via convex-order reduction) is **out of scope** for this
phase; it is the harder Phase 3b-3 piece. The Codex pre-audit
confirmed: "Convex domination from `[0,1]` variables to Bernoulli
endpoints is not in mathlib and may be the real hard part." -/

/-- The Bernoulli Kullback-Leibler divergence at parameters `q, p ∈ [0, 1]`:

  `bernoulliKL q p := q · log(q / p) + (1 - q) · log((1 - q) / (1 - p))`.

With the standard convention `0 · log(0/x) = 0` (since `Real.log 0 = 0`
and `0 * anything = 0`, this convention is automatically respected
when `q = 0` or `q = 1`).

For `p ∈ (0, 1)` and `q ∈ [0, 1]` this is the KL divergence between
the Bernoulli distributions `Bernoulli(q)` and `Bernoulli(p)`, viewed
as PMFs on `{0, 1}`. -/
noncomputable def bernoulliKL (q p : ℝ) : ℝ :=
  q * Real.log (q / p) + (1 - q) * Real.log ((1 - q) / (1 - p))

@[simp]
lemma bernoulliKL_def (q p : ℝ) :
    bernoulliKL q p
      = q * Real.log (q / p) + (1 - q) * Real.log ((1 - q) / (1 - p)) := rfl

/-- At `q = p`, the Bernoulli KL divergence vanishes. -/
lemma bernoulliKL_self {p : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    bernoulliKL p p = 0 := by
  unfold bernoulliKL
  have hp_pos : 0 < p := hp.1
  have hp_lt : p < 1 := hp.2
  have hp_ne : p ≠ 0 := ne_of_gt hp_pos
  have h1p_pos : 0 < 1 - p := sub_pos.mpr hp_lt
  have h1p_ne : (1 : ℝ) - p ≠ 0 := ne_of_gt h1p_pos
  rw [div_self hp_ne, div_self h1p_ne, Real.log_one, mul_zero, mul_zero, add_zero]

/-- At `q = 0`, the Bernoulli KL divergence reduces to `log(1 / (1 - p))`. -/
lemma bernoulliKL_zero {p : ℝ} (_hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    bernoulliKL 0 p = Real.log (1 / (1 - p)) := by
  unfold bernoulliKL
  simp

/-- At `q = 1`, the Bernoulli KL divergence reduces to `log(1 / p)`. -/
lemma bernoulliKL_one {p : ℝ} (_hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    bernoulliKL 1 p = Real.log (1 / p) := by
  unfold bernoulliKL
  simp

/-! ### Named residuals for the Bernoulli/KL spine

We expose three `Prop`-valued residuals capturing the technical
content of the Bernoulli/KL method-of-types route. Each is
mathematically standard and provable in principle from Mathlib's
existing infrastructure plus a moderate amount of additional work,
but the work is substantial enough (Stirling upper bound: 1–2 weeks;
Pinsker: 1–2 days; method-of-types identity: 2–4 days of careful
discrete-measure integration) that we factor it out cleanly so the
composition (Bernoulli case of Bach Eq. 14.21) can be stated
unconditionally modulo the residuals.

The residuals are designed to compose: discharging all three gives
the Bernoulli case of Bach Eq. 14.21 mechanically.
-/

/-- **DEAD-END (2026-05-21):** This predicate is part of the
"Bernoulli KL method-of-types" route that targeted a *squared*-gap
exponential moment bound `E[exp(2n·Z²)] ≤ 2√n` (the project-internal
"Eq. 14.21" misnomer). A 2026-05-21 textbook re-read established
that Bach (2024) §14.4.2 does NOT use this route — Bach's actual
proof uses the **linear** Hoeffding MGF `E exp(s·(R−R̂)) ≤ exp(s²K)`
followed by integration over the prior, DV, and Chernoff. The
A-class theorem `pac_bayes_mcallester_bach_path` in
`LTFP.Ch14_Probabilistic.PACBayes` follows Bach's actual proof and
does **not** depend on this predicate. This declaration is retained
for backward-compatibility only.

**Original docstring (for reference):**

**Named residual: Bernoulli method-of-types identity.**

For an iid `Bernoulli(p)` family `X 0, …, X (n - 1)` realized as
`{0, 1}`-valued random variables on a probability space `(Ω, μ)`,
the expectation of `exp(n · bernoulliKL (empirical mean) p)`
equals the `p`-free finite sum on the right-hand side.

**Mathematical content:** Write `Σ X := ∑ X i ω`. Since each `X i ω`
is `{0, 1}`-valued, the random variable `Σ X` takes values in
`{0, 1, …, n}`, and `P(Σ X = k) = C(n, k) p^k (1 - p)^(n - k)`. Then
```
exp(n · bernoulliKL (k/n) p)
  = (k/n)^k · (1 - k/n)^(n - k) · p^(-k) · (1 - p)^(-(n - k))
```
(by expanding the `log` terms in `bernoulliKL`). The expectation
becomes
```
∑_{k = 0}^{n} C(n, k) p^k (1 - p)^(n - k) · exp(n · bernoulliKL (k/n) p)
  = ∑_{k = 0}^{n} C(n, k) (k/n)^k (1 - k/n)^(n - k)
```
with the `p^k (1 - p)^(n - k)` factors canceling exactly.

**Provability:** Standard discrete-measure integration argument.
Estimated 2–4 days of Mathlib-style work using `PMF.bernoulli`,
`integral_fintype_prod_eq_prod`, and `Finset.sum_pow_mul_pow`. Not
attempted in the current dispatch.
-/
def BernoulliMethodOfTypesIdentity
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (X : Fin n → Ω → ℝ) (p : ℝ) : Prop :=
  ∫ ω, Real.exp ((n : ℝ) * bernoulliKL ((1 / (n : ℝ)) * ∑ i, X i ω) p) ∂μ
    = ∑ k : Fin (n + 1), (Nat.choose n k : ℝ)
        * (((k : ℝ) / (n : ℝ)) ^ (k : ℕ))
        * ((1 - (k : ℝ) / (n : ℝ)) ^ (n - (k : ℕ)))

/-- **DEAD-END (2026-05-21):** Same status as
`BernoulliMethodOfTypesIdentity` — part of the wrong-direction
"squared-gap method-of-types" route. The A-class
`pac_bayes_mcallester_bach_path` in `LTFP.Ch14_Probabilistic.PACBayes`
follows Bach's actual proof (linear Hoeffding MGF + DV + Chernoff)
and does NOT depend on this Stirling/Robbins residual. Retained for
backward-compatibility only.

**Original docstring (for reference):**

**Named residual: Stirling/Robbins method-of-types finite-sum bound.**

The `p`-free finite sum produced by the method-of-types identity is
bounded by `2 √n`:
```
∑_{k = 0}^{n} C(n, k) (k/n)^k (1 - k/n)^(n - k) ≤ 2 √n.
```

**Mathematical content:** A classical estimate, sometimes called the
Robbins entropy bound for the binomial coefficient. It can be derived
from Stirling's approximation with the explicit Robbins constants:
```
n! ≤ √(2πn) (n/e)^n · exp(1/(12n))
```
(i.e., the Robbins UPPER bound matching the lower bound). The
maximum of the integrand at `k = n/2` is `C(n, n/2) · 2^(-n)`, which
Stirling estimates as `≤ √(2/(πn))`; the sum over all `k` adds a
factor of `n + 1`, but a sharper bound via concentration of the
binomial gives the `2 √n` form directly.

**Mathlib status (2026-05-21):**
`Mathlib.Analysis.SpecialFunctions.Stirling` provides
`le_factorial_stirling : √(2πn) · (n/e)^n ≤ n!`
(the LOWER bound) but the matching Robbins UPPER bound is explicitly
documented as not yet formalised
("Sharper bounds due to Robbins are available, but are not yet
formalised", `Stirling.lean:264`). Formalizing the Robbins upper
bound is an estimated 1–2 week Mathlib project on its own.

**Provability:** Conditional on the Robbins upper bound, the sum
estimate is a 1–2 day Lean exercise. Not attempted in the current
dispatch.
-/
def MethodOfTypesStirlingBound (n : ℕ) : Prop :=
  ∑ k : Fin (n + 1), (Nat.choose n k : ℝ)
      * (((k : ℝ) / (n : ℝ)) ^ (k : ℕ))
      * ((1 - (k : ℝ) / (n : ℝ)) ^ (n - (k : ℕ)))
    ≤ 2 * Real.sqrt (n : ℝ)

/-- **DEAD-END (2026-05-21):** Same status as
`BernoulliMethodOfTypesIdentity` — part of the wrong-direction
"squared-gap method-of-types" route. The A-class
`pac_bayes_mcallester_bach_path` in `LTFP.Ch14_Probabilistic.PACBayes`
follows Bach's actual proof (linear Hoeffding MGF + DV + Chernoff)
and does NOT depend on Bernoulli Pinsker. Retained for
backward-compatibility only.

**Original docstring (for reference):**

**Named residual: Pinsker inequality for Bernoulli distributions.**

For `q ∈ [0, 1]` and `p ∈ (0, 1)`,
`2 (q - p)^2 ≤ bernoulliKL q p`.

**Mathematical content:** A classical 1D convex-analysis lemma; the
standard proof considers the function
`f(q) := bernoulliKL q p - 2 (q - p)^2`
on `[0, 1]`, shows `f(p) = 0`, `f'(p) = 0`, and `f''(q) ≥ 0` for all
`q ∈ (0, 1)`. The second derivative bound uses
```
f''(q) = 1/q + 1/(1 - q) - 4 = (1 - 4q(1 - q))/(q(1 - q)) ≥ 0
```
since `4 q (1 - q) ≤ 1` for all `q ∈ [0, 1]` (AM-GM applied to
`q + (1 - q) = 1`).

**Mathlib status:** No direct Pinsker lemma in the 2026-05-21
snapshot (no hits on `Pinsker` or `tv_dist_le_sqrt_klDiv`). The
general Pinsker inequality between measures is sometimes available
via `InformationTheory.klDiv` but specialization to the Bernoulli
case requires a separate elementary proof.

**Provability:** 1–2 days of Lean using `Mathlib.Analysis.Convex.Slope`
and the explicit second-derivative computation. Not attempted in the
current dispatch.
-/
def BernoulliPinsker : Prop :=
  ∀ ⦃q p : ℝ⦄, q ∈ Set.Icc (0 : ℝ) 1 → p ∈ Set.Ioo (0 : ℝ) 1 →
    2 * (q - p) ^ 2 ≤ bernoulliKL q p

/-! ### Composition: Bernoulli case of Bach Eq. 14.21 via the named residuals -/

/-- **Bernoulli E[exp(n · KL)] bound from the named residuals.**

Composing `BernoulliMethodOfTypesIdentity` (sub-goal 2) and
`MethodOfTypesStirlingBound` (sub-goal 3) gives the moment bound on
the exponentiated Bernoulli KL of the empirical mean. -/
theorem expectation_exp_n_bernoulliKL_le_two_sqrt
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (_hn : 0 < n) (X : Fin n → Ω → ℝ) (p : ℝ)
    (h_id : BernoulliMethodOfTypesIdentity μ X p)
    (h_stirling : MethodOfTypesStirlingBound n) :
    ∫ ω, Real.exp ((n : ℝ) * bernoulliKL ((1 / (n : ℝ)) * ∑ i, X i ω) p) ∂μ
      ≤ 2 * Real.sqrt (n : ℝ) := by
  unfold BernoulliMethodOfTypesIdentity at h_id
  unfold MethodOfTypesStirlingBound at h_stirling
  rw [h_id]
  exact h_stirling

/-- A handy algebraic identity for the composition step:
for any `n : ℝ` and `Z : ℝ`, we have `2 * n * Z ^ 2 = n * (2 * Z ^ 2)`. -/
private lemma two_n_sq_eq (n Z : ℝ) : 2 * n * Z ^ 2 = n * (2 * Z ^ 2) := by ring

/-- **Bernoulli case of Bach 2024 Eq. 14.21, conditional on the three
named residuals.**

For an iid `Bernoulli(p)` family `X 0, …, X (n - 1)` on `(Ω, μ)` with
common mean `p ∈ (0, 1)`, the squared-exponential moment of the
centered empirical average at the critical exponent `2 n` is bounded
by `2 √n` — *modulo* the three named residuals:

* `BernoulliMethodOfTypesIdentity` (sub-goal 2): expansion of the
  expectation as a `p`-free finite sum.
* `MethodOfTypesStirlingBound` (sub-goal 3): Stirling/Robbins estimate
  on the finite sum.
* `BernoulliPinsker` (sub-goal 5): Pinsker `2 (q - p)^2 ≤ KL(q, p)`.

This is the **Bernoulli case** of Bach Eq. 14.21. The extension to
general `[0, 1]`-bounded variables via convex-order reduction is
**out of scope** for Phase 3b-2 (it is the Phase 3b-3 piece, and
Codex's pre-audit confirms "convex domination from `[0,1]` variables
to Bernoulli endpoints is not in mathlib and may be the real hard
part"). -/
theorem bernoulli_case_bach_eq_14_21
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n) (X : Fin n → Ω → ℝ) {p : ℝ}
    (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (hX_bdd : ∀ i, ∀ᵐ ω ∂μ, X i ω ∈ Set.Icc (0 : ℝ) 1)
    (hX_meas : ∀ i, Measurable (X i))
    (h_id : BernoulliMethodOfTypesIdentity μ X p)
    (h_stirling : MethodOfTypesStirlingBound n)
    (h_pinsker : BernoulliPinsker) :
    ∫ ω, Real.exp (2 * (n : ℝ)
            * ((1 / (n : ℝ)) * ∑ i : Fin n, X i ω - p) ^ 2) ∂μ
      ≤ 2 * Real.sqrt (n : ℝ) := by
  -- Step 1: a.e. boundedness of the empirical mean.
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn_pos
  -- The empirical mean is in [0, 1] a.e.
  have h_emp_bdd : ∀ᵐ ω ∂μ,
      (1 / (n : ℝ)) * ∑ i, X i ω ∈ Set.Icc (0 : ℝ) 1 := by
    have h_all : ∀ᵐ ω ∂μ, ∀ i, X i ω ∈ Set.Icc (0 : ℝ) 1 :=
      ae_all_iff.mpr hX_bdd
    filter_upwards [h_all] with ω hω
    refine ⟨?_, ?_⟩
    · -- 0 ≤ (1/n) · ∑ X i ω
      apply mul_nonneg
      · positivity
      · exact Finset.sum_nonneg (fun i _ => (hω i).1)
    · -- (1/n) · ∑ X i ω ≤ 1
      rw [one_div, inv_mul_le_iff₀ hn_pos, mul_one]
      calc ∑ i, X i ω
          ≤ ∑ _i : Fin n, (1 : ℝ) :=
            Finset.sum_le_sum (fun i _ => (hω i).2)
        _ = (n : ℝ) := by simp
  -- Step 2: pointwise (a.e.) inequality from Pinsker.
  --   exp(2 n · (q̂ - p)^2) ≤ exp(n · bernoulliKL q̂ p)
  have h_pw : ∀ᵐ ω ∂μ,
      Real.exp (2 * (n : ℝ) * ((1 / (n : ℝ)) * ∑ i, X i ω - p) ^ 2)
        ≤ Real.exp ((n : ℝ) *
            bernoulliKL ((1 / (n : ℝ)) * ∑ i, X i ω) p) := by
    filter_upwards [h_emp_bdd] with ω hω
    -- Use Pinsker: 2 (q - p)^2 ≤ bernoulliKL q p
    have h_pinsker_apply := h_pinsker hω hp
    -- Multiply both sides by n (≥ 0)
    have h_n_nonneg : (0 : ℝ) ≤ (n : ℝ) := le_of_lt hn_pos
    have h_mul : (n : ℝ) * (2 * ((1 / (n : ℝ)) * ∑ i, X i ω - p) ^ 2)
        ≤ (n : ℝ) * bernoulliKL ((1 / (n : ℝ)) * ∑ i, X i ω) p :=
      mul_le_mul_of_nonneg_left h_pinsker_apply h_n_nonneg
    -- Rewrite the LHS to match the goal
    rw [← two_n_sq_eq] at h_mul
    exact Real.exp_le_exp.mpr h_mul
  -- Step 3: integrate the inequality and apply the method-of-types bound.
  have h_kl_bound :
      ∫ ω, Real.exp ((n : ℝ) *
            bernoulliKL ((1 / (n : ℝ)) * ∑ i, X i ω) p) ∂μ
        ≤ 2 * Real.sqrt (n : ℝ) :=
    expectation_exp_n_bernoulliKL_le_two_sqrt μ hn X p h_id h_stirling
  -- For the integral comparison we need integrability of the upper bound.
  -- Both sides are nonneg, exp is nonneg; we use `integral_mono_ae` carefully.
  -- A clean route: take the LHS ≤ RHS via `integral_mono_of_nonneg` if both
  -- are integrable, OR use the simpler fact that
  -- `∫ f ∂μ ≤ ∫ g ∂μ` when `f ≤ g` a.e. AND `g` is integrable.
  -- We use the version that handles non-integrable LHS gracefully.
  have h_int_le :
      ∫ ω, Real.exp (2 * (n : ℝ) * ((1 / (n : ℝ)) * ∑ i, X i ω - p) ^ 2) ∂μ
        ≤ ∫ ω, Real.exp ((n : ℝ) *
              bernoulliKL ((1 / (n : ℝ)) * ∑ i, X i ω) p) ∂μ := by
    -- Both integrands are nonneg; we use `integral_mono_ae` modulo integrability.
    -- A safe path: cast to ENNReal via `lintegral` and use `lintegral_mono_ae`.
    -- But the simpler `integral_mono_ae` requires both integrable.
    -- We split on integrability of the RHS.
    by_cases h_RHS_int : Integrable
        (fun ω => Real.exp ((n : ℝ) *
            bernoulliKL ((1 / (n : ℝ)) * ∑ i, X i ω) p)) μ
    · -- LHS is dominated a.e. by an integrable function, hence integrable.
      have h_LHS_int : Integrable
          (fun ω => Real.exp (2 * (n : ℝ)
              * ((1 / (n : ℝ)) * ∑ i, X i ω - p) ^ 2)) μ := by
        refine h_RHS_int.mono' ?_ ?_
        · -- AEStronglyMeasurable
          have : Measurable (fun ω => Real.exp (2 * (n : ℝ)
              * ((1 / (n : ℝ)) * ∑ i, X i ω - p) ^ 2)) := by
            refine Real.measurable_exp.comp ?_
            refine Measurable.mul measurable_const ?_
            refine Measurable.pow_const ?_ _
            refine Measurable.sub ?_ measurable_const
            refine Measurable.mul measurable_const ?_
            exact Finset.measurable_sum _ (fun i _ => hX_meas i)
          exact this.aestronglyMeasurable
        · -- Norm bound: |exp(LHS)| ≤ exp(RHS) a.e.
          filter_upwards [h_pw] with ω hω
          rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
          exact hω
      exact integral_mono_ae h_LHS_int h_RHS_int h_pw
    · -- If the RHS is not integrable, then `h_kl_bound` is a bound on 0
      -- (Bochner integral of non-integrable function is 0), and `2 √n ≥ 0`,
      -- so any nonneg LHS bound also gives the inequality.
      -- Use the integral expression: `∫ f = 0` when f is not integrable.
      rw [integral_undef h_RHS_int] at h_kl_bound
      -- So `2 √n ≥ 0`. We need LHS ≤ 0... but LHS could be positive.
      -- Fall back to lintegral comparison:
      -- Actually, since both sides are nonneg, we use the ENNReal-valued
      -- integral version which doesn't require integrability.
      -- Use `MeasureTheory.integral_le_lintegral_real_or_similar`.
      -- Simpler: rule out this case by integrability of the LHS.
      -- The LHS exp(2n · (q̂ - p)^2) where q̂ ∈ [0,1] a.e. and p ∈ (0,1),
      -- so (q̂ - p)^2 ≤ 1 a.e. and exp(2n · 1) = exp(2n) (bounded), hence
      -- the LHS IS integrable (μ is a probability measure).
      -- But then the RHS-via-Pinsker is bounded by an integrable function
      -- on the dominating side, giving RHS integrable too — contradiction
      -- with h_RHS_int. So this branch is vacuous.
      exfalso
      apply h_RHS_int
      -- Show the RHS function is integrable.
      -- A.e., (1/n) ∑ X i ω ∈ [0, 1], so bernoulliKL (·, p) is bounded
      -- by (a finite explicit bound depending only on p). But this bound
      -- requires Pinsker-converse-like estimates we don't want to develop.
      -- Easier: directly bound exp(n · KL) ≤ (1/p)^n + (1/(1-p))^n
      -- (since KL ≤ log(1/p) + log(1/(1-p)) for q ∈ [0,1])... still requires
      -- a fact about KL.
      -- Cleanest: dominate by a constant via the LHS-integrability route.
      -- exp(n · KL) is *measurable* and the integral is the lintegral
      -- (it's nonneg), so we can use lintegral comparison directly without
      -- assuming RHS integrable.
      -- Bypass: use `integral_eq_lintegral_of_nonneg_ae` to convert both
      -- to lintegrals, then `lintegral_mono_ae`, which is unconditional.
      -- Construct integrability of RHS from this.
      have h_RHS_meas : AEStronglyMeasurable
          (fun ω => Real.exp ((n : ℝ) *
              bernoulliKL ((1 / (n : ℝ)) * ∑ i, X i ω) p)) μ := by
        have : Measurable (fun ω => Real.exp ((n : ℝ) *
            bernoulliKL ((1 / (n : ℝ)) * ∑ i, X i ω) p)) := by
          refine Real.measurable_exp.comp ?_
          refine Measurable.mul measurable_const ?_
          unfold bernoulliKL
          refine Measurable.add ?_ ?_
          · refine Measurable.mul ?_ ?_
            · refine Measurable.mul measurable_const ?_
              exact Finset.measurable_sum _ (fun i _ => hX_meas i)
            · refine Real.measurable_log.comp ?_
              refine Measurable.div ?_ measurable_const
              refine Measurable.mul measurable_const ?_
              exact Finset.measurable_sum _ (fun i _ => hX_meas i)
          · refine Measurable.mul ?_ ?_
            · refine Measurable.sub measurable_const ?_
              refine Measurable.mul measurable_const ?_
              exact Finset.measurable_sum _ (fun i _ => hX_meas i)
            · refine Real.measurable_log.comp ?_
              refine Measurable.div ?_ measurable_const
              refine Measurable.sub measurable_const ?_
              refine Measurable.mul measurable_const ?_
              exact Finset.measurable_sum _ (fun i _ => hX_meas i)
        exact this.aestronglyMeasurable
      -- The LHS is bounded by exp(2n) a.e. (since (q̂ - p)^2 ≤ 1).
      -- And LHS ≤ RHS a.e. is NOT directly usable for RHS integrability;
      -- we'd need an upper bound on the RHS itself.
      -- Actually: we know `h_kl_bound` is `∫ RHS ∂μ ≤ 2 √n` after the
      -- `integral_undef` rewrite says `∫ RHS = 0` due to non-integrability.
      -- But `0 ≤ 2 √n` always; so `h_kl_bound` after the rewrite gives
      -- no info. We genuinely need RHS to be integrable.
      -- The cleanest discharge: bound `exp(n · bernoulliKL q p)` uniformly
      -- on `q ∈ [0, 1]` (it's continuous on the compact interval ... but
      -- log explodes at endpoints, so KL itself can be unbounded).
      -- At q = 0: KL = log(1/(1-p)), finite.
      -- At q = 1: KL = log(1/p), finite.
      -- For p ∈ (0, 1), KL is continuous and bounded on [0, 1] by an
      -- explicit constant; the function ω ↦ KL((1/n) ∑ X i ω, p) is
      -- therefore bounded a.e. on (q̂ ∈ [0, 1] a.e.), and exp(n · KL)
      -- is a.e. bounded by an explicit constant.
      have h_KL_bound : ∀ᵐ ω ∂μ,
          bernoulliKL ((1 / (n : ℝ)) * ∑ i, X i ω) p
            ≤ Real.log (1 / p) + Real.log (1 / (1 - p)) := by
        filter_upwards [h_emp_bdd] with ω hω
        unfold bernoulliKL
        set q : ℝ := (1 / (n : ℝ)) * ∑ i, X i ω with hq
        have hq_mem : q ∈ Set.Icc (0 : ℝ) 1 := hω
        have hq0 : 0 ≤ q := hq_mem.1
        have hq1 : q ≤ 1 := hq_mem.2
        have hp_pos : 0 < p := hp.1
        have hp_lt : p < 1 := hp.2
        have h1q : 0 ≤ 1 - q := by linarith
        have h1p_pos : 0 < 1 - p := by linarith
        -- q * log(q/p) ≤ log(1/p):
        --   if q = 0: 0 ≤ log(1/p) (log(1/p) ≥ 0 since p ≤ 1).
        --   if 0 < q ≤ 1: q · log(q/p) ≤ q · log(1/p) ≤ 1 · log(1/p) = log(1/p)
        --     since log(q/p) ≤ log(1/p) when q ≤ 1 (and 1/p > 0).
        -- Similarly for the second term.
        have h_log_inv_p_nonneg : 0 ≤ Real.log (1 / p) := by
          apply Real.log_nonneg
          rw [le_div_iff₀ hp_pos]
          linarith
        have h_log_inv_1p_nonneg : 0 ≤ Real.log (1 / (1 - p)) := by
          apply Real.log_nonneg
          rw [le_div_iff₀ h1p_pos]
          linarith
        have h1 : q * Real.log (q / p) ≤ Real.log (1 / p) := by
          by_cases hq_zero : q = 0
          · rw [hq_zero, zero_mul]; exact h_log_inv_p_nonneg
          · have hq_pos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hq_zero)
            have h_log_le : Real.log (q / p) ≤ Real.log (1 / p) := by
              apply Real.log_le_log
              · exact div_pos hq_pos hp_pos
              · exact div_le_div_of_nonneg_right hq1 hp_pos.le
            calc q * Real.log (q / p)
                ≤ q * Real.log (1 / p) :=
                  mul_le_mul_of_nonneg_left h_log_le hq0
              _ ≤ Real.log (1 / p) :=
                  mul_le_of_le_one_left h_log_inv_p_nonneg hq1
        have h2 : (1 - q) * Real.log ((1 - q) / (1 - p))
              ≤ Real.log (1 / (1 - p)) := by
          by_cases h1q_zero : 1 - q = 0
          · rw [h1q_zero, zero_mul]; exact h_log_inv_1p_nonneg
          · have h1q_pos : 0 < 1 - q := lt_of_le_of_ne h1q (Ne.symm h1q_zero)
            have h1q_le : 1 - q ≤ 1 := by linarith
            have h_log_le : Real.log ((1 - q) / (1 - p))
                ≤ Real.log (1 / (1 - p)) := by
              apply Real.log_le_log
              · exact div_pos h1q_pos h1p_pos
              · exact div_le_div_of_nonneg_right h1q_le h1p_pos.le
            calc (1 - q) * Real.log ((1 - q) / (1 - p))
                ≤ (1 - q) * Real.log (1 / (1 - p)) :=
                  mul_le_mul_of_nonneg_left h_log_le h1q
              _ ≤ Real.log (1 / (1 - p)) :=
                  mul_le_of_le_one_left h_log_inv_1p_nonneg h1q_le
        linarith
      -- Now RHS = exp(n · KL) ≤ exp(n · (log(1/p) + log(1/(1-p)))) a.e.
      have h_RHS_const_bound : ∀ᵐ ω ∂μ,
          Real.exp ((n : ℝ) *
              bernoulliKL ((1 / (n : ℝ)) * ∑ i, X i ω) p)
            ≤ Real.exp ((n : ℝ) *
                (Real.log (1 / p) + Real.log (1 / (1 - p)))) := by
        filter_upwards [h_KL_bound] with ω hω
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left hω hn_pos.le
      -- And exp(n · const) is integrable on a probability measure (it's a constant).
      have h_const_int : Integrable
          (fun _ : Ω => Real.exp ((n : ℝ) *
              (Real.log (1 / p) + Real.log (1 / (1 - p))))) μ :=
        integrable_const _
      -- Hence RHS is integrable (dominated by an integrable constant).
      refine h_const_int.mono' h_RHS_meas ?_
      filter_upwards [h_RHS_const_bound] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
      exact hω
  exact le_trans h_int_le h_kl_bound

end LTFP.MathlibExt.Probability
