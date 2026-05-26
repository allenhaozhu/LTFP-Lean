/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# d=1 OLS sample-mean distribution and Gaussian MSE

Proposed Mathlib path: `Mathlib/Statistics/OLSSampleD1.lean`.
Proposed Mathlib namespace: `Statistics`.

This module lands the **concrete d=1 OLS sample model** and the
**Gaussian mean-squared error** as a measure-theoretic integral, used
in the closure of `ols_minimax_lower_bound_d1_gaussian` (Bach 2024,
§3.7; Tsybakov 2009, §2.4.2).

## Sample-mean reduction at d=1

For the d=1 fixed-design OLS problem with `n` iid Gaussian samples
`Y_i ~ N(θ, σ²)` (`i = 1, …, n`), the sample mean
`Ȳ = (1/n) ∑_i Y_i` is a *sufficient statistic* and is distributed as

`Ȳ ~ N(θ, σ²/n)`.

The OLS estimator `θ̂ = Ȳ` (and indeed any reasonable estimator at
d=1) only depends on `Ȳ`, so the entire n-sample model collapses to a
single Gaussian draw `Y ~ N(θ, σ²/n)`. We exploit this collapse to
avoid product-measure infrastructure: `olsGaussianSampleD1` is simply
`gaussianReal θ (σ²/n)`, the scalar Gaussian on `ℝ` with mean `θ` and
variance `σ²/n`.

## Main definitions

* `Statistics.olsGaussianSampleD1 θ σ² n` — the d=1 OLS sample-mean
  distribution, `gaussianReal θ (σ²/n)` on `ℝ`. The full joint
  product distribution of the n iid samples is not needed because at
  d=1 the OLS estimator is a function of the sample mean alone.
* `Statistics.gaussianMSED1 A θ σ² n` — the **Gaussian mean-squared
  error** of an estimator `A : ℝ → ℝ` at true parameter `θ` under d=1
  OLS sampling, defined as `∫ y, (A y - θ)² ∂(olsGaussianSampleD1 θ σ² n)`.

## Main results

* `Statistics.gaussianMSED1_nonneg` — the MSE is nonnegative for any
  estimator (integral of nonneg integrand).
* `Statistics.olsGaussianSampleD1_isProbabilityMeasure` — the sample
  distribution is a probability measure for `σ² ≥ 0`, `n > 0` (inherited
  from `gaussianReal`).

## References

* F. Bach, *Learning Theory from First Principles*, MIT Press, 2024,
  §3.7 (Mourtada minimax lower bound for OLS).
* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer,
  2009, §2.4.2 (two-point method, squared-loss form).
* Mourtada, J. (2022). *Exact minimax risk for linear least squares
  and the lower tail of sample covariance matrices*. Annals of
  Statistics 50(4), 2157–2178.

## Tags

OLS, minimax, lower bound, two-point method, Gaussian, sample mean, MSE
-/

namespace LTFP.MathlibExt.Probability

open MeasureTheory ProbabilityTheory

/-- The **d=1 OLS sample-mean distribution**: with `n` iid Gaussian
samples `Y_i ~ N(θ, σ²)`, the sample mean `Ȳ` is distributed as
`N(θ, σ²/n)`. We model the n-sample setup via the distribution of `Ȳ`
because at d=1 the OLS estimator depends only on this sufficient
statistic.

The variance is wrapped as `NNReal` for compatibility with the Mathlib
`gaussianReal` signature; the nonnegativity hypothesis on `σ²` is
threaded through the input. -/
noncomputable def olsGaussianSampleD1
    (θ : ℝ) (sigmaSq : ℝ) (n : ℕ)
    (hσ : 0 ≤ sigmaSq) (hn : 0 < n) : Measure ℝ :=
  ProbabilityTheory.gaussianReal θ
    ⟨sigmaSq / (n : ℝ),
      div_nonneg hσ (by exact_mod_cast hn.le)⟩

/-- The d=1 OLS sample-mean distribution is a probability measure.
This is inherited from the `gaussianReal` instance. -/
instance olsGaussianSampleD1_isProbabilityMeasure
    (θ : ℝ) (sigmaSq : ℝ) (n : ℕ) (hσ : 0 ≤ sigmaSq) (hn : 0 < n) :
    IsProbabilityMeasure (olsGaussianSampleD1 θ sigmaSq n hσ hn) := by
  unfold olsGaussianSampleD1
  infer_instance

/-- The **Gaussian mean-squared error** of an estimator `A : ℝ → ℝ` at
true parameter `θ` under the d=1 OLS sample-mean distribution:

`gaussianMSED1 A θ σ² n = ∫ y, (A y - θ)² ∂(N(θ, σ²/n))`.

This is the concrete instantiation of the abstract `excessRisk` used
in the carrier theorem `ols_minimax_lower_bound_d1_gaussian`. -/
noncomputable def gaussianMSED1
    (A : ℝ → ℝ) (θ : ℝ) (sigmaSq : ℝ) (n : ℕ)
    (hσ : 0 ≤ sigmaSq) (hn : 0 < n) : ℝ :=
  ∫ y, (A y - θ)^2 ∂(olsGaussianSampleD1 θ sigmaSq n hσ hn)

/-- The Gaussian MSE is nonnegative for any estimator: it is the
integral of the pointwise-nonnegative function `(A y - θ)²`. -/
theorem gaussianMSED1_nonneg
    (A : ℝ → ℝ) (θ : ℝ) (sigmaSq : ℝ) (n : ℕ)
    (hσ : 0 ≤ sigmaSq) (hn : 0 < n) :
    0 ≤ gaussianMSED1 A θ sigmaSq n hσ hn := by
  unfold gaussianMSED1
  apply integral_nonneg
  intro y
  exact sq_nonneg _

end LTFP.MathlibExt.Probability
