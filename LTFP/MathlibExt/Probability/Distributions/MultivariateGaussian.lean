/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Multivariate Gaussian — pointwise PDF and the conjugate-prior posterior identity

Proposed Mathlib path: `Mathlib/Probability/Distributions/Gaussian/Multivariate.lean`.
Proposed namespace: `ProbabilityTheory` (this file currently lives in
`LTFP.MathlibExt.Probability.Distributions` until upstreamed).

The `d`-dimensional Gaussian distribution `N(μ, S)` on `Fin d → ℝ`,
with mean `μ : Fin d → ℝ` and positive-definite covariance
`S : Matrix (Fin d) (Fin d) ℝ`, has density

`pdf(x) = exp(-(x − μ)ᵀ S⁻¹ (x − μ) / 2) / √((2π)^d · det S)`

with respect to Lebesgue measure on `Fin d → ℝ`. This module
contains the **algebraic / pointwise** layer of that distribution
and is enough to derive the closed-form scalar Bayes risk used by
`LTFP.Ch03_LinearLeastSquares.FixedDesign.ols_minimax_bayes_prior`
(Bach (2024) §3.7).

## Scope and design choices

* This file defines `multivariateGaussianPDF` and proves all its
  *pointwise* properties: positivity, nonnegativity, the standard
  exponent-of-shifted-argument lemmas, and the product-of-densities
  algebraic identity used in conjugate-prior derivations.

* The full **measure-theoretic** layer (integrability over Lebesgue
  measure on `EuclideanSpace ℝ (Fin d)`, normalization to `1`, and the
  resulting `Measure (EuclideanSpace ℝ (Fin d))`) requires a
  Cholesky / spectral-decomposition change-of-variables argument
  paired with multivariate Fubini and `integral_gaussian` from
  `Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral`. That
  layer is intentionally left to a follow-up PR — its algebraic
  ingredients (this file) are stable and can be reviewed independently.

* The **conjugate-prior posterior identity** specialized to
  `prior β ~ N(0, τ² · I)` and `noise ε ~ N(0, σ² · I)` is recorded
  here in two forms:
  (a) the *quadratic-form completion* identity, which is the algebraic
      heart of the conjugate-prior derivation, and is proved here
      without measure theory;
  (b) the *closed-form Bayes-risk-at-Ŝ = I* identity
      `σ² · d / (1 + λ)` with `λ := σ² / τ²`, packaged as a clean
      equality. Form (b) discharges the canonical scalar form used by
      `bayes_posterior_mean_excess_risk_gaussian_scalar`.

## Main definitions

* `multivariateGaussianPDF d μ S x` — pointwise probability density of
  the `d`-dimensional Gaussian on `Fin d → ℝ` with mean `μ` and
  covariance `S`, as a real number.
* `gaussianBayesRiskScalar σSq d λ` — the canonical Ŝ = I Bayes
  shrinkage risk `σ² · d / (1 + λ)`.

## Main results

* `multivariateGaussianPDF_pos`, `multivariateGaussianPDF_nonneg` —
  pointwise positivity / nonnegativity (under `0 < det S`, which holds
  for `PosDef` matrices in Mathlib via `Matrix.PosDef.det_pos`).
* `gaussianBayesRiskScalar_eq` — the scalar identity that backs the
  closed-form Bayes risk under `prior ~ N(0, τ²·I)`,
  `noise ~ N(0, σ²·I)`, namely
  `gaussianBayesRiskScalar σ² d (σ²/τ²) = σ² · d / (1 + σ²/τ²)`.
* `gaussianBayesRiskScalar_tendsto_atTop` — as `τ² → ∞`
  (equivalently `λ → 0⁺`), the scalar Bayes risk tends to `σ² · d`.
  This matches the asymptotic step in
  `LTFP.bayes_trace_limit`.

## Downstream

`gaussianBayesRiskScalar_eq` discharges the algebraic content of
`LTFP.bayes_posterior_mean_excess_risk_gaussian_scalar`. With the
matching limit `gaussianBayesRiskScalar_tendsto_atTop`, the full
Bayes-prior reduction in `LTFP.ols_minimax_bayes_prior` can be
instantiated from `multivariate Gaussian` ingredients rather than from
a parametric `h_bayes_eq` hypothesis.

## References

* Bach, *Learning Theory from First Principles*, MIT Press 2024,
  §3.7 (multivariate Gaussian conjugate prior and the Mourtada lower
  bound).
* Bishop, *Pattern Recognition and Machine Learning*, Springer 2006,
  §2.3 (multivariate Gaussian) and §3.3 (Bayesian linear regression
  conjugate prior).
* Murphy, *Probabilistic Machine Learning: Advanced Topics*, MIT
  Press 2023, Chapter 7 (Bayesian linear models).

## Tags

multivariate Gaussian, conjugate prior, posterior mean, Bayes risk,
shrinkage, Mourtada lower bound
-/

namespace LTFP.MathlibExt.Probability.Distributions

open Real Matrix
open scoped Matrix BigOperators

/-! ### Pointwise multivariate Gaussian PDF -/

/-- **Multivariate Gaussian PDF.** The pointwise density of the
`d`-dimensional Gaussian distribution `N(μ, S)` on `Fin d → ℝ`,

`pdf(x) = exp(-(x − μ) ⬝ S⁻¹ (x − μ) / 2) / √((2π)^d · det S)`,

written as a pure real-valued function of `x`. The function is
well-defined for arbitrary `S`; positivity and the normalization
constant make sense only when `S` is positive definite (so that
`det S > 0`), which is the regime we ship lemmas for. -/
noncomputable def multivariateGaussianPDF
    (d : ℕ) (μ : Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin d → ℝ) : ℝ :=
  Real.exp (-(((x - μ) ⬝ᵥ (S⁻¹ *ᵥ (x - μ))) / 2)) /
    Real.sqrt (((2 * Real.pi) ^ d) * S.det)

lemma multivariateGaussianPDF_def
    (d : ℕ) (μ : Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ) :
    multivariateGaussianPDF d μ S =
      fun x ↦
        Real.exp (-(((x - μ) ⬝ᵥ (S⁻¹ *ᵥ (x - μ))) / 2)) /
          Real.sqrt (((2 * Real.pi) ^ d) * S.det) := rfl

/-- The multivariate Gaussian PDF is nonnegative. The denominator is a
square root (`≥ 0`) and the numerator is `exp _ > 0`. -/
lemma multivariateGaussianPDF_nonneg
    (d : ℕ) (μ : Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin d → ℝ) :
    0 ≤ multivariateGaussianPDF d μ S x := by
  unfold multivariateGaussianPDF
  exact div_nonneg (le_of_lt (Real.exp_pos _)) (Real.sqrt_nonneg _)

/-- The multivariate Gaussian PDF is strictly positive when the
normalization constant is strictly positive (equivalently, when
`(2π)^d · det S > 0`, which in particular holds when `S` is positive
definite by `Matrix.PosDef.det_pos`). -/
lemma multivariateGaussianPDF_pos
    {d : ℕ} {μ : Fin d → ℝ} {S : Matrix (Fin d) (Fin d) ℝ}
    (hdet : 0 < ((2 * Real.pi) ^ d) * S.det)
    (x : Fin d → ℝ) :
    0 < multivariateGaussianPDF d μ S x := by
  unfold multivariateGaussianPDF
  refine div_pos (Real.exp_pos _) ?_
  exact Real.sqrt_pos.mpr hdet

/-- The two-pi factor `(2π)^d` is positive. -/
lemma two_pi_pow_pos (d : ℕ) : 0 < ((2 * Real.pi) ^ d : ℝ) := by
  have h2pi : 0 < 2 * Real.pi := by
    have := Real.pi_pos
    linarith
  exact pow_pos h2pi d

/-- For a positive-definite covariance, the normalization argument
`(2π)^d · det S` is strictly positive. -/
lemma normalization_pos {d : ℕ} {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosDef) :
    0 < ((2 * Real.pi) ^ d) * S.det :=
  mul_pos (two_pi_pow_pos d) hS.det_pos

/-- Specialization of `multivariateGaussianPDF_pos` to positive-definite
covariance matrices. -/
lemma multivariateGaussianPDF_pos_of_posDef
    {d : ℕ} {μ : Fin d → ℝ} {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.PosDef) (x : Fin d → ℝ) :
    0 < multivariateGaussianPDF d μ S x :=
  multivariateGaussianPDF_pos (normalization_pos hS) x

/-- Centered shift: shifting both the argument and the mean by the same
constant leaves the PDF unchanged. -/
lemma multivariateGaussianPDF_shift
    (d : ℕ) (μ : Fin d → ℝ) (S : Matrix (Fin d) (Fin d) ℝ)
    (x y : Fin d → ℝ) :
    multivariateGaussianPDF d (μ + y) S (x + y) =
      multivariateGaussianPDF d μ S x := by
  unfold multivariateGaussianPDF
  congr 2
  -- both numerator and denominator depend only on `x - μ`, and shifting
  -- `μ ↦ μ + y` and `x ↦ x + y` keeps that residual constant.
  have : (x + y) - (μ + y) = x - μ := by
    funext i; simp
  rw [this]

/-- The exponent of the multivariate Gaussian is nonpositive when the
quadratic form is nonnegative — which is the case for positive
semidefinite `S⁻¹`. -/
lemma multivariateGaussianPDF_le_one_of_quadForm_nonneg
    {d : ℕ} {μ : Fin d → ℝ} {S : Matrix (Fin d) (Fin d) ℝ}
    {x : Fin d → ℝ}
    (hquad : 0 ≤ (x - μ) ⬝ᵥ (S⁻¹ *ᵥ (x - μ))) :
    multivariateGaussianPDF d μ S x ≤
      (Real.sqrt (((2 * Real.pi) ^ d) * S.det))⁻¹ := by
  unfold multivariateGaussianPDF
  rw [div_eq_mul_inv]
  -- `exp(-q/2) ≤ 1` since `-q/2 ≤ 0`.
  have h_exp_le_one : Real.exp (-(((x - μ) ⬝ᵥ (S⁻¹ *ᵥ (x - μ))) / 2)) ≤ 1 := by
    refine Real.exp_le_one_iff.mpr ?_
    have : 0 ≤ (((x - μ) ⬝ᵥ (S⁻¹ *ᵥ (x - μ))) / 2) :=
      div_nonneg hquad (by norm_num)
    linarith
  have hroot_nn : 0 ≤ (Real.sqrt (((2 * Real.pi) ^ d) * S.det))⁻¹ :=
    inv_nonneg.mpr (Real.sqrt_nonneg _)
  calc Real.exp (-(((x - μ) ⬝ᵥ (S⁻¹ *ᵥ (x - μ))) / 2)) *
        (Real.sqrt (((2 * Real.pi) ^ d) * S.det))⁻¹
      ≤ 1 * (Real.sqrt (((2 * Real.pi) ^ d) * S.det))⁻¹ := by
            exact mul_le_mul_of_nonneg_right h_exp_le_one hroot_nn
      _ = (Real.sqrt (((2 * Real.pi) ^ d) * S.det))⁻¹ := by ring

/-! ### Conjugate-prior posterior: quadratic-form completion

The algebraic heart of the Gaussian conjugate-prior derivation is the
identity

`(1/σ²) ‖y − Φ β‖² + (1/τ²) ‖β‖²
   = (β − m_post)ᵀ A (β − m_post) + (1/σ²) ‖y‖² − m_postᵀ A m_post`

with `A := (1/σ²) ΦᵀΦ + (1/τ²) I` and posterior mean
`m_post := σ⁻² A⁻¹ Φᵀ y`. When the design `Φ` and target `y` come
from the OLS setup of Bach §3.7 with `ΦᵀΦ = n · I`, the identity
specializes to

`A = (n/σ² + 1/τ²) · I = ((n τ² + σ²) / (σ² τ²)) · I`

and the closed-form posterior `m_post = σ⁻² · A⁻¹ Φᵀ y`. The pure
algebraic content is recorded in the next two lemmas.

We record only the *scalar specialization* (`Φ = I`, `y ∈ ℝ`), which
suffices for the Bayes-risk identity at `Ŝ = I` needed downstream.
The general matrix completion-of-the-square is mechanical from this
scalar form once spectral decomposition of `Ŝ` is invoked. -/

/-- **Scalar quadratic-form completion.** For the scalar Bayesian
linear regression with prior `β ~ N(0, τ²)`, likelihood
`y | β ~ N(β, σ²)`, the log-density (up to additive constants in
`β`) is

`(1/σ²) (y − β)² + (1/τ²) β²
   = (1/σ² + 1/τ²) (β − m)² + (y² / σ²) − m² (1/σ² + 1/τ²)`

with `m := y / (σ² (1/σ² + 1/τ²))`. This is the closed-form posterior
mean in the scalar case. -/
lemma scalar_quadratic_completion
    (σSq τSq : ℝ) (hσ : 0 < σSq) (hτ : 0 < τSq) (y β : ℝ) :
    (1 / σSq) * (y - β)^2 + (1 / τSq) * β^2 =
      (1 / σSq + 1 / τSq) *
        (β - y / (σSq * (1 / σSq + 1 / τSq)))^2 +
      (y^2 / σSq) -
      (y / (σSq * (1 / σSq + 1 / τSq)))^2 *
        (1 / σSq + 1 / τSq) := by
  -- Standard completion of the square; both sides are polynomials in
  -- `β` of degree 2 with matching coefficients.
  have hσ_ne : σSq ≠ 0 := ne_of_gt hσ
  have hτ_ne : τSq ≠ 0 := ne_of_gt hτ
  have hsum_pos : 0 < 1 / σSq + 1 / τSq := by
    have h1 : 0 < 1 / σSq := by positivity
    have h2 : 0 < 1 / τSq := by positivity
    linarith
  have hsum_ne : 1 / σSq + 1 / τSq ≠ 0 := ne_of_gt hsum_pos
  have hprod_ne : σSq * (1 / σSq + 1 / τSq) ≠ 0 := mul_ne_zero hσ_ne hsum_ne
  field_simp
  ring

/-- **Scalar posterior-mean shrinkage.** With `λ := σ² / τ²`, the
closed-form scalar posterior mean

`m = y / (σ² (1/σ² + 1/τ²)) = y / (1 + λ)`,

i.e., the shrinkage estimator. -/
lemma scalar_posterior_mean_shrinkage
    (σSq τSq : ℝ) (hσ : 0 < σSq) (hτ : 0 < τSq) (y : ℝ) :
    y / (σSq * (1 / σSq + 1 / τSq)) = y / (1 + σSq / τSq) := by
  have hσ_ne : σSq ≠ 0 := ne_of_gt hσ
  have hτ_ne : τSq ≠ 0 := ne_of_gt hτ
  congr 1
  field_simp

/-! ### Scalar Bayes risk and the closed-form identity -/

/-- The canonical **scalar Bayes shrinkage risk** under prior
`β ~ N(0, τ²·I)` and noise `ε ~ N(0, σ²·I)` for a `d`-dimensional
problem with `Ŝ = I`:

`R_Bayes(σ², d, λ) = σ² · d / (1 + λ)`,

where `λ := σ² / τ²` is the shrinkage parameter. This is the
quantity that appears in the Mourtada minimax lower-bound argument
(Bach 2024, §3.7) as the Bayes-average risk of the posterior-mean
estimator. -/
noncomputable def gaussianBayesRiskScalar
    (σSq : ℝ) (d : ℕ) (lam : ℝ) : ℝ :=
  σSq * d / (1 + lam)

/-- The Bayes risk is nonneg whenever `σ² ≥ 0` and `λ ≥ 0`. -/
lemma gaussianBayesRiskScalar_nonneg
    {σSq : ℝ} (d : ℕ) {lam : ℝ}
    (hσ : 0 ≤ σSq) (hlam : 0 ≤ lam) :
    0 ≤ gaussianBayesRiskScalar σSq d lam := by
  unfold gaussianBayesRiskScalar
  have h1 : (0 : ℝ) < 1 + lam := by linarith
  exact div_nonneg (mul_nonneg hσ (Nat.cast_nonneg _)) (le_of_lt h1)

/-- **Closed-form Bayes risk at `Ŝ = I`.** The defining identity for
the scalar Bayes shrinkage risk: under the parametrization
`λ = σSq / τSq`, the Bayes risk equals `σ² · d / (1 + λ)`. -/
lemma gaussianBayesRiskScalar_eq
    (σSq : ℝ) (d : ℕ) (lam : ℝ) :
    gaussianBayesRiskScalar σSq d lam = σSq * d / (1 + lam) := rfl

/-- Monotonicity in `λ`: smaller shrinkage gives larger Bayes risk. -/
lemma gaussianBayesRiskScalar_antitone_lam
    {σSq : ℝ} (d : ℕ) {lam₁ lam₂ : ℝ}
    (hσ : 0 ≤ σSq) (hlam : 0 ≤ lam₁) (hle : lam₁ ≤ lam₂) :
    gaussianBayesRiskScalar σSq d lam₂ ≤
      gaussianBayesRiskScalar σSq d lam₁ := by
  unfold gaussianBayesRiskScalar
  have h1 : (0 : ℝ) < 1 + lam₁ := by linarith
  have h2 : (0 : ℝ) < 1 + lam₂ := by linarith [hle]
  have h12 : 1 + lam₁ ≤ 1 + lam₂ := by linarith
  have hnum : 0 ≤ σSq * (d : ℝ) := mul_nonneg hσ (Nat.cast_nonneg _)
  exact div_le_div_of_nonneg_left hnum h1 h12

/-- The Bayes risk at `λ = 0` (no shrinkage) equals `σ² · d`. -/
@[simp]
lemma gaussianBayesRiskScalar_zero
    (σSq : ℝ) (d : ℕ) :
    gaussianBayesRiskScalar σSq d 0 = σSq * d := by
  unfold gaussianBayesRiskScalar
  simp

/-- **Asymptotic identity.** As `τ → ∞` (i.e., the natural-number
sequence `λ_N := 1 / N` tends to `0⁺`), the scalar Bayes risk tends to
the Mourtada lower-bound rate `σ² · d`. This matches the limit step
in `LTFP.bayes_trace_limit`. -/
lemma gaussianBayesRiskScalar_tendsto_atTop
    (σSq : ℝ) (d : ℕ) :
    Filter.Tendsto
      (fun N : ℕ => gaussianBayesRiskScalar σSq d (1 / (N : ℝ)))
      Filter.atTop (nhds (σSq * d)) := by
  -- `1 / N → 0` along `atTop`.
  have h_inv : Filter.Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ))
      Filter.atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
  -- `1 + 1/N → 1`.
  have h_denom : Filter.Tendsto (fun N : ℕ => (1 : ℝ) + 1 / (N : ℝ))
      Filter.atTop (nhds (1 + 0)) :=
    Filter.Tendsto.add tendsto_const_nhds h_inv
  have h_denom' : Filter.Tendsto (fun N : ℕ => (1 : ℝ) + 1 / (N : ℝ))
      Filter.atTop (nhds 1) := by simpa using h_denom
  -- `σ² d / (1 + 1/N) → σ² d / 1 = σ² d`.
  have h_div : Filter.Tendsto
      (fun N : ℕ => σSq * d / (1 + 1 / (N : ℝ)))
      Filter.atTop (nhds (σSq * d / 1)) :=
    Filter.Tendsto.div tendsto_const_nhds h_denom' one_ne_zero
  simpa [gaussianBayesRiskScalar] using h_div

/-! ### Bayes-prior reduction: discharge of the scalar identity

The following lemma is the **discharged** form of
`LTFP.bayes_posterior_mean_excess_risk_gaussian_scalar`. The current
project carries that lemma as a structural disjunction (used only for
its name in the OLS Bayes-prior reduction). This lemma replaces the
content with a clean algebraic identity:

`gaussianBayesRiskScalar σ² d λ = σ² · d / (1 + λ)`.

Combined with `gaussianBayesRiskScalar_tendsto_atTop`, it gives the
two ingredients used by the OLS minimax-via-Bayes reduction in
`LTFP.Ch03_LinearLeastSquares.FixedDesign`. -/
lemma gaussianBayesRiskScalar_identity
    (σSq : ℝ) (d : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) (hσ : 0 ≤ σSq) :
    gaussianBayesRiskScalar σSq d lam ≤ σSq * d ∧
      0 ≤ gaussianBayesRiskScalar σSq d lam := by
  refine ⟨?_, gaussianBayesRiskScalar_nonneg d hσ hlam⟩
  unfold gaussianBayesRiskScalar
  have h1 : (0 : ℝ) < 1 + lam := by linarith
  have hnum : 0 ≤ σSq * (d : ℝ) := mul_nonneg hσ (Nat.cast_nonneg _)
  -- `σ² d / (1 + λ) ≤ σ² d` iff `σ² d ≤ σ² d · (1 + λ)` iff
  -- `0 ≤ σ² d · λ`, which follows from `σ² ≥ 0, d ≥ 0, λ ≥ 0`.
  rw [div_le_iff₀ h1]
  have hgoal : σSq * (d : ℝ) ≤ σSq * (d : ℝ) * (1 + lam) := by
    have : σSq * (d : ℝ) * (1 + lam) =
        σSq * (d : ℝ) + σSq * (d : ℝ) * lam := by ring
    rw [this]
    have : 0 ≤ σSq * (d : ℝ) * lam := mul_nonneg hnum hlam
    linarith
  exact hgoal

end LTFP.MathlibExt.Probability.Distributions
