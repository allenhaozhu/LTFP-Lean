/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Matrix Chernoff / Markov bound on the maximum eigenvalue

For a random Hermitian matrix `X : Ω → Matrix n n ℂ`, the Laplace
transform method bounds the upper tail of its maximum eigenvalue by
the expected trace of the matrix exponential. This is the core
matrix-Chernoff inequality that underlies the matrix Bernstein
concentration inequality.

The pointwise spectral bridge

  `Real.exp (θ · λₘₐₓ(X ω)) ≤ (trace (exp (θ · X ω))).re`

(supplied by `CFC.exp_theta_lambdaMax_le_trace_exp`) combined with the
scalar Chernoff bound on a finite measure gives, for any `θ > 0`,

  `μ{ω | t ≤ λₘₐₓ(X ω)} ≤ exp(-θ t) · ∫ ω, (trace (exp (θ · X ω))).re ∂μ`.

The measurability of `ω ↦ λₘₐₓ(X ω)` is taken as a hypothesis: the
required infrastructure (measurability of the spectral functional
calculus of a measurable matrix-valued map) is not currently in
Mathlib at the pinned commit.

## Main result

* `matrix_markov_lambdaMax_trace_exp` : the matrix Markov bound on the
  maximum eigenvalue, in terms of the trace-exponential MGF surrogate.
-/
import LTFP.MathlibExt.MatrixAnalysis.SpectralTraceExp
import Mathlib.Probability.Moments.Basic

namespace CFC

open MeasureTheory ProbabilityTheory Finset Real

/-- **Matrix Markov / Chernoff bound on the maximum eigenvalue.**

For a measurable family `X : Ω → Matrix n n ℂ` of Hermitian matrices
on a finite measure space `(Ω, μ)`, and any positive scalar `θ > 0`,
the upper-tail measure of the maximum eigenvalue is controlled by the
trace-exponential surrogate moment generating function:

  `μ.real {ω | t ≤ λₘₐₓ(X ω)} ≤ exp(-θ t) · ∫ ω, (tr exp (θ • X ω)).re ∂μ`.

This is the matrix-Chernoff key step underlying the matrix Bernstein
inequality. The pointwise spectral bound `exp(θ · λₘₐₓ) ≤ (tr exp(θ•A)).re`
(Part 1) supplies the bridge from the scalar Chernoff bound applied to
the real random variable `λₘₐₓ(X ·)` to the trace-exponential dominator.

`hYMeas` is required as a hypothesis: a.e.-measurability of
`ω ↦ λₘₐₓ(X ω)` follows from measurability of `X` and continuity of
the spectral functional calculus, but the corresponding Mathlib
infrastructure is not yet available at this pin. -/
theorem matrix_markov_lambdaMax_trace_exp
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [MeasureTheory.IsFiniteMeasure μ]
    (X : Ω → Matrix n n ℂ) (hX : ∀ ω, (X ω).IsHermitian)
    (t θ : ℝ) (hθ : 0 < θ)
    (hYMeas : AEMeasurable
      (fun ω => Finset.sup' Finset.univ Finset.univ_nonempty (hX ω).eigenvalues) μ)
    (hInt : Integrable
      (fun ω => (Matrix.trace (NormedSpace.exp (θ • X ω))).re) μ) :
    μ.real {ω | t ≤ Finset.sup' Finset.univ Finset.univ_nonempty (hX ω).eigenvalues} ≤
      Real.exp (-θ * t) *
        ∫ ω, (Matrix.trace (NormedSpace.exp (θ • X ω))).re ∂μ := by
  classical
  -- Set `Y ω := λₘₐₓ(X ω)` and `Z ω := (trace exp (θ • X ω)).re`.
  set Y : Ω → ℝ := fun ω =>
    Finset.sup' Finset.univ Finset.univ_nonempty (hX ω).eigenvalues with hY_def
  set Z : Ω → ℝ := fun ω => (Matrix.trace (NormedSpace.exp (θ • X ω))).re with hZ_def
  -- Pointwise spectral lower bound from Part 1: `exp(θ * Y ω) ≤ Z ω`.
  have h_ptwise : ∀ ω, Real.exp (θ * Y ω) ≤ Z ω := by
    intro ω
    exact CFC.exp_theta_lambdaMax_le_trace_exp (hX ω) θ
  -- Strong measurability of the MGF integrand `fun ω => exp (θ * Y ω)`.
  have h_aemeasMGF :
      AEMeasurable (fun ω => Real.exp (θ * Y ω)) μ :=
    Real.measurable_exp.comp_aemeasurable (hYMeas.const_mul θ)
  have h_aesmMGF :
      AEStronglyMeasurable (fun ω => Real.exp (θ * Y ω)) μ :=
    h_aemeasMGF.aestronglyMeasurable
  -- Squeeze: MGF integrand is dominated by trace integrand, hence integrable.
  have h_intMGF : Integrable (fun ω => Real.exp (θ * Y ω)) μ := by
    refine hInt.mono' h_aesmMGF (ae_of_all _ ?_)
    intro ω
    -- `‖exp(θ * Y ω)‖ = exp(θ * Y ω) ≤ Z ω`.
    have h_nn : 0 ≤ Real.exp (θ * Y ω) := (Real.exp_pos _).le
    simpa [Real.norm_eq_abs, abs_of_nonneg h_nn] using h_ptwise ω
  -- Scalar Chernoff bound on `Y` at threshold `t` and `θ ≥ 0`.
  have h_chernoff :
      μ.real {ω | t ≤ Y ω} ≤ Real.exp (-θ * t) * mgf Y μ θ :=
    measure_ge_le_exp_mul_mgf (X := Y) (μ := μ) (t := θ) t hθ.le h_intMGF
  -- Bound `mgf Y μ θ = ∫ ω, exp (θ * Y ω) ∂μ ≤ ∫ ω, Z ω ∂μ`.
  have h_mgf_le :
      mgf Y μ θ ≤ ∫ ω, Z ω ∂μ := by
    unfold mgf
    exact integral_mono_ae h_intMGF hInt (ae_of_all _ h_ptwise)
  -- Multiply by `exp(-θ t) ≥ 0` and chain.
  have h_factor_nn : 0 ≤ Real.exp (-θ * t) := (Real.exp_pos _).le
  calc
    μ.real {ω | t ≤ Y ω}
        ≤ Real.exp (-θ * t) * mgf Y μ θ := h_chernoff
    _ ≤ Real.exp (-θ * t) * ∫ ω, Z ω ∂μ := by
          exact mul_le_mul_of_nonneg_left h_mgf_le h_factor_nn

end CFC
