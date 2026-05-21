/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.LinearAlgebra.HermitianRegularizedInv
import LTFP.MathlibExt.Probability.Distributions.MultivariateGaussian
import Mathlib.Tactic.FieldSimp

/-!
# Gaussian Bayes-risk: multivariate ridge-trace wire-up

A small conditional bridge between the spectral ridge-trace identity
(`Matrix.trace_regularizedInv_mul_eq_eigenvalue_sum_real`, lifted to
`ℝ`-symmetric PosDef matrices) and the LTFP scalar Gaussian Bayes-risk
formula (`gaussianBayesRiskScalar`).

This file proves: when the eigenvalue sum `∑ᵢ eigᵢ(M) / (eigᵢ(M) + λ)`
scalarizes to the canonical `d / (1 + λ)` (the `Ŝ = I` isotropic case),
the multivariate ridge trace-risk equals the scalar Gaussian Bayes
risk. The scalarization itself is the parametric hypothesis `hscalar`.

Note: this is NOT a full closure of the B4 Node 3 OLS-minimax carrier.
That requires the quantified Gaussian-conjugate finite-prior hypothesis
and measure-theoretic posterior integration tracked separately in
`LTFP/Ch03_LinearLeastSquares/FixedDesign.lean`.
-/

namespace LTFP.MathlibExt.Probability.Distributions

open Matrix
open scoped BigOperators

noncomputable section

/-- Small wire-up: if the spectral ridge trace scalarizes to the
`Ŝ = I` eigenvalue sum `d / (1 + λ)`, then the multivariate ridge
trace risk is exactly the existing scalar Gaussian Bayes risk. -/
theorem gaussianBayesRiskScalar_eq_regularizedTrace_of_eigenvalue_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hPos : M.PosDef)
    (σSq : ℝ) (sampleN : ℕ) (lam : ℝ) (hlam : 0 ≤ lam)
    (hscalar :
      (∑ i, hPos.1.eigenvalues i / (hPos.1.eigenvalues i + lam)) =
        (Fintype.card ι : ℝ) / (1 + lam)) :
    gaussianBayesRiskScalar σSq (Fintype.card ι) sampleN lam =
      σSq * (((M + lam • (1 : Matrix ι ι ℝ))⁻¹ * M).trace) / sampleN := by
  classical
  have htrace :=
    Matrix.trace_regularizedInv_mul_eq_eigenvalue_sum_real M hPos lam hlam
  have hden : (1 + lam) ≠ 0 := by
    have hpos : (0 : ℝ) < 1 + lam := by linarith
    exact ne_of_gt hpos
  rw [htrace, hscalar, gaussianBayesRiskScalar_eq]
  by_cases hn : (sampleN : ℝ) = 0
  · simp [hn]
  · field_simp [hn, hden]

end

end LTFP.MathlibExt.Probability.Distributions
