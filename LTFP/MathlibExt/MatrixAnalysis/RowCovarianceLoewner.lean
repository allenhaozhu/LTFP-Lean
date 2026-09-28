/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.MatrixAnalysis.HermitianSqLeNormSqOne
import LTFP.MathlibExt.Probability.NTKConcentrationMatrixBernstein
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Row-covariance Loewner tightening of the matrix Bernstein variance proxy

This module proves the standard row-covariance Loewner bound

  `∑ i, X i * (X i)ᴴ ≤ (R^2 * card ι) • 1`

for a family `X : ι → Matrix (Fin n) (Fin n) ℂ` with `‖X i‖ ≤ R`
uniformly in `i`.  Compared with the coarse deterministic proxy
`R^2 * card ι` in the standard matrix Bernstein bound, the row
covariance `∑ i, X i * (X i)ᴴ` is Loewner-tighter — it is the object
which appears in the matrix Bernstein variance hypothesis
(`Matrix.bernstein_full`), and Loewner-monotonicity of the
scalar-variance functional in that hypothesis lets us plug in the
tighter proxy `‖Σ‖` instead of `R^2 * card ι` without further work.

The concrete factor of the tightening (`κ = (R^2 * card ι) / ‖Σ‖`)
depends on the input distribution and activation of the underlying
NTK model.  Numerical values `κ ≈ 84×` for `(p=32, d=8, m=16)` and
`κ ≈ 113×` for `(p=64, d=16, m=32)` under an iid clipped-ReLU model
are computed in `NTKConcentrationMatrixBernsteinTightened.lean`.

## Main result

* `Matrix.row_covariance_loewner_bound` — the deterministic bridge
  lemma:

  `(X : ι → Matrix (Fin n) (Fin n) ℂ) (R : ℝ) (hR : ∀ i, ‖X i‖ ≤ R)`
  `⊢ ∑ i, X i * (X i)ᴴ ≤ (R^2 * card ι) • 1`

## Proof strategy

For each `i`:

1. `X i * (X i)ᴴ` is positive semidefinite by
   `Matrix.posSemidef_self_mul_conjTranspose`.
2. `X i * (X i)ᴴ ≤ ‖X i * (X i)ᴴ‖ • 1` by
   `Matrix.PosSemidef.le_norm_smul_one_of_isHermitian`.
3. `‖X i * (X i)ᴴ‖ ≤ ‖X i‖ * ‖(X i)ᴴ‖ = ‖X i‖^2 ≤ R^2` via
   `norm_mul_le`, the C⋆-property `‖star A‖ = ‖A‖` on the L2 operator
   norm, and `pow_le_pow_left₀`.
4. Combine (2) and (3) with `Matrix.real_smul_one_le_smul_one` to get
   `X i * (X i)ᴴ ≤ R^2 • 1`.
5. Sum termwise via `Finset.sum_le_sum`, then reshape
   `∑ _, R^2 • 1 = (R^2 * card ι) • 1` using `Finset.sum_const`,
   `nsmul_eq_mul`, `smul_smul`, `mul_comm`.

## References

* J. A. Tropp, *An introduction to matrix concentration inequalities*,
  Foundations and Trends in Machine Learning 8 (2015), §6.1.
* F. Bach, *Learning Theory from First Principles*, MIT Press 2024,
  Chapter 12 (matrix Bernstein for neural-tangent-kernel concentration).
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace Matrix

variable {n : ℕ}

set_option maxHeartbeats 400000 in
/-- **Row-covariance Loewner bound (deterministic bridge lemma).**

For any family `X : ι → Matrix (Fin n) (Fin n) ℂ` with `‖X i‖ ≤ R`
uniformly in `i` (and any nonempty `Fin n`),

  `∑ i, X i * (X i)ᴴ ≤ (R^2 * card ι) • 1`

in the Loewner order on `Matrix (Fin n) (Fin n) ℂ`.

This is the deterministic Loewner-tightening bridge which lets the
matrix Bernstein variance hypothesis
`∑ i, ∫ X i · (X i)ᴴ ∂μ i ≤ σ² • 1` be discharged with a **row-covariance
norm proxy** `σ² := ‖∑ i, ∫ X i · (X i)ᴴ ∂μ i‖` in place of the coarser
scalar proxy `R^2 · card ι`.  See
`NTKConcentrationMatrixBernsteinTightened.lean` for the Bernstein
composition.

Reference: Tropp 2015 §6.1; Bach 2024 §12. -/
theorem row_covariance_loewner_bound
    [Nonempty (Fin n)]
    {ι : Type*} [Fintype ι]
    (X : ι → Matrix (Fin n) (Fin n) ℂ)
    (R : ℝ) (hR : ∀ i, ‖X i‖ ≤ R) :
    (∑ i, X i * (X i)ᴴ)
      ≤ (R ^ 2 * (Fintype.card ι : ℝ)) •
          (1 : Matrix (Fin n) (Fin n) ℂ) := by
  classical
  -- Per-summand bound: for every `i`, `X i * (X i)ᴴ ≤ R^2 • 1`.
  have h_per_summand :
      ∀ i, X i * (X i)ᴴ ≤
        ((R ^ 2 : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
    intro i
    -- (1) `X i * (X i)ᴴ` is PSD.
    have h_psd : (X i * (X i)ᴴ).PosSemidef :=
      Matrix.posSemidef_self_mul_conjTranspose (X i)
    -- (2) Norm-to-Loewner: `X i * (X i)ᴴ ≤ ‖X i * (X i)ᴴ‖ • 1`.
    have h_norm_le : X i * (X i)ᴴ ≤
        (‖X i * (X i)ᴴ‖ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) :=
      h_psd.le_norm_smul_one_of_isHermitian
    -- (3a) Norm of the product: `‖X i * (X i)ᴴ‖ ≤ ‖X i‖ * ‖(X i)ᴴ‖`.
    have h_norm_mul : ‖X i * (X i)ᴴ‖ ≤ ‖X i‖ * ‖(X i)ᴴ‖ :=
      norm_mul_le _ _
    -- (3b) Conj-transpose is an isometry: `‖(X i)ᴴ‖ = ‖X i‖`.
    have h_norm_conj : ‖(X i)ᴴ‖ = ‖X i‖ := by
      -- On `Matrix n n ℂ` under the L2 operator norm, `Aᴴ = star A` and
      -- `star` is an isometry.
      rw [← Matrix.star_eq_conjTranspose]
      exact norm_star _
    -- (3c) So `‖X i * (X i)ᴴ‖ ≤ ‖X i‖^2`.
    have h_sq_bound : ‖X i * (X i)ᴴ‖ ≤ ‖X i‖ ^ 2 := by
      calc ‖X i * (X i)ᴴ‖
          ≤ ‖X i‖ * ‖(X i)ᴴ‖ := h_norm_mul
        _ = ‖X i‖ * ‖X i‖ := by rw [h_norm_conj]
        _ = ‖X i‖ ^ 2 := by ring
    -- (3d) And `‖X i‖^2 ≤ R^2` by monotonicity of `x ↦ x^2` on `[0, ∞)`.
    have h_XR : ‖X i‖ ^ 2 ≤ R ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hR i) 2
    -- Combined: `‖X i * (X i)ᴴ‖ ≤ R^2`.
    have h_norm_R2 : ‖X i * (X i)ᴴ‖ ≤ R ^ 2 := h_sq_bound.trans h_XR
    -- (4) Scalar-to-Loewner monotonicity: `‖⋯‖ • 1 ≤ R^2 • 1`.
    have h_scalar_step :
        (‖X i * (X i)ᴴ‖ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) ≤
          ((R ^ 2 : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℂ) :=
      Matrix.real_smul_one_le_smul_one h_norm_R2
    exact h_norm_le.trans h_scalar_step
  -- (5) Sum termwise, then reshape.
  have h_sum_le :
      (∑ i, X i * (X i)ᴴ) ≤
        ∑ _i : ι, ((R ^ 2 : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℂ) :=
    Finset.sum_le_sum (fun i _ => h_per_summand i)
  -- Reshape the constant sum: `∑ _, c • 1 = (card ι) • (c • 1) = (c * card ι) • 1`.
  have h_sum_const :
      (∑ _i : ι, ((R ^ 2 : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℂ)) =
        (R ^ 2 * (Fintype.card ι : ℝ)) •
          (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [Finset.sum_const, Finset.card_univ]
    -- Nat smul → real smul, then `smul_smul` and `mul_comm`.
    rw [← Nat.cast_smul_eq_nsmul (R := ℝ)
        (Fintype.card ι)
        (((R ^ 2 : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℂ))]
    -- Now goal shape: `(card ι : ℝ) • (R^2 • 1) = (R^2 * card ι) • 1`.
    rw [smul_smul, mul_comm]
  calc (∑ i, X i * (X i)ᴴ)
      ≤ ∑ _i : ι, ((R ^ 2 : ℝ)) • (1 : Matrix (Fin n) (Fin n) ℂ) := h_sum_le
    _ = (R ^ 2 * (Fintype.card ι : ℝ)) •
          (1 : Matrix (Fin n) (Fin n) ℂ) := h_sum_const

end Matrix
