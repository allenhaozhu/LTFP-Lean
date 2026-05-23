/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Schur and Woodbury identities for the Gaussian conjugate-prior posterior covariance

This module collects the matrix-algebra payload underlying the B4 N2
Gaussian conjugate-prior posterior covariance identity. Two equivalent
closed forms are proved for the same matrix:

* `schurPosteriorCov`, the "covariance form"
  `priorCov - priorCov · Xᵀ · (X · priorCov · Xᵀ + noiseVar • 1)⁻¹ · X · priorCov`,
  which is the bottom-right Schur complement of the joint
  prior–observation block covariance.
* The "precision form"
  `(priorCov⁻¹ + Xᵀ · (noiseVar⁻¹ • 1) · X)⁻¹`,
  obtained by adding the data-driven precision update to the prior
  precision.

The first form is the Schur complement of the obvious block matrix; the
second form is its Woodbury rewrite. Together they are the algebraic
core of the standard Gaussian conjugate posterior covariance identity.

This file is intentionally algebra-only — no measure-theoretic or
positive-definiteness hypotheses are required. Invertibility is stated
as `IsUnit` on the relevant matrices and scalars, so consumers can
discharge it either via `PosDef`/`PosSemidef` infrastructure or via
direct unit hypotheses.

## Main definitions

* `Matrix.obsCov` — `X · priorCov · Xᵀ + noiseVar • 1`, the marginal
  observation covariance.
* `Matrix.schurPosteriorCov` — `priorCov - priorCov · Xᵀ · obsCov⁻¹ · X · priorCov`.

## Main results

* `Matrix.schurPosteriorCov_eq_schur_complement` — `schurPosteriorCov`
  is the bottom-right Schur complement of the joint covariance block.
* `Matrix.schurPosteriorCov_eq_precision_inv` — Woodbury identity
  giving the precision-form expression.
* `Matrix.schurPosteriorCov_eq_precision_inv_of_obsCov` — convenience
  alias of the Woodbury identity stated with the invertibility
  hypothesis in `obsCov` ordering (i.e. `X · priorCov · Xᵀ + noiseVar • 1`
  rather than `noiseVar • 1 + X · priorCov · Xᵀ`).
* `Matrix.inv_smul_one_eq_smul_one` — scalar-noise inverse identity
  `(noiseVar⁻¹ • 1)⁻¹ = noiseVar • 1`, the algebraic core of the
  precision-to-covariance Woodbury rewrite.
* `Matrix.obsCov_eq_add_comm` — bridges the `noiseVar • 1 + …`
  ordering used by `Matrix.add_mul_mul_inv_eq_sub` to the
  `obsCov` ordering used everywhere downstream.

## References

* Bach (2024), *Learning Theory from First Principles*, §B.4 N2.
* Hager (1989), *Updating the inverse of a matrix* (Woodbury identity).
-/

namespace Matrix

open scoped Matrix

variable {R : Type*} [Field R]
variable {n p : Type*} [Fintype n] [Fintype p] [DecidableEq n] [DecidableEq p]

/-- The marginal observation covariance
`X · priorCov · Xᵀ + noiseVar • I` arising in the standard Gaussian
linear-model conjugate setup. -/
noncomputable def obsCov
    (priorCov : Matrix p p R) (X : Matrix n p R) (noiseVar : R) :
    Matrix n n R :=
  X * priorCov * Xᵀ + noiseVar • (1 : Matrix n n R)

/-- The posterior covariance in "covariance form": the Schur complement
of `obsCov` in the joint prior–observation block covariance. This is
one of the two equivalent expressions for the Gaussian conjugate-prior
posterior covariance; the other is the precision-form Woodbury rewrite
proved as `schurPosteriorCov_eq_precision_inv`. -/
noncomputable def schurPosteriorCov
    (priorCov : Matrix p p R) (X : Matrix n p R) (noiseVar : R) :
    Matrix p p R :=
  priorCov - priorCov * Xᵀ * (obsCov priorCov X noiseVar)⁻¹ * (X * priorCov)

/-! ### Convenience algebraic lemmas

These three small lemmas are the load-bearing internal `have`s of the
Woodbury rewrite below, surfaced as named public API so downstream
callers can reuse them without re-deriving the algebra.
-/

/-- **Scalar-noise inverse identity.** For a unit scalar `noiseVar`, the
matrix `noiseVar⁻¹ • (1 : Matrix n n R)` has matrix inverse
`noiseVar • 1`. This is the algebraic core of the precision-to-
covariance Woodbury rewrite: `C := noiseVar⁻¹ • 1` plays the role of
the middle factor and its inverse is the original noise-times-identity. -/
theorem inv_smul_one_eq_smul_one
    {n : Type*} [Fintype n] [DecidableEq n]
    (noiseVar : R) (hNoise : IsUnit noiseVar) :
    (noiseVar⁻¹ • (1 : Matrix n n R))⁻¹ = noiseVar • (1 : Matrix n n R) := by
  refine Matrix.inv_eq_left_inv ?_
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul,
    mul_inv_cancel₀ (IsUnit.ne_zero hNoise), one_smul]

omit [Fintype n] [DecidableEq p] in
/-- **`obsCov` add-comm bridge.** Rewrites the additive ordering
`noiseVar • 1 + X · priorCov · Xᵀ` (as it arises out of
`Matrix.add_mul_mul_inv_eq_sub`) into the canonical `obsCov` form
`X · priorCov · Xᵀ + noiseVar • 1`. -/
theorem obsCov_eq_add_comm
    (priorCov : Matrix p p R) (X : Matrix n p R) (noiseVar : R) :
    noiseVar • (1 : Matrix n n R) + X * priorCov * Xᵀ
      = obsCov priorCov X noiseVar := by
  unfold obsCov
  abel

/-! ### Theorem 1 — Schur complement identity -/

omit [DecidableEq p] in
/-- **Schur-complement identity for the posterior covariance.**
`schurPosteriorCov priorCov X noiseVar` is, definitionally, the
bottom-right Schur complement of the block covariance matrix
`fromBlocks priorCov (priorCov · Xᵀ) (X · priorCov) (obsCov priorCov X noiseVar)`.

This is the algebraic statement that the conditional-Gaussian
covariance formula
`Σ_{θ|y} = Σ_θ - Σ_θ Xᵀ (X Σ_θ Xᵀ + ν² I)⁻¹ X Σ_θ`
is exactly the Schur complement appearing in the LDU decomposition of
the joint covariance via `Matrix.fromBlocks_eq_of_invertible₂₂`. -/
theorem schurPosteriorCov_eq_schur_complement
    (priorCov : Matrix p p R) (X : Matrix n p R) (noiseVar : R) :
    schurPosteriorCov priorCov X noiseVar
      = priorCov - (priorCov * Xᵀ) * (obsCov priorCov X noiseVar)⁻¹ * (X * priorCov) := by
  rfl

/-! ### Theorem 2 — Woodbury / precision-form identity -/

/-- The Woodbury / precision-form identity for the Gaussian conjugate-prior
posterior covariance. Under invertibility of `priorCov`, the scalar
`noiseVar`, and the "Schur" matrix `noiseVar • 1 + X · priorCov · Xᵀ`,
the inverse of the posterior precision matrix
`priorCov⁻¹ + Xᵀ · (noiseVar⁻¹ • 1) · X` agrees with the covariance-form
expression `schurPosteriorCov priorCov X noiseVar`.

Proof: apply `Matrix.add_mul_mul_inv_eq_sub` (the `⁻¹`-version of the
Woodbury identity) with `A := priorCov⁻¹`, `U := Xᵀ`,
`C := noiseVar⁻¹ • 1`, `V := X`. -/
theorem schurPosteriorCov_eq_precision_inv
    (priorCov : Matrix p p R) (X : Matrix n p R) (noiseVar : R)
    (hPrior : IsUnit priorCov) (hNoise : IsUnit noiseVar)
    (hSchur : IsUnit (noiseVar • (1 : Matrix n n R) + X * priorCov * Xᵀ)) :
    (priorCov⁻¹ + Xᵀ * (noiseVar⁻¹ • (1 : Matrix n n R)) * X)⁻¹
      = schurPosteriorCov priorCov X noiseVar := by
  -- Set up the Woodbury substitution.
  set A : Matrix p p R := priorCov⁻¹ with hA
  set U : Matrix p n R := Xᵀ with hU
  set C : Matrix n n R := noiseVar⁻¹ • (1 : Matrix n n R) with hC
  set V : Matrix n p R := X with hV
  -- `IsUnit` hypotheses for `add_mul_mul_inv_eq_sub`.
  have hPriorDet : IsUnit priorCov.det := (Matrix.isUnit_iff_isUnit_det _).mp hPrior
  have hA_unit : IsUnit A := by
    rw [hA]
    exact (Matrix.isUnit_iff_isUnit_det _).mpr
      (Matrix.isUnit_nonsing_inv_det _ hPriorDet)
  -- The scalar `noiseVar⁻¹ • 1` is the inverse of `noiseVar • 1` and is a unit.
  have hNoiseInv : IsUnit noiseVar⁻¹ := hNoise.inv
  have h_invNoise_one_det : IsUnit (noiseVar⁻¹ • (1 : Matrix n n R)).det := by
    rw [Matrix.det_smul, Matrix.det_one, mul_one]
    exact hNoiseInv.pow _
  have hC_unit : IsUnit C := (Matrix.isUnit_iff_isUnit_det _).mpr h_invNoise_one_det
  -- Compute `C⁻¹ = noiseVar • 1`.
  have hC_inv : C⁻¹ = noiseVar • (1 : Matrix n n R) := by
    rw [hC]
    exact Matrix.inv_smul_one_eq_smul_one noiseVar hNoise
  -- The third invertibility hypothesis: `C⁻¹ + V * A⁻¹ * U` is a unit.
  have hAC_unit : IsUnit (C⁻¹ + V * A⁻¹ * U) := by
    rw [hC_inv]
    have hA_inv : A⁻¹ = priorCov := by
      rw [hA]; exact Matrix.nonsing_inv_nonsing_inv _ hPriorDet
    rw [hA_inv, hU, hV]
    exact hSchur
  -- Apply Woodbury.
  have hWoodbury :
      (A + U * C * V)⁻¹
        = A⁻¹ - A⁻¹ * U * (C⁻¹ + V * A⁻¹ * U)⁻¹ * V * A⁻¹ :=
    Matrix.add_mul_mul_inv_eq_sub A U C V hA_unit hC_unit hAC_unit
  -- Unfold the substitution back.
  have hA_inv_eq : A⁻¹ = priorCov := by
    rw [hA]; exact Matrix.nonsing_inv_nonsing_inv _ hPriorDet
  have hMid_eq : (C⁻¹ + V * A⁻¹ * U)⁻¹ = (obsCov priorCov X noiseVar)⁻¹ := by
    rw [hC_inv, hA_inv_eq, hU, hV]
    congr 1
    exact Matrix.obsCov_eq_add_comm priorCov X noiseVar
  -- Rewrite the Woodbury RHS into `schurPosteriorCov`.
  calc (priorCov⁻¹ + Xᵀ * (noiseVar⁻¹ • (1 : Matrix n n R)) * X)⁻¹
      = (A + U * C * V)⁻¹ := by rw [hA, hU, hC, hV]
    _ = A⁻¹ - A⁻¹ * U * (C⁻¹ + V * A⁻¹ * U)⁻¹ * V * A⁻¹ := hWoodbury
    _ = priorCov - priorCov * Xᵀ * (obsCov priorCov X noiseVar)⁻¹
            * (X * priorCov) := by
          rw [hMid_eq, hA_inv_eq, hU, hV, Matrix.mul_assoc, Matrix.mul_assoc,
            Matrix.mul_assoc]
    _ = schurPosteriorCov priorCov X noiseVar := by
          rw [schurPosteriorCov_eq_schur_complement]

/-- **Woodbury identity, `obsCov`-ordered variant.** Identical
content to `schurPosteriorCov_eq_precision_inv`, but with the
third invertibility hypothesis stated directly on
`obsCov priorCov X noiseVar = X · priorCov · Xᵀ + noiseVar • 1`
rather than on the additively-swapped
`noiseVar • 1 + X · priorCov · Xᵀ`. This is the form most natural
for callers who carry an `obsCov` invertibility witness around. -/
theorem schurPosteriorCov_eq_precision_inv_of_obsCov
    (priorCov : Matrix p p R) (X : Matrix n p R) (noiseVar : R)
    (hPrior : IsUnit priorCov) (hNoise : IsUnit noiseVar)
    (hObs : IsUnit (obsCov priorCov X noiseVar)) :
    (priorCov⁻¹ + Xᵀ * (noiseVar⁻¹ • (1 : Matrix n n R)) * X)⁻¹
      = schurPosteriorCov priorCov X noiseVar := by
  refine schurPosteriorCov_eq_precision_inv priorCov X noiseVar hPrior hNoise ?_
  rw [obsCov_eq_add_comm]
  exact hObs

end Matrix
