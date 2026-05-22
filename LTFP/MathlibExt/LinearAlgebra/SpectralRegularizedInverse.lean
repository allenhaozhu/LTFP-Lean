/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Spectral form of the regularized-inverse trace identity

For a real positive-definite matrix `A : Matrix d d ℝ` and a strictly
positive regularization parameter `lam : ℝ`, the trace of
`(A + lam • 1)⁻¹ * A` decomposes diagonally in the eigenbasis of `A`:
```
trace ((A + lam • 1)⁻¹ * A) = ∑ i, eig i / (eig i + lam)
```
where `eig i = hA.1.eigenvalues i` are the eigenvalues of `A`.

This is **Step 2-impl** of the B4 Node 3 implementation plan
(`LTFP/MathlibExt/LinearAlgebra/SpectralSpike.lean`, the budget-
assessment companion left as a `sorry`-shelved skeleton). It is the
load-bearing identity used by the general-`Σ̂` Bach §3.7 lower bound:
in the limit `lam → 0` the right-hand side becomes
`∑ i, 1 = Fintype.card d`, recovering the inverse-limit carrier from
`LTFP.MathlibExt.LinearAlgebra.MatrixInverseLimit` but exposing the
per-eigenvalue Bayes-risk structure en route.

## Proof outline

1. Spectral decomposition: `A = U * D * star U` with
   `D = diagonal (eig)` (the `RCLike.ofReal` factors collapse via
   `RCLike.ofReal_real_eq_id` because `𝕜 = ℝ`).
2. Compatibility: `A + lam • 1 = U * diagonal (eig + const lam) * star U`,
   using that conjugation by a unitary preserves the algebra structure
   and that `lam • 1 = diagonal (fun _ => lam)`.
3. Inversion: under the local conjugation-inverse lemma
   `conjStarAlgAut_matrix_inv` (a candidate for upstream PR — see the
   notes below), this yields
   `(A + lam • 1)⁻¹ = U * diagonal ((eig + const lam)⁻¹) * star U`.
4. Diagonal product: `(A + lam • 1)⁻¹ * A` collapses to
   `U * diagonal (eig / (eig + const lam)) * star U`.
5. Trace: `trace_mul_cycle` + `Unitary.coe_star_mul_self` peel off the
   unitary, and `trace_diagonal` closes the sum.

## Codex pre-audit patches applied

* `RCLike.ofReal_id` does not exist in pinned Mathlib; we use the real
  name `RCLike.ofReal_real_eq_id` (`Analysis/RCLike/Basic.lean:1002`).
* Generic `map_inv` does NOT discharge matrix `⁻¹` through a
  `StarAlgEquiv` (matrix inverse is not the group inverse). We prove a
  local `conjStarAlgAut_matrix_inv` instead, via
  `Matrix.inv_eq_right_inv`.
* No `PosDef.add_const_smul_invertible` exists; invertibility of
  `A + lam • 1` is routed through positive-definiteness of the
  diagonal `eig + const lam` and `Matrix.isUnit_diagonal`.
-/

namespace LTFP.MathlibExt.LinearAlgebra

open Matrix Unitary

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- **Local lemma (PR candidate).** Conjugation by a unitary commutes
with the nonsingular matrix inverse: for `U : unitaryGroup d ℝ` and
`X : Matrix d d ℝ` with `IsUnit X.det`,
`(U * X * star U)⁻¹ = U * X⁻¹ * star U`.

This is the matrix-`⁻¹` analogue of the algebra-`Inv` `map_inv` lemma
which does NOT apply here (matrix nonsingular inverse is not a
group inverse). -/
private lemma conjStarAlgAut_matrix_inv
    (U : unitaryGroup d ℝ) (X : Matrix d d ℝ) (hX : IsUnit X.det) :
    (conjStarAlgAut ℝ (Matrix d d ℝ) U X)⁻¹ =
      conjStarAlgAut ℝ (Matrix d d ℝ) U X⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [← map_mul, Matrix.mul_nonsing_inv X hX, map_one]

/-- **Step 2-impl (B4 Node 3).** Spectral form of the regularized-
inverse trace identity:
```
trace ((A + lam • 1)⁻¹ * A) = ∑ i, eig i / (eig i + lam)
```
for a real positive-definite `A`, with `eig` the eigenvalues of `A`
and `0 < lam`.

The result is `0 ≤ lam`-compatible for free (the proof only uses
`0 < eig i + lam`, which follows from `0 < eig i` alone when
`0 ≤ lam`), but we state the strict version since the B4 Node 3
downstream `lam → 0⁺` continuity argument has strict positivity at
every fixed `lam`. -/
theorem trace_regularized_inv_mul_eq_eigenvalue_sum
    (A : Matrix d d ℝ) (hA : A.PosDef) {lam : ℝ} (hlam : 0 < lam) :
    ((A + lam • (1 : Matrix d d ℝ))⁻¹ * A).trace
      = ∑ i, hA.1.eigenvalues i / (hA.1.eigenvalues i + lam) := by
  classical
  -- Shorthands.
  set U : unitaryGroup d ℝ := hA.1.eigenvectorUnitary with hU_def
  set eig : d → ℝ := hA.1.eigenvalues with heig_def
  -- Step 1: spectral decomposition of `A` (RCLike.ofReal collapses to id over ℝ).
  have h_spec : A = conjStarAlgAut ℝ (Matrix d d ℝ) U (diagonal eig) := by
    have := hA.1.spectral_theorem
    -- `(↑) ∘ eig = id ∘ eig = eig` because `(↑ : ℝ → ℝ) = id`.
    simpa [Function.comp_def, RCLike.ofReal_real_eq_id, hU_def, heig_def] using this
  -- Step 2: `lam • 1 = U * (diagonal (const lam)) * star U`.
  have h_smul_one :
      (lam • (1 : Matrix d d ℝ)) =
        conjStarAlgAut ℝ (Matrix d d ℝ) U (diagonal (fun _ : d => lam)) := by
    -- `conjStarAlgAut U (lam • 1) = lam • (conjStarAlgAut U 1) = lam • 1`.
    have h₁ : conjStarAlgAut ℝ (Matrix d d ℝ) U (lam • (1 : Matrix d d ℝ)) =
        lam • (1 : Matrix d d ℝ) := by
      rw [map_smul, map_one]
    rw [← h₁, Matrix.smul_one_eq_diagonal]
  -- Step 3: combine to express `A + lam • 1` as conjugation of a diagonal.
  have h_sum :
      A + lam • (1 : Matrix d d ℝ) =
        conjStarAlgAut ℝ (Matrix d d ℝ) U (diagonal (fun i => eig i + lam)) := by
    rw [h_spec, h_smul_one, ← map_add]
    congr 1
    rw [← Matrix.diagonal_add]
  -- Step 4: invertibility of the diagonal (via `det_diagonal` and positivity).
  have h_pos : ∀ i, 0 < eig i + lam := fun i =>
    add_pos (hA.eigenvalues_pos i) hlam
  have h_ne : ∀ i, eig i + lam ≠ 0 := fun i => (h_pos i).ne'
  have h_det_ne : (diagonal (fun i => eig i + lam)).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => h_ne i)
  have h_diag_det_unit : IsUnit (diagonal (fun i => eig i + lam)).det :=
    isUnit_iff_ne_zero.mpr h_det_ne
  -- Step 5a: inverse of the diagonal matrix, by direct check.
  have h_diag_inv :
      (diagonal (fun i => eig i + lam))⁻¹ =
        diagonal (fun i => (eig i + lam)⁻¹) := by
    apply Matrix.inv_eq_right_inv
    rw [Matrix.diagonal_mul_diagonal,
        show (fun i => (eig i + lam) * (eig i + lam)⁻¹) = (fun _ : d => (1 : ℝ))
          from funext fun i => mul_inv_cancel₀ (h_ne i),
        Matrix.diagonal_one]
  -- Step 5b: invert through the conjugation.
  have h_inv :
      (A + lam • (1 : Matrix d d ℝ))⁻¹ =
        conjStarAlgAut ℝ (Matrix d d ℝ) U (diagonal (fun i => (eig i + lam)⁻¹)) := by
    rw [h_sum, conjStarAlgAut_matrix_inv U _ h_diag_det_unit, h_diag_inv]
  -- Step 6: multiply through and collapse the diagonal product.
  have h_prod :
      (A + lam • (1 : Matrix d d ℝ))⁻¹ * A =
        conjStarAlgAut ℝ (Matrix d d ℝ) U
          (diagonal (fun i => eig i / (eig i + lam))) := by
    rw [h_inv, h_spec, ← map_mul]
    congr 1
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [mul_comm, ← div_eq_mul_inv]
  -- Step 7: trace via cyclic move and the unitary cancellation.
  rw [h_prod]
  -- Unfold conjugation: `U * D * star U`.
  rw [conjStarAlgAut_apply, Matrix.trace_mul_cycle]
  -- `star U * U = 1`.
  rw [Unitary.coe_star_mul_self, Matrix.one_mul]
  -- `trace (diagonal f) = ∑ i, f i`.
  rw [Matrix.trace_diagonal]

end LTFP.MathlibExt.LinearAlgebra
