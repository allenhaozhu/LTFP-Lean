/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Hermitian regularized inverse and Bayes-risk trace identity

For a Hermitian matrix `M : Matrix n n ℂ` with eigenvalues all distinct
from `-lam`, the regularized inverse `(M + lam • 1)⁻¹` admits the
explicit diagonalization
`U * diagonal (fun i => (eigᵢ + lam)⁻¹) * star U`,
where `U = M.eigenvectorUnitary` is the unitary of eigenvectors. As a
corollary, the trace identity
`tr((M + lam • 1)⁻¹ * M) = ∑ i, eigᵢ / (eigᵢ + lam)`
holds for positive-definite `M` and non-negative `lam`.

This module is the spectral companion of
`LTFP.MathlibExt.LinearAlgebra.MatrixInverseLimit`, which discharges the
limit `(M + lam • 1)⁻¹ * M → 1` as `lam → 0` via the inverse-continuity
route (without exposing the per-eigenvalue structure). The eigenvalue
sum form proven here is what Bach (2024), *Learning Theory from First
Principles*, §3.7 (pp. 60–62) uses to write the Bayes excess risk for
ridge regression as
`E[‖X β̂_ridge − Xθ‖² / n] = σ² / n · tr((Σ̂ + λI)⁻¹ Σ̂)`.

## Main results

* `Matrix.IsHermitian.regularizedInv_eq_conj_diagonal`
  — explicit diagonalization of the regularized inverse for Hermitian
  `M` and any `lam` with `eigᵢ + lam ≠ 0`.
* `Matrix.IsHermitian.regularizedInv_eq_conj_diagonal_of_posDef`
  — specialization to positive-definite `M` and `0 ≤ lam`, where the
  unit hypothesis is automatic from `PosDef.eigenvalues_pos`.
* `Matrix.IsHermitian.trace_regularizedInv_mul_eq_eigenvalue_sum`
  — the Bayes-risk trace identity
  `tr((M + lam • 1)⁻¹ * M) = ∑ i, eigᵢ / (eigᵢ + lam)` for `PosDef M`
  and `0 ≤ lam`.

## Implementation notes

The diagonalization proof is verbatim from a Codex peer-review session
(2026-05-22) that verified clean against pinned Mathlib commit
`80732f7660`. The trace identity follows the same six-step chain used
by `Matrix.PosSemidef.trace_eq_zero_iff` in `Analysis/Matrix/PosDef.lean`:
`spectral_theorem → conjStarAlgAut_apply → trace_mul_cycle →
Unitary.coe_star_mul_self → trace_diagonal`.

## Follow-up (not in this module)

* Real-symmetric specialization (`Matrix n n ℝ` directly, without the
  `ℂ` coercion) and wiring into the LTFP Bach §3.7 carrier
  (`LTFP/Ch03_LinearLeastSquares/FixedDesign.lean`) are deferred. The
  identity proven here over `ℂ` is sufficient for the spectral lift of
  Node 3; the downstream `gaussianBayesRiskScalar_eq` plug-in is the
  next dispatch.
-/

namespace Matrix.IsHermitian

noncomputable section

open Matrix Unitary
open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Explicit diagonalization of the regularized inverse `(M + lam • 1)⁻¹`
for a Hermitian matrix `M` over `𝕜 ∈ {ℝ, ℂ}` (any `RCLike` field), when
every shifted eigenvalue `eigᵢ + lam` is non-zero (so the inverse
exists). -/
theorem regularizedInv_eq_conj_diagonal
    {𝕜 : Type*} [RCLike 𝕜]
    {M : Matrix n n 𝕜} (hM : M.IsHermitian) (lam : ℝ)
    (h_pos : ∀ i, hM.eigenvalues i + lam ≠ 0) :
    (M + (lam : 𝕜) • (1 : Matrix n n 𝕜))⁻¹
      = (hM.eigenvectorUnitary : Matrix n n 𝕜) *
        diagonal (fun i => ((hM.eigenvalues i : 𝕜) + lam)⁻¹) *
        star (hM.eigenvectorUnitary : Matrix n n 𝕜) := by
  classical
  let U : Matrix.unitaryGroup n 𝕜 := hM.eigenvectorUnitary
  let D : Matrix n n 𝕜 := diagonal (fun i => (hM.eigenvalues i : 𝕜))
  let E : Matrix n n 𝕜 :=
    diagonal (fun i => ((hM.eigenvalues i : 𝕜) + (lam : 𝕜)))
  have hspec : M = (U : Matrix n n 𝕜) * D * star (U : Matrix n n 𝕜) := by
    rw [hM.spectral_theorem]
    simp [U, D, Unitary.conjStarAlgAut_apply, Function.comp_def]
  have hE : E = D + (lam : 𝕜) • (1 : Matrix n n 𝕜) := by
    rw [Matrix.smul_one_eq_diagonal (lam : 𝕜)]
    simp [E, D, Matrix.diagonal_add]
  have hreg :
      M + (lam : 𝕜) • (1 : Matrix n n 𝕜)
        = (U : Matrix n n 𝕜) * E * star (U : Matrix n n 𝕜) := by
    rw [hspec, hE]
    simp [mul_add, add_mul, Matrix.mul_assoc]
  have hUinv : ((U : Matrix n n 𝕜)⁻¹) = star (U : Matrix n n 𝕜) := by
    exact Matrix.inv_eq_left_inv (by simp)
  have hstarUinv : (star (U : Matrix n n 𝕜))⁻¹ = (U : Matrix n n 𝕜) := by
    exact Matrix.inv_eq_left_inv (by simp)
  have hEinv : E⁻¹ = diagonal (fun i => ((hM.eigenvalues i : 𝕜) + lam)⁻¹) := by
    let f : n → 𝕜 := fun i => ((hM.eigenvalues i : 𝕜) + (lam : 𝕜))
    have hfunit : IsUnit f := by
      rw [Pi.isUnit_iff]
      intro i
      rw [isUnit_iff_ne_zero]
      dsimp [f]
      exact_mod_cast h_pos i
    dsimp [E]
    rw [Matrix.inv_diagonal]
    change diagonal (Ring.inverse f) = diagonal (fun i => (f i)⁻¹)
    congr 1
    rw [Ring.inverse_of_isUnit hfunit]
    ext i
    simp [f, IsUnit.val_inv_apply]
  rw [hreg, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hUinv, hstarUinv, hEinv]
  simp [Matrix.mul_assoc, U]

/-- Positive-definite specialization of `regularizedInv_eq_conj_diagonal`
for the complex case: if `M : Matrix n n ℂ` is positive definite and
`0 ≤ lam`, every `eigᵢ + lam` is positive (hence non-zero), so the unit
hypothesis is automatic. -/
theorem regularizedInv_eq_conj_diagonal_of_posDef
    (M : Matrix n n ℂ) (hPos : M.PosDef) (lam : ℝ) (hlam : 0 ≤ lam) :
    (M + (lam : ℂ) • (1 : Matrix n n ℂ))⁻¹
      = (hPos.1.eigenvectorUnitary : Matrix n n ℂ) *
        diagonal (fun i => ((hPos.1.eigenvalues i : ℂ) + lam)⁻¹) *
        star (hPos.1.eigenvectorUnitary : Matrix n n ℂ) := by
  apply Matrix.IsHermitian.regularizedInv_eq_conj_diagonal hPos.1 lam
  intro i
  have hpos : 0 < hPos.1.eigenvalues i := hPos.eigenvalues_pos i
  have hsum : (0 : ℝ) < hPos.1.eigenvalues i + lam := by linarith
  exact ne_of_gt hsum

end

end Matrix.IsHermitian

noncomputable section

open Matrix Unitary
open scoped ComplexOrder

/-- **Bayes-risk trace identity (complex form).**
For a positive-definite Hermitian matrix `M` and any `0 ≤ lam`,
`tr((M + lam • 1)⁻¹ * M) = ∑ i, eigᵢ / (eigᵢ + lam)`.

This is the key linear-algebra reduction in Bach (2024) §3.7: the Bayes
excess risk for ridge regression under a Gaussian prior on `θ` rewrites
as a per-eigenvalue sum, exposing the bias-variance balance at the
spectral level. -/
theorem Matrix.IsHermitian.trace_regularizedInv_mul_eq_eigenvalue_sum
    {𝕜 : Type*} [RCLike 𝕜]
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n 𝕜) (hM : M.IsHermitian) (hPos : M.PosDef)
    (lam : ℝ) (hlam : 0 ≤ lam) :
    ((M + (lam : 𝕜) • (1 : Matrix n n 𝕜))⁻¹ * M).trace
      = ∑ i, ((hM.eigenvalues i : 𝕜)) / ((hM.eigenvalues i : 𝕜) + lam) := by
  classical
  have h_pos_shift : ∀ i, (0 : ℝ) < hM.eigenvalues i + lam := by
    intro i
    have hEq : hM.eigenvalues i = hPos.1.eigenvalues i := by
      congr
    rw [hEq]
    have := hPos.eigenvalues_pos i
    linarith
  have h_ne_shift_real : ∀ i, hM.eigenvalues i + lam ≠ 0 := by
    intro i
    exact ne_of_gt (h_pos_shift i)
  have h_inv :
      (M + (lam : 𝕜) • (1 : Matrix n n 𝕜))⁻¹
        = (hM.eigenvectorUnitary : Matrix n n 𝕜) *
          diagonal (fun i => ((hM.eigenvalues i : 𝕜) + lam)⁻¹) *
          star (hM.eigenvectorUnitary : Matrix n n 𝕜) :=
    Matrix.IsHermitian.regularizedInv_eq_conj_diagonal hM lam h_ne_shift_real
  have h_M : (hM.eigenvectorUnitary : Matrix n n 𝕜) *
        diagonal ((↑) ∘ hM.eigenvalues : n → 𝕜) *
        star (hM.eigenvectorUnitary : Matrix n n 𝕜) = M := by
    have := hM.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this.symm
  set U : Matrix n n 𝕜 := (hM.eigenvectorUnitary : Matrix n n 𝕜) with hU_def
  set Dinv : Matrix n n 𝕜 :=
    diagonal (fun i => ((hM.eigenvalues i : 𝕜) + lam)⁻¹) with hDinv_def
  set D : Matrix n n 𝕜 :=
    diagonal ((↑) ∘ hM.eigenvalues : n → 𝕜) with hD_def
  have h_prod :
      (M + (lam : 𝕜) • (1 : Matrix n n 𝕜))⁻¹ * M
        = U * (Dinv * D) * star U := by
    rw [h_inv, ← h_M]
    have hstarU_U : star U * U = 1 := by
      simp [U,
        Unitary.coe_star_mul_self
          (hM.eigenvectorUnitary : Matrix.unitaryGroup n 𝕜)]
    calc
      (U * Dinv * star U) * (U * D * star U)
          = U * Dinv * (star U * U) * D * star U := by
              simp [Matrix.mul_assoc]
      _ = U * Dinv * 1 * D * star U := by rw [hstarU_U]
      _ = U * Dinv * D * star U := by simp [Matrix.mul_assoc]
      _ = U * (Dinv * D) * star U := by simp [Matrix.mul_assoc]
  have h_starU_U : star U * U = 1 := by
    simp [U,
      Unitary.coe_star_mul_self
        (hM.eigenvectorUnitary : Matrix.unitaryGroup n 𝕜)]
  have h_trace_peel :
      (U * (Dinv * D) * star U).trace = (Dinv * D).trace := by
    rw [Matrix.trace_mul_cycle, ← Matrix.mul_assoc, h_starU_U, Matrix.one_mul]
  have h_diag_prod :
      Dinv * D = diagonal (fun i =>
        ((hM.eigenvalues i : 𝕜) + lam)⁻¹ * (hM.eigenvalues i : 𝕜)) := by
    rw [hDinv_def, hD_def, Matrix.diagonal_mul_diagonal]
    rfl
  rw [h_prod, h_trace_peel, h_diag_prod, Matrix.trace_diagonal]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [mul_comm]
  exact (div_eq_mul_inv _ _).symm

/-- **Bayes-risk trace identity (real form).**
Real-symmetric specialization of
`Matrix.IsHermitian.trace_regularizedInv_mul_eq_eigenvalue_sum`.

For a positive-definite (hence symmetric) real matrix `M` and any
`0 ≤ lam`, the trace of `(M + lam • 1)⁻¹ * M` equals the per-eigenvalue
sum `∑ i, eigᵢ / (eigᵢ + lam)`. This is the form consumed by Bach
(2024) §3.7's Bayes excess-risk identity for ridge regression. -/
theorem Matrix.trace_regularizedInv_mul_eq_eigenvalue_sum_real
    {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) (hPos : M.PosDef) (lam : ℝ) (hlam : 0 ≤ lam) :
    ((M + lam • (1 : Matrix n n ℝ))⁻¹ * M).trace
      = ∑ i, hPos.1.eigenvalues i / (hPos.1.eigenvalues i + lam) := by
  simpa only [RCLike.ofReal_real_eq_id] using
    Matrix.IsHermitian.trace_regularizedInv_mul_eq_eigenvalue_sum
      (𝕜 := ℝ) M hPos.1 hPos lam hlam

end
