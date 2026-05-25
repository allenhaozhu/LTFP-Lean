/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Matrix relative entropy nonnegativity (Klein-shifted form) — building blocks

For strictly positive complex matrices `P, Q : Matrix n n ℂ`, the matrix
relative entropy in its "shifted" or Klein form satisfies

  `0 ≤ Re tr (P · log P - P · log Q - P + Q)`.

When `tr P = tr Q` (e.g. both `P` and `Q` are density matrices), the
shift `Re tr (Q - P)` vanishes and we recover the usual relative entropy
nonnegativity `Re tr (P · (log P - log Q)) ≥ 0`.

This file establishes the **scalar** and **spectral** building blocks
needed for the matrix entropy proof:

* `CFC.scalar_klein_inequality` — the per-eigenvalue scalar inequality
  `x · log x - x · log y - x + y ≥ 0` for `x, y > 0`.
* `Matrix.trace_mul_log_eq_sum_eigenvalues` — the spectral identity
  `tr (P · log P) = ∑ k, λ_k · log λ_k` for strictly positive `P`,
  reducing the matrix entropy to a sum over `P`'s eigenvalues.
* `Matrix.trace_mul_log_Q_eq_sum_eigenvalues` — the cross-trace
  identity `tr (P · log Q) = ∑ j, P̃_{jj} · log μ_j` where
  `P̃ := U_Q* · P · U_Q` and `μ_j` are `Q`'s eigenvalues.

The remaining piece — Peierls–Bogoliubov applied across the change of
basis between `P`'s and `Q`'s eigenbases — assembles these three
ingredients into the full Klein inequality. That step is a separate
sub-project tracked as Part 3b of the matrix Bernstein chain.

## Proof structure (full theorem, for reference)

Let `λ_k` be eigenvalues of `P`, `μ_j` of `Q`. The full proof chains:

  `tr (P log P) = ∑ k, λ_k log λ_k`                        [spectral identity]
                `≥ ∑ j, ⟨v_j | P v_j⟩ · log ⟨v_j | P v_j⟩`  [Peierls–Bogoliubov]
                `≥ ∑ j, (⟨v_j | P v_j⟩ log μ_j + ⟨v_j | P v_j⟩ - μ_j)`
                                                            [scalar Klein per j]
                `= tr (P log Q) + tr P - tr Q.`             [trace identity in `Q`-basis]

-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace CFC

/-! ## Scalar Klein inequality

The scalar entropy inequality `f(x) := x · log x - x · log y - x + y ≥ 0`
for `x, y > 0`. The proof uses `Real.log_le_sub_one_of_pos` applied at
`z = y/x`. -/

/-- **Scalar Klein inequality.**

For positive reals `x, y > 0`,

  `0 ≤ x · log x - x · log y - x + y`.

This is the per-eigenvalue scalar inequality underlying the matrix
relative entropy nonnegativity. It follows from
`Real.log_le_sub_one_of_pos` applied at `z = y / x`:
`log (y / x) ≤ y / x - 1`, multiplied by `x > 0`. -/
theorem scalar_klein_inequality {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 ≤ x * Real.log x - x * Real.log y - x + y := by
  -- Apply `Real.log_le_sub_one_of_pos` at `y / x`.
  have hyx_pos : 0 < y / x := div_pos hy hx
  have hlog_le : Real.log (y / x) ≤ y / x - 1 :=
    Real.log_le_sub_one_of_pos hyx_pos
  -- `log (y / x) = log y - log x`.
  have hx_ne : x ≠ 0 := ne_of_gt hx
  have hlog_div : Real.log (y / x) = Real.log y - Real.log x :=
    Real.log_div (ne_of_gt hy) hx_ne
  -- Multiply by `x > 0`: `x · (log y - log x) ≤ x · (y / x - 1) = y - x`.
  have hxle : x * (Real.log y - Real.log x) ≤ x * (y / x - 1) := by
    have hmul := mul_le_mul_of_nonneg_left hlog_le (le_of_lt hx)
    -- `x · log (y / x) ≤ x · (y / x - 1)` rewriting via `hlog_div`.
    rw [hlog_div] at hmul
    exact hmul
  -- `x · (y / x - 1) = y - x`.
  have hcancel : x * (y / x - 1) = y - x := by
    field_simp
  -- Combine: `x · log y - x · log x ≤ y - x`.
  have hcombined : x * Real.log y - x * Real.log x ≤ y - x := by
    have hcomb := hxle.trans_eq hcancel
    have heq : x * (Real.log y - Real.log x) = x * Real.log y - x * Real.log x := by
      ring
    linarith
  linarith

end CFC

namespace Matrix

open Finset Unitary
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

/-! ## Spectral identity for `tr (P · CFC.log P)`

For a strictly positive matrix `P`, the trace `tr (P · log P)` (a
complex number a priori) decomposes into the real-valued sum
`∑ k, λ_k · log λ_k` over `P`'s eigenvalues. -/

/-- **Spectral identity for matrix entropy.**

For a strictly positive complex matrix `P`, the trace of `P · log P`
equals the sum of `λ_k · log λ_k` over `P`'s eigenvalues, embedded into
`ℂ`.

This reduces the matrix entropy `tr (P · log P)` to a finite scalar sum
and is the first ingredient of the matrix relative entropy nonnegativity
chain. -/
theorem trace_mul_log_eq_sum_eigenvalues
    {n : Type*} [Fintype n] [DecidableEq n]
    {P : Matrix n n ℂ} (hP : IsStrictlyPositive P)
    (hPH : P.IsHermitian := (Matrix.isStrictlyPositive_iff_posDef.mp hP).isHermitian) :
    Matrix.trace ((P : Matrix n n ℂ) * CFC.log P) =
      ((∑ k, hPH.eigenvalues k * Real.log (hPH.eigenvalues k) : ℝ) : ℂ) := by
  classical
  -- `CFC.log P = hPH.cfc Real.log` via `cfc_eq`.
  have hlog_eq : CFC.log P = hPH.cfc Real.log := by
    rw [CFC.log]
    exact hPH.cfc_eq Real.log
  -- Spectral pieces.
  set U : Matrix.unitaryGroup n ℂ := hPH.eigenvectorUnitary with hU_def
  set DP : Matrix n n ℂ := diagonal (RCLike.ofReal ∘ hPH.eigenvalues) with hDP_def
  set DlogP : Matrix n n ℂ :=
    diagonal (RCLike.ofReal ∘ Real.log ∘ hPH.eigenvalues) with hDlogP_def
  -- `P = U · DP · star U`.
  have hP_eq : P = (U : Matrix n n ℂ) * DP * (star U : Matrix n n ℂ) := by
    simpa [conjStarAlgAut_apply, hDP_def] using hPH.spectral_theorem
  -- `CFC.log P = U · DlogP · star U` via `IsHermitian.cfc`.
  have hlog_P_eq :
      CFC.log P = (U : Matrix n n ℂ) * DlogP * (star U : Matrix n n ℂ) := by
    rw [hlog_eq, IsHermitian.cfc, conjStarAlgAut_apply]
  -- Unitary identity.
  have hUstarU : (star U : Matrix n n ℂ) * (U : Matrix n n ℂ) = 1 :=
    Unitary.coe_star_mul_self U
  -- `P · log P = U · (DP · DlogP) · star U`.
  have hprod_eq :
      (P : Matrix n n ℂ) * CFC.log P
        = (U : Matrix n n ℂ) * (DP * DlogP) * (star U : Matrix n n ℂ) := by
    conv_lhs => rw [hlog_P_eq, hP_eq]
    -- (U DP U*) (U DlogP U*) = U DP (U* U) DlogP U* = U DP DlogP U*.
    set Uc : Matrix n n ℂ := (U : Matrix n n ℂ) with hUc_def
    set Usc : Matrix n n ℂ := (star U : Matrix n n ℂ) with hUsc_def
    show Uc * DP * Usc * (Uc * DlogP * Usc) = Uc * (DP * DlogP) * Usc
    have hUsc_Uc : Usc * Uc = 1 := hUstarU
    calc
      Uc * DP * Usc * (Uc * DlogP * Usc)
          = Uc * DP * (Usc * Uc) * DlogP * Usc := by noncomm_ring
      _ = Uc * DP * 1 * DlogP * Usc := by rw [hUsc_Uc]
      _ = Uc * (DP * DlogP) * Usc := by noncomm_ring
  -- Trace cyclic + unitary cancellation.
  have htrace_eq :
      Matrix.trace ((P : Matrix n n ℂ) * CFC.log P)
        = Matrix.trace (DP * DlogP) := by
    rw [hprod_eq]
    rw [show Matrix.trace ((U : Matrix n n ℂ) * (DP * DlogP) *
              (star U : Matrix n n ℂ))
          = Matrix.trace ((star U : Matrix n n ℂ) * (U : Matrix n n ℂ) *
              (DP * DlogP)) from by rw [Matrix.trace_mul_cycle]]
    rw [hUstarU, Matrix.one_mul]
  -- `DP * DlogP` is diagonal with entries `λ_k * log λ_k` (as `ℂ`).
  have hDP_DlogP_diag :
      DP * DlogP
        = diagonal (fun k =>
            ((hPH.eigenvalues k : ℂ) * (Real.log (hPH.eigenvalues k) : ℂ))) := by
    rw [hDP_def, hDlogP_def, ← Matrix.diagonal_mul_diagonal]
    rfl
  rw [htrace_eq, hDP_DlogP_diag, Matrix.trace_diagonal]
  -- Cast the sum: `∑ k, (λ_k : ℂ) · (log λ_k : ℂ) = ↑(∑ k, λ_k · log λ_k)`.
  have hfun :
      (fun k =>
              (hPH.eigenvalues k : ℂ) * (Real.log (hPH.eigenvalues k) : ℂ))
        = (fun k =>
            ((hPH.eigenvalues k * Real.log (hPH.eigenvalues k) : ℝ) : ℂ)) := by
    funext k
    push_cast
    ring
  rw [hfun, ← Complex.ofReal_sum]

/-! ## Spectral identity for `tr (P · CFC.log Q)` in the `Q`-basis

For strictly positive `Q`, the trace `tr (P · log Q)` equals the
weighted sum `∑ j, P̃_{jj} · log μ_j` where `μ_j` are `Q`'s eigenvalues,
`U_Q` is `Q`'s eigenvector unitary, and `P̃ := U_Q* · P · U_Q`. -/

/-- **Spectral identity for the cross-trace `tr (P · log Q)`.**

For any matrix `P` and strictly positive `Q`, the trace of `P · log Q`
equals the weighted sum `∑ j, P̃_{jj} · log μ_j` over `Q`'s eigenvalues
`μ_j`, where `P̃ := U_Q* · P · U_Q` is `P` expressed in `Q`'s eigenbasis.

The diagonal entries `P̃_{jj}` are real and nonnegative when `P` is
positive semidefinite. -/
theorem trace_mul_log_Q_eq_sum_eigenvalues
    {n : Type*} [Fintype n] [DecidableEq n]
    (P : Matrix n n ℂ) {Q : Matrix n n ℂ} (hQ : IsStrictlyPositive Q)
    (hQH : Q.IsHermitian := (Matrix.isStrictlyPositive_iff_posDef.mp hQ).isHermitian) :
    Matrix.trace ((P : Matrix n n ℂ) * CFC.log Q) =
      ∑ j, ((star (hQH.eigenvectorUnitary : Matrix n n ℂ)) * P *
              (hQH.eigenvectorUnitary : Matrix n n ℂ)) j j *
            ((Real.log (hQH.eigenvalues j) : ℂ)) := by
  classical
  -- `CFC.log Q = U_Q · diag(log μ_j) · star U_Q`.
  have hlog_eq : CFC.log Q = hQH.cfc Real.log := by
    rw [CFC.log]
    exact hQH.cfc_eq Real.log
  set V : Matrix n n ℂ := (hQH.eigenvectorUnitary : Matrix n n ℂ) with hV_def
  set Vs : Matrix n n ℂ := (star hQH.eigenvectorUnitary : Matrix n n ℂ) with hVs_def
  set DlogQ : Matrix n n ℂ :=
    diagonal (RCLike.ofReal ∘ Real.log ∘ hQH.eigenvalues) with hDlogQ_def
  have hlog_Q_eq : CFC.log Q = V * DlogQ * Vs := by
    rw [hlog_eq, IsHermitian.cfc, conjStarAlgAut_apply]
  -- Substitute and cyclic the trace: `tr(P · V · D · V*) = tr((V* · P · V) · D)`.
  have htrace_eq :
      Matrix.trace ((P : Matrix n n ℂ) * CFC.log Q)
        = Matrix.trace (Vs * P * V * DlogQ) := by
    rw [hlog_Q_eq]
    -- tr(P · V · DlogQ · Vs) = tr(Vs · P · V · DlogQ) by cycling.
    have heq1 :
        P * (V * DlogQ * Vs) = (P * V * DlogQ) * Vs := by noncomm_ring
    rw [heq1]
    have heq2 :
        Matrix.trace ((P * V * DlogQ) * Vs)
          = Matrix.trace (Vs * (P * V * DlogQ)) := by
      rw [Matrix.trace_mul_comm]
    rw [heq2]
    congr 1
    noncomm_ring
  -- Now `tr ((V* P V) · DlogQ) = Σ j, (V* P V) j j · (log μ_j)` since DlogQ
  -- is diagonal.
  rw [htrace_eq]
  -- Use `Matrix.trace_diagonal` after rewriting `(M * diagonal d) i i = M i i * d i`.
  rw [Matrix.trace]
  simp only [Matrix.diag_apply]
  apply Finset.sum_congr rfl
  intro j _
  -- `(Vs * P * V * DlogQ) j j = (Vs * P * V) j j * (Real.log (hQH.eigenvalues j) : ℂ)`.
  rw [hDlogQ_def, Matrix.mul_apply, Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    have : (diagonal (RCLike.ofReal ∘ Real.log ∘ hQH.eigenvalues) : Matrix n n ℂ) k j = 0 := by
      simp [hkj]
    rw [this, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Matrix
