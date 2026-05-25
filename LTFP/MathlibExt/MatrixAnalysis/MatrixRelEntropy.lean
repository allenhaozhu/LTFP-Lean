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
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

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

/-! ## Peierls–Bogoliubov inequality for `x log x`

For a strictly positive matrix `P` and any unitary `V`, the diagonal of
the unitary-conjugate `V* · P · V` is "more spread out" than `P`'s
spectrum in the sense of Jensen's inequality applied to the convex
function `x · log x`:

  `∑ j, P̃_jj · log P̃_jj  ≤  Re tr(P · log P)`

where `P̃ := V* · P · V`.

This is the missing link between the scalar Klein inequality and the
matrix relative entropy nonnegativity. The proof uses:
1. Spectral decomposition `P = U · D_P · U*` (Mathlib's
   `IsHermitian.spectral_theorem`).
2. Doubly-stochastic matrix `w_{jk} := ‖W_{jk}‖²` where `W := V* · U`.
3. Finite-form Jensen `ConvexOn.map_sum_le` for `Real.convexOn_mul_log`.
4. Row/column unit sums from `W · star W = 1` and `star W · W = 1`. -/

/-- **Peierls–Bogoliubov inequality** (`x · log x` form).

For a strictly positive complex matrix `P` and any unitary `V`,

  `∑ j, ((V* · P · V) j j).re · log ((V* · P · V) j j).re
        ≤ Re tr(P · log P)`.

In words: pre-composing with any unitary diagonal extraction lowers the
matrix "Shannon-style" entropy `tr (P · log P)` (the eigenvalue case is
equality when `V` is `P`'s eigenvector matrix). This is the spectral
ingredient that, combined with the scalar Klein inequality, yields the
full matrix relative entropy nonnegativity. -/
theorem peierls_bogoliubov_mul_log
    {n : Type*} [Fintype n] [DecidableEq n]
    {P : Matrix n n ℂ} (hP : IsStrictlyPositive P)
    (V : Matrix.unitaryGroup n ℂ) :
    ∑ j, ((star (V : Matrix n n ℂ) * P * (V : Matrix n n ℂ)) j j).re *
        Real.log (((star (V : Matrix n n ℂ) * P * (V : Matrix n n ℂ)) j j).re) ≤
      (Matrix.trace (P * CFC.log P)).re := by
  classical
  -- Spectral pieces for `P`.
  have hPd : P.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp hP
  have hPH : P.IsHermitian := hPd.isHermitian
  set U : Matrix n n ℂ := (hPH.eigenvectorUnitary : Matrix n n ℂ) with hU_def
  set Us : Matrix n n ℂ := (star hPH.eigenvectorUnitary : Matrix n n ℂ) with hUs_def
  -- Eigenvalues of `P`.
  set lam : n → ℝ := hPH.eigenvalues with hlam_def
  have hlam_pos : ∀ k, 0 < lam k := fun k => hPd.eigenvalues_pos k
  have hlam_nn : ∀ k, 0 ≤ lam k := fun k => (hlam_pos k).le
  -- `P = U · D_P · U*` and `U* · U = 1`, `U · U* = 1`.
  set DP : Matrix n n ℂ := diagonal (RCLike.ofReal ∘ lam) with hDP_def
  have hP_eq : P = U * DP * Us := by
    simpa [conjStarAlgAut_apply, hDP_def, hU_def, hUs_def] using hPH.spectral_theorem
  have hUsU : Us * U = 1 := Unitary.coe_star_mul_self hPH.eigenvectorUnitary
  have hUUs : U * Us = 1 := Unitary.coe_mul_star_self hPH.eigenvectorUnitary
  -- The unitary `V` as a matrix.
  set Vm : Matrix n n ℂ := (V : Matrix n n ℂ) with hVm_def
  set Vms : Matrix n n ℂ := (star V : Matrix n n ℂ) with hVms_def
  have hVmsVm : Vms * Vm = 1 := Unitary.coe_star_mul_self V
  have hVmVms : Vm * Vms = 1 := Unitary.coe_mul_star_self V
  -- Define `W := Vms · U` (which is unitary).
  set W : Matrix n n ℂ := Vms * U with hW_def
  -- `star W = star U · star Vms = star U · Vm = Us · Vm`. We use this expansion directly.
  -- Compute `(Vms · P · Vm) j j` in the `U`-basis.
  -- Step 1: `Vms · P · Vm = W · DP · star W` where `W := Vms · U`.
  have hVPV_eq : Vms * P * Vm = W * DP * (star W) := by
    -- substitute `P = U · DP · Us`
    -- `Vms · (U · DP · Us) · Vm = (Vms · U) · DP · (Us · Vm)`.
    -- And `star W = star (Vms · U) = star U · star Vms = Us · Vm` (since star is involutive
    -- on `Vms`).
    have hstarW : star W = Us * Vm := by
      show star (Vms * U) = Us * Vm
      rw [star_mul, show star Vms = Vm from by
        show star (star (V : Matrix n n ℂ)) = (V : Matrix n n ℂ)
        exact star_star _]
    rw [hstarW, hW_def, hP_eq]
    noncomm_ring
  -- Now expand `(W · DP · star W) j j` entry-wise. Since DP is diagonal:
  -- `(W · DP · star W) j j = Σ k, W j k · (lam k : ℂ) · (star W) k j`.
  -- Also `(star W) k j = star (W j k)`.
  -- So `(W · DP · star W) j j = Σ k, (lam k : ℂ) · (W j k * star (W j k))`
  --                            = Σ k, (lam k : ℂ) · ‖W j k‖² (coerced).
  -- Define the real weights `w j k := ‖W j k‖²`.
  set wt : n → n → ℝ := fun j k => ‖W j k‖ ^ 2 with hwt_def
  -- Each weight is nonneg.
  have hwt_nn : ∀ j k, 0 ≤ wt j k := fun j k => by
    simp [hwt_def]
  -- Pointwise identity: `(Vms · P · Vm) j j = ↑(∑ k, wt j k * lam k) : ℂ`.
  have hVPV_diag :
      ∀ j, (Vms * P * Vm) j j
            = ((∑ k, wt j k * lam k : ℝ) : ℂ) := by
    intro j
    rw [hVPV_eq]
    -- `(W * DP * star W) j j` expansion.
    -- Use `Matrix.mul_apply` twice.
    rw [show (W * DP * star W) j j
          = ∑ k, (W * DP) j k * (star W) k j from Matrix.mul_apply]
    -- And `(W * DP) j k = ∑ a, W j a * DP a k = W j k * (lam k : ℂ)` since DP is diagonal.
    have hWDP : ∀ k, (W * DP) j k = W j k * ((lam k : ℂ)) := by
      intro k
      rw [show (W * DP) j k = ∑ a, W j a * DP a k from Matrix.mul_apply]
      rw [Finset.sum_eq_single k]
      · simp [hDP_def, Matrix.diagonal_apply_eq]
      · intro a _ hak
        simp [hDP_def, Matrix.diagonal_apply_ne _ hak]
      · intro h
        exact absurd (Finset.mem_univ k) h
    -- Now simplify the sum.
    have hstarW_app : ∀ k, (star W) k j = star (W j k) := by
      intro k
      rfl
    have hexpand :
        (∑ k, (W * DP) j k * (star W) k j)
          = ∑ k, ((wt j k : ℂ) * (lam k : ℂ)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [hWDP k, hstarW_app k]
      -- W j k * (lam k : ℂ) * star (W j k) = (lam k : ℂ) * (W j k * star (W j k))
      --                                     = (lam k : ℂ) * ‖W j k‖² (coerced).
      have hnorm : W j k * star (W j k) = ((‖W j k‖ ^ 2 : ℝ) : ℂ) := by
        -- For ℂ: `z * conj z = ‖z‖²` (where RHS is via algebra ℝ → ℂ).
        have hmc := RCLike.mul_conj (W j k)
        -- For ℂ, `star = conj`.
        have hstar_eq : star (W j k) = (starRingEnd ℂ) (W j k) := rfl
        rw [hstar_eq, hmc]
        norm_cast
      calc
        W j k * (lam k : ℂ) * star (W j k)
            = (lam k : ℂ) * (W j k * star (W j k)) := by ring
        _ = (lam k : ℂ) * ((‖W j k‖ ^ 2 : ℝ) : ℂ) := by rw [hnorm]
        _ = ((wt j k : ℂ) * (lam k : ℂ)) := by
              simp [hwt_def]; ring
    rw [hexpand]
    -- Cast sum: `∑ k, ((wt j k : ℂ) * (lam k : ℂ)) = ((∑ k, wt j k * lam k : ℝ) : ℂ)`.
    push_cast
    rfl
  -- Pull out the `.re` of the diagonal entry.
  have hVPV_diag_re :
      ∀ j, ((Vms * P * Vm) j j).re = ∑ k, wt j k * lam k := by
    intro j
    rw [hVPV_diag j]
    simp
  -- Now compute row sums of `wt`: `∑ k, wt j k = 1`.
  -- This follows from `W * star W = 1` since
  -- `(W * star W) j j = ∑ k, W j k * star (W j k) = ∑ k, ‖W j k‖² (in ℂ) = 1`.
  have hWWs : W * star W = 1 := by
    -- W * star W = (Vms * U) * (star U * Vm) = Vms * (U * Us) * Vm
    --             = Vms * 1 * Vm = Vms * Vm = 1.
    have hstarW : star W = Us * Vm := by
      show star (Vms * U) = Us * Vm
      rw [star_mul, show star Vms = Vm from by
        show star (star (V : Matrix n n ℂ)) = (V : Matrix n n ℂ)
        exact star_star _]
    rw [hW_def, hstarW]
    calc
      Vms * U * (Us * Vm)
          = Vms * (U * Us) * Vm := by noncomm_ring
      _ = Vms * 1 * Vm := by rw [hUUs]
      _ = Vms * Vm := by rw [Matrix.mul_one]
      _ = 1 := hVmsVm
  have hwt_row_sum : ∀ j, ∑ k, wt j k = 1 := by
    intro j
    have h1 : (W * star W) j j = (1 : Matrix n n ℂ) j j := by rw [hWWs]
    have h1' : (1 : Matrix n n ℂ) j j = 1 := by simp
    rw [show (W * star W) j j = ∑ k, W j k * (star W) k j from Matrix.mul_apply] at h1
    -- `(star W) k j = star (W j k)`, so `W j k * star (W j k) = ‖W j k‖² : ℂ`.
    have hexp : ∑ k, W j k * (star W) k j = ((∑ k, wt j k : ℝ) : ℂ) := by
      rw [show (∑ k, W j k * (star W) k j) = ∑ k, ((wt j k : ℝ) : ℂ) from ?_]
      · push_cast; rfl
      apply Finset.sum_congr rfl
      intro k _
      have hstarW_app : (star W) k j = star (W j k) := rfl
      rw [hstarW_app]
      -- W j k * star (W j k) = ((‖W j k‖²:ℝ):ℂ)
      have hmc := RCLike.mul_conj (W j k)
      have hstar_eq : star (W j k) = (starRingEnd ℂ) (W j k) := rfl
      rw [hstar_eq, hmc]
      simp [hwt_def]
    rw [hexp] at h1
    rw [h1'] at h1
    exact_mod_cast h1
  -- Column sums of `wt`: `∑ j, wt j k = 1`.
  -- This follows from `star W * W = 1` since
  -- `(star W * W) k k = ∑ j, (star W) k j * W j k = ∑ j, star (W j k) * W j k = ∑ j, ‖W j k‖² = 1`.
  have hWsW : star W * W = 1 := by
    have hstarW : star W = Us * Vm := by
      show star (Vms * U) = Us * Vm
      rw [star_mul, show star Vms = Vm from by
        show star (star (V : Matrix n n ℂ)) = (V : Matrix n n ℂ)
        exact star_star _]
    rw [hW_def, hstarW]
    calc
      Us * Vm * (Vms * U)
          = Us * (Vm * Vms) * U := by noncomm_ring
      _ = Us * 1 * U := by rw [hVmVms]
      _ = Us * U := by rw [Matrix.mul_one]
      _ = 1 := hUsU
  have hwt_col_sum : ∀ k, ∑ j, wt j k = 1 := by
    intro k
    have h1 : (star W * W) k k = (1 : Matrix n n ℂ) k k := by rw [hWsW]
    have h1' : (1 : Matrix n n ℂ) k k = 1 := by simp
    rw [show (star W * W) k k = ∑ j, (star W) k j * W j k from Matrix.mul_apply] at h1
    have hexp : ∑ j, (star W) k j * W j k = ((∑ j, wt j k : ℝ) : ℂ) := by
      rw [show (∑ j, (star W) k j * W j k) = ∑ j, ((wt j k : ℝ) : ℂ) from ?_]
      · push_cast; rfl
      apply Finset.sum_congr rfl
      intro j _
      have hstarW_app : (star W) k j = star (W j k) := rfl
      rw [hstarW_app]
      -- star (W j k) * W j k = ((‖W j k‖²:ℝ):ℂ)
      have hcm := RCLike.conj_mul (W j k)
      have hstar_eq : star (W j k) = (starRingEnd ℂ) (W j k) := rfl
      rw [hstar_eq, hcm]
      simp [hwt_def]
    rw [hexp] at h1
    rw [h1'] at h1
    exact_mod_cast h1
  -- Apply Jensen per-`j` to get the inner inequality.
  -- For each `j`: `(∑ k, wt j k * lam k) * log (∑ k, wt j k * lam k)
  --                  ≤ ∑ k, wt j k * (lam k * log (lam k))`.
  have hjensen : ∀ j,
      (∑ k, wt j k * lam k) * Real.log (∑ k, wt j k * lam k)
        ≤ ∑ k, wt j k * (lam k * Real.log (lam k)) := by
    intro j
    have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x => x * Real.log x) :=
      Real.convexOn_mul_log
    have h0 : ∀ k ∈ (Finset.univ : Finset n), 0 ≤ wt j k := fun k _ => hwt_nn j k
    have h1 : ∑ k ∈ (Finset.univ : Finset n), wt j k = 1 := hwt_row_sum j
    have hmem : ∀ k ∈ (Finset.univ : Finset n), lam k ∈ Set.Ici (0 : ℝ) :=
      fun k _ => Set.mem_Ici.mpr (hlam_nn k)
    have hJ := hconv.map_sum_le h0 h1 hmem
    -- `hJ : (∑ k, wt j k • lam k) * log (∑ k, wt j k • lam k) ≤ ∑ k, wt j k • (lam k * log (lam k))`.
    simpa [smul_eq_mul] using hJ
  -- Sum over `j`.
  have hsum_jensen :
      ∑ j, (∑ k, wt j k * lam k) * Real.log (∑ k, wt j k * lam k)
        ≤ ∑ j, ∑ k, wt j k * (lam k * Real.log (lam k)) :=
    Finset.sum_le_sum (fun j _ => hjensen j)
  -- Swap sums on the RHS.
  have hswap :
      ∑ j, ∑ k, wt j k * (lam k * Real.log (lam k))
        = ∑ k, (∑ j, wt j k) * (lam k * Real.log (lam k)) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k _
    rw [← Finset.sum_mul]
  rw [hswap] at hsum_jensen
  -- Simplify the RHS using `hwt_col_sum`.
  have hrhs_simp :
      ∑ k, (∑ j, wt j k) * (lam k * Real.log (lam k))
        = ∑ k, lam k * Real.log (lam k) := by
    apply Finset.sum_congr rfl
    intro k _
    rw [hwt_col_sum k, one_mul]
  rw [hrhs_simp] at hsum_jensen
  -- Now connect LHS to the goal via `hVPV_diag_re`.
  -- LHS of goal: `∑ j, ((Vms * P * Vm) j j).re * log ((Vms * P * Vm) j j).re
  --              = ∑ j, (∑ k, wt j k * lam k) * log (∑ k, wt j k * lam k)`.
  have hLHS_eq :
      (∑ j, ((Vms * P * Vm) j j).re * Real.log (((Vms * P * Vm) j j).re))
        = ∑ j, (∑ k, wt j k * lam k) * Real.log (∑ k, wt j k * lam k) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hVPV_diag_re j]
  -- And connect RHS to `(tr (P · log P)).re` via the Part 3a helper.
  have hRHS_eq :
      ((∑ k, lam k * Real.log (lam k) : ℝ) : ℂ)
        = Matrix.trace (P * CFC.log P) := by
    have := trace_mul_log_eq_sum_eigenvalues hP hPH
    exact this.symm
  have hRHS_re :
      ∑ k, lam k * Real.log (lam k) = (Matrix.trace (P * CFC.log P)).re := by
    have h := congrArg Complex.re hRHS_eq
    simpa using h
  -- Combine.
  rw [hLHS_eq]
  calc
    ∑ j, (∑ k, wt j k * lam k) * Real.log (∑ k, wt j k * lam k)
        ≤ ∑ k, lam k * Real.log (lam k) := hsum_jensen
    _ = (Matrix.trace (P * CFC.log P)).re := hRHS_re

/-! ## Matrix relative entropy nonnegativity (Klein-shifted form)

The full assembly: scalar Klein (Part 3a) + spectral identity (Part 3a) +
Peierls–Bogoliubov (Part 3b) gives the matrix Klein inequality. -/

/-- **Matrix relative entropy nonnegativity (Klein-shifted form).**

For strictly positive complex matrices `P, Q : Matrix n n ℂ`,

  `0 ≤ Re tr (P · log P - P · log Q - P + Q)`.

When `tr P = tr Q` (e.g. both `P` and `Q` are density matrices), the
shift `Re tr (Q - P)` vanishes and we recover the usual relative
entropy nonnegativity `Re tr (P · (log P - log Q)) ≥ 0`. -/
theorem matrix_relative_entropy_nonneg
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {P Q : Matrix n n ℂ}
    (hP : IsStrictlyPositive P) (hQ : IsStrictlyPositive Q) :
    0 ≤ (Matrix.trace (P * CFC.log P - P * CFC.log Q - P + Q)).re := by
  classical
  -- Spectral pieces.
  have hQd : Q.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp hQ
  have hQH : Q.IsHermitian := hQd.isHermitian
  have hPd : P.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp hP
  have hPH : P.IsHermitian := hPd.isHermitian
  -- `Q`'s eigenvector unitary and eigenvalues.
  set V : Matrix.unitaryGroup n ℂ := hQH.eigenvectorUnitary with hV_def
  set Vm : Matrix n n ℂ := (V : Matrix n n ℂ) with hVm_def
  set Vms : Matrix n n ℂ := (star V : Matrix n n ℂ) with hVms_def
  set mu : n → ℝ := hQH.eigenvalues with hmu_def
  have hmu_pos : ∀ j, 0 < mu j := fun j => hQd.eigenvalues_pos j
  -- `P̃ := V* · P · V`. Its diagonal entries are real and nonneg.
  set Pt : Matrix n n ℂ := Vms * P * Vm with hPt_def
  -- `Pt` is positive semidefinite (PSD is preserved by unitary conjugation).
  have hPt_psd : Pt.PosSemidef := by
    have hVmH : Vmᴴ = Vms := by
      show (V : Matrix n n ℂ)ᴴ = (star V : Matrix n n ℂ)
      rfl
    have := hPd.posSemidef.conjTranspose_mul_mul_same (B := Vm)
    rw [hVmH] at this
    exact this
  -- The diagonal entries of `Pt` are real (Hermitian) and nonneg (PSD).
  have hPt_diag_nn : ∀ j, 0 ≤ (Pt j j).re := by
    intro j
    have hd := hPt_psd.diag_nonneg (i := j)
    -- `hd : 0 ≤ Pt j j` (in ℂ with the `ComplexOrder` instance).
    -- For ℂ, `0 ≤ z ↔ z.im = 0 ∧ 0 ≤ z.re`.
    rw [Complex.le_def] at hd
    exact hd.1
  have hPt_diag_im : ∀ j, (Pt j j).im = 0 := by
    intro j
    have hd := hPt_psd.diag_nonneg (i := j)
    rw [Complex.le_def] at hd
    -- `hd.2 : (0 : ℂ).im = (Pt j j).im`, which means `(Pt j j).im = 0`.
    have := hd.2
    simp at this
    exact this.symm
  -- Re-coercion: `(Pt j j) = ((Pt j j).re : ℂ)`.
  have hPt_diag_eq : ∀ j, (Pt j j) = (((Pt j j).re : ℝ) : ℂ) := by
    intro j
    apply Complex.ext
    · simp
    · simp [hPt_diag_im j]
  -- Step 1: Connect `tr (P · log Q)` to `Σ j, (Pt j j).re * log (μ j)`.
  have htr_PlogQ_eq :
      Matrix.trace (P * CFC.log Q) = ∑ j, ((Pt j j).re : ℂ) * ((Real.log (mu j) : ℂ)) := by
    have h := trace_mul_log_Q_eq_sum_eigenvalues P hQ hQH
    rw [h]
    apply Finset.sum_congr rfl
    intro j _
    -- `(star ↑V_Q * P * ↑V_Q) j j = Pt j j` via the `set`.
    -- Goal: (Vms * P * Vm) j j * log(hQH.eigenvalues j) = (Pt j j).re * log (mu j).
    show (Vms * P * Vm) j j * ((Real.log (hQH.eigenvalues j) : ℂ))
        = ((Pt j j).re : ℂ) * ((Real.log (mu j) : ℂ))
    have hmu_eq : hQH.eigenvalues j = mu j := rfl
    rw [hmu_eq]
    congr 1
    exact hPt_diag_eq j
  have htr_PlogQ_re : (Matrix.trace (P * CFC.log Q)).re = ∑ j, (Pt j j).re * Real.log (mu j) := by
    rw [htr_PlogQ_eq]
    -- Re of a real-coerced sum is the sum.
    rw [show (∑ j, ((Pt j j).re : ℂ) * ((Real.log (mu j) : ℂ))) =
           (((∑ j, (Pt j j).re * Real.log (mu j) : ℝ)) : ℂ) from by
        push_cast; rfl]
    simp
  -- Step 2: trace invariance: `tr P = tr Pt = Σ j, (Pt j j)`. The latter is real.
  have htr_P_eq_trPt : Matrix.trace P = Matrix.trace Pt := by
    -- tr (Vms · P · Vm) = tr (Vm · Vms · P) = tr ((Vm · Vms) · P) = tr (1 · P) = tr P. Cycle.
    rw [hPt_def]
    -- tr(Vms * P * Vm) = tr(Vm * Vms * P) by cycling: Vms*P*Vm ⟶ Vm*Vms*P.
    have h1 : Matrix.trace (Vms * P * Vm) = Matrix.trace (Vm * (Vms * P)) := by
      rw [Matrix.trace_mul_comm]
    rw [h1]
    have h2 : Vm * (Vms * P) = (Vm * Vms) * P := by noncomm_ring
    rw [h2]
    have h3 : Vm * Vms = (1 : Matrix n n ℂ) := Unitary.coe_mul_star_self V
    rw [h3]
    rw [Matrix.one_mul]
  -- `tr Pt = Σ j, Pt j j`.
  have htr_Pt_eq_sum : Matrix.trace Pt = ∑ j, Pt j j := rfl
  -- So `(tr P).re = Σ j, (Pt j j).re`.
  have htr_P_re : (Matrix.trace P).re = ∑ j, (Pt j j).re := by
    rw [htr_P_eq_trPt, htr_Pt_eq_sum]
    rw [show (∑ j, Pt j j) = ((∑ j, (Pt j j).re : ℝ) : ℂ) from by
      rw [show (∑ j, Pt j j) = ∑ j, ((Pt j j).re : ℂ) from
        Finset.sum_congr rfl (fun j _ => hPt_diag_eq j)]
      push_cast
      rfl]
    simp
  -- Step 3: `tr Q = Σ j, μ j` (as reals).
  have htr_Q_re : (Matrix.trace Q).re = ∑ j, mu j := by
    -- tr Q = tr (V · D_Q · V*) = tr ((V* · V) · D_Q) = tr D_Q = Σ μ_j.
    have hQ_eq : Q = Vm * (diagonal (RCLike.ofReal ∘ mu)) * Vms := by
      simpa [conjStarAlgAut_apply, hVm_def, hVms_def, hmu_def]
        using hQH.spectral_theorem
    have htrQ : Matrix.trace Q
        = Matrix.trace (diagonal (RCLike.ofReal ∘ mu : n → ℂ)) := by
      rw [hQ_eq]
      have h1 :
          Matrix.trace (Vm * (diagonal (RCLike.ofReal ∘ mu : n → ℂ)) * Vms)
            = Matrix.trace (Vms * Vm * (diagonal (RCLike.ofReal ∘ mu : n → ℂ))) := by
        rw [Matrix.trace_mul_cycle]
      rw [h1]
      rw [show Vms * Vm = (1 : Matrix n n ℂ) from Unitary.coe_star_mul_self V]
      rw [Matrix.one_mul]
    rw [htrQ, Matrix.trace_diagonal]
    rw [show (∑ j, ((RCLike.ofReal ∘ mu) j : ℂ)) = ((∑ j, mu j : ℝ) : ℂ) from by
      push_cast; rfl]
    simp
  -- Step 4: Apply scalar Klein per-j.
  have hklein_sum :
      0 ≤ ∑ j, ((Pt j j).re * Real.log ((Pt j j).re)
                - (Pt j j).re * Real.log (mu j) - (Pt j j).re + mu j) := by
    apply Finset.sum_nonneg
    intro j _
    by_cases hPt_pos : 0 < (Pt j j).re
    · exact CFC.scalar_klein_inequality hPt_pos (hmu_pos j)
    · -- If (Pt j j).re = 0, the scalar Klein expression simplifies to `mu j > 0`.
      have hPt_zero : (Pt j j).re = 0 := le_antisymm (not_lt.mp hPt_pos) (hPt_diag_nn j)
      rw [hPt_zero]
      simp
      exact (hmu_pos j).le
  -- Step 5: Use Peierls-Bogoliubov.
  have hPB := peierls_bogoliubov_mul_log hP V
  -- `hPB : ∑ j, ((star ↑V * P * ↑V) j j).re * log ((star ↑V * P * ↑V) j j).re
  --        ≤ (tr (P * log P)).re`. The LHS sum equals `∑ j, (Pt j j).re * log ((Pt j j).re)`.
  have hPB' :
      ∑ j, (Pt j j).re * Real.log ((Pt j j).re) ≤ (Matrix.trace (P * CFC.log P)).re := by
    have := hPB
    -- Vms * P * Vm = Pt by definition.
    show ∑ j, (Pt j j).re * Real.log ((Pt j j).re) ≤ _
    convert this using 1
  -- Step 6: Assemble. We want:
  -- `0 ≤ (tr(P log P)).re - (tr(P log Q)).re - (tr P).re + (tr Q).re`.
  have hgoal_re :
      (Matrix.trace (P * CFC.log P - P * CFC.log Q - P + Q)).re
        = (Matrix.trace (P * CFC.log P)).re - (Matrix.trace (P * CFC.log Q)).re
            - (Matrix.trace P).re + (Matrix.trace Q).re := by
    simp [Matrix.trace_sub, Matrix.trace_add]
  rw [hgoal_re, htr_PlogQ_re, htr_P_re, htr_Q_re]
  -- Now we need:
  -- 0 ≤ (tr(P log P)).re
  --       - ∑ j, (Pt_jj).re * log μ_j
  --       - ∑ j, (Pt_jj).re
  --       + ∑ j, mu_j.
  -- From hPB' and hklein_sum, this is straightforward arithmetic.
  -- Let `A := (tr(P log P)).re`, `B := ∑ (Pt_jj).re * log (Pt_jj).re`, etc.
  -- hklein_sum: 0 ≤ B - ∑ (Pt_jj).re * log μ_j - ∑ (Pt_jj).re + ∑ μ_j.
  -- hPB': B ≤ A.
  -- So 0 ≤ A - ∑ (Pt_jj).re * log μ_j - ∑ (Pt_jj).re + ∑ μ_j.
  have hsum_split :
      ∑ j, ((Pt j j).re * Real.log ((Pt j j).re)
                - (Pt j j).re * Real.log (mu j) - (Pt j j).re + mu j)
        = (∑ j, (Pt j j).re * Real.log ((Pt j j).re))
          - (∑ j, (Pt j j).re * Real.log (mu j))
          - (∑ j, (Pt j j).re) + (∑ j, mu j) := by
    simp [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hsum_split] at hklein_sum
  linarith [hPB', hklein_sum]

/-! ## Gibbs variational inequality

For Hermitian `H` and a strictly positive matrix `P` with `Re tr P = 1`,

  `Re tr (P · H) - Re tr (P · log P) ≤ log (Re tr (exp H))`.

This is the matrix analogue of the classical Gibbs variational principle
`E_P[H] - H_P ≤ log Z` for the partition function `Z := tr(exp H)`. It
follows directly from `matrix_relative_entropy_nonneg` applied with
`Q := Z⁻¹ • exp H`: this `Q` has `Re tr Q = 1` and `log Q = H - log Z · 1`,
so the Klein nonnegativity rearranges to the Gibbs bound. -/

/-- **Gibbs variational inequality (matrix form).**

For any Hermitian matrix `H : Matrix n n ℂ` and any strictly positive
matrix `P` with `Re tr P = 1`,

  `Re tr (P · H) - Re tr (P · log P) ≤ log (Re tr (exp H))`.

The right-hand side is the log of the partition function
`Z := Re tr (exp H)`, which is positive because `exp H` is strictly
positive. The proof normalizes `Q := Z⁻¹ • exp H` and applies the matrix
relative entropy nonnegativity `matrix_relative_entropy_nonneg`. -/
theorem gibbs_variational_inequality
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian)
    {P : Matrix n n ℂ} (hP : IsStrictlyPositive P) (hPtrace : (Matrix.trace P).re = 1) :
    (Matrix.trace (P * H)).re - (Matrix.trace (P * CFC.log P)).re ≤
      Real.log (Matrix.trace (NormedSpace.exp H)).re := by
  classical
  -- Set `E := exp H`. Then `E` is Hermitian (hence self-adjoint) and a unit, so
  -- `E` is strictly positive.
  set E : Matrix n n ℂ := NormedSpace.exp H with hE_def
  have hH_sa : IsSelfAdjoint H := hH
  have hE_herm : E.IsHermitian := Matrix.IsHermitian.exp hH
  have hE_sa : IsSelfAdjoint E := hE_herm
  have hE_nn : (0 : Matrix n n ℂ) ≤ E := hH_sa.exp_nonneg
  have hE_unit : IsUnit E := Matrix.isUnit_exp H
  have hE_sp : IsStrictlyPositive E := hE_unit.isStrictlyPositive hE_nn
  -- `E` is positive definite (sum of strictly positive eigenvalues).
  have hE_pd : E.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp hE_sp
  -- Define `Z := (trace E).re` and show `0 < Z`.
  set Z : ℝ := (Matrix.trace E).re with hZ_def
  -- Each diagonal entry of `E` is positive (in `ComplexOrder`), so its `.re` is `> 0`.
  have hE_diag_pos : ∀ i, 0 < (E i i).re := by
    intro i
    have hd : (0 : ℂ) < E i i := hE_pd.diag_pos
    -- `0 < z` in `ComplexOrder` ⇒ `0 < z.re` and `z.im = 0`.
    rw [Complex.lt_def] at hd
    exact hd.1
  -- `(trace E).re = ∑ i, (E i i).re > 0` (sum of positives, nonempty index).
  have hZ_pos : 0 < Z := by
    rw [hZ_def, Matrix.trace, Complex.re_sum]
    have hpos := fun i (_ : i ∈ (Finset.univ : Finset n)) => hE_diag_pos i
    have hne : (Finset.univ : Finset n).Nonempty := Finset.univ_nonempty
    exact Finset.sum_pos (fun i hi => hpos i hi) hne
  have hZ_ne : Z ≠ 0 := ne_of_gt hZ_pos
  have hZ_inv_pos : 0 < Z⁻¹ := inv_pos.mpr hZ_pos
  -- Define `Q := Z⁻¹ • E` and show it is strictly positive.
  set Q : Matrix n n ℂ := Z⁻¹ • E with hQ_def
  have hQ_sp : IsStrictlyPositive Q := hE_sp.smul hZ_inv_pos
  -- Compute `(trace Q).re = 1`. The trace of a Hermitian matrix is real.
  have htraceE_real : ((Matrix.trace E).re : ℂ) = Matrix.trace E := by
    -- `trace E = ∑ i, E i i = ∑ i, (E i i).re` (since `E` is Hermitian).
    rw [Matrix.trace]
    rw [show (∑ i, Matrix.diag E i) = ∑ i, (((Matrix.diag E i).re : ℝ) : ℂ) from ?_]
    · simp [Complex.re_sum]
    · apply Finset.sum_congr rfl
      intro i _
      exact (hE_herm.coe_re_apply_self i).symm
  have htraceE_im : (Matrix.trace E).im = 0 := by
    have h := congrArg Complex.im htraceE_real
    simp at h
    linarith [h]
  have htraceQ_re : (Matrix.trace Q).re = 1 := by
    rw [hQ_def, Matrix.trace_smul]
    -- `(Z⁻¹ • trace E).re = Z⁻¹ * (trace E).re = Z⁻¹ * Z = 1`.
    show (((Z⁻¹ : ℝ) : ℂ) * Matrix.trace E).re = 1
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [htraceE_im]
    ring_nf
    rw [← hZ_def]
    exact inv_mul_cancel₀ hZ_ne
  -- Compute `CFC.log Q = algebraMap ℝ _ (log Z⁻¹) + log E = algebraMap ℝ _ (log Z⁻¹) + H`.
  have hlog_E : CFC.log E = H := by
    rw [hE_def]
    exact CFC.log_exp H hH_sa
  have hlog_Q : CFC.log Q = algebraMap ℝ (Matrix n n ℂ) (Real.log Z⁻¹) + H := by
    rw [hQ_def]
    rw [CFC.log_smul' E hZ_inv_pos hE_sp]
    rw [hlog_E]
  -- Rewrite `Real.log Z⁻¹ = -Real.log Z`.
  have hlogZ_inv : Real.log Z⁻¹ = -Real.log Z := Real.log_inv Z
  -- Now express `trace (P * CFC.log Q)`.
  -- `P * (algebraMap ℝ _ (log Z⁻¹) + H) = P * algebraMap ℝ _ (log Z⁻¹) + P * H`.
  -- `algebraMap ℝ (Matrix n n ℂ) r = r • 1`.
  have halg_eq : algebraMap ℝ (Matrix n n ℂ) (Real.log Z⁻¹)
                  = (Real.log Z⁻¹) • (1 : Matrix n n ℂ) :=
    Algebra.algebraMap_eq_smul_one (Real.log Z⁻¹)
  -- Compute `trace (P * CFC.log Q)`.
  have htr_PlogQ :
      Matrix.trace (P * CFC.log Q)
        = (Real.log Z⁻¹) • Matrix.trace P + Matrix.trace (P * H) := by
    rw [hlog_Q, halg_eq]
    rw [show P * ((Real.log Z⁻¹) • (1 : Matrix n n ℂ) + H)
          = (Real.log Z⁻¹) • (P * 1) + P * H from by
        rw [mul_add, Matrix.mul_smul]]
    rw [Matrix.mul_one, Matrix.trace_add, Matrix.trace_smul]
  -- The real part of `trace (P * CFC.log Q)`.
  have htr_PlogQ_re :
      (Matrix.trace (P * CFC.log Q)).re
        = Real.log Z⁻¹ * (Matrix.trace P).re + (Matrix.trace (P * H)).re := by
    rw [htr_PlogQ]
    -- `((r • z) + w).re = r * z.re + w.re` for `r : ℝ`, `z w : ℂ`.
    simp [Complex.add_re, Complex.real_smul, Complex.ofReal_re, Complex.ofReal_im,
          Complex.mul_re]
  -- Apply the matrix relative entropy nonnegativity.
  have hklein := matrix_relative_entropy_nonneg hP hQ_sp
  -- `hklein : 0 ≤ (trace (P · log P - P · log Q - P + Q)).re`.
  -- Expand the trace.
  have hexpand :
      (Matrix.trace (P * CFC.log P - P * CFC.log Q - P + Q)).re
        = (Matrix.trace (P * CFC.log P)).re - (Matrix.trace (P * CFC.log Q)).re
            - (Matrix.trace P).re + (Matrix.trace Q).re := by
    simp [Matrix.trace_sub, Matrix.trace_add]
  rw [hexpand, htr_PlogQ_re, hPtrace, htraceQ_re, hlogZ_inv] at hklein
  -- `hklein : 0 ≤ (trace (P log P)).re - (-log Z * 1 + (trace (P · H)).re) - 1 + 1`.
  -- Simplify: `0 ≤ (trace (P log P)).re + log Z - (trace (P · H)).re`.
  -- Therefore `(trace (P · H)).re - (trace (P log P)).re ≤ log Z`.
  linarith

/-! ## Gibbs variational equality (achievability)

The Gibbs variational inequality is in fact tight: the supremum of
`Re tr (P · H) - Re tr (P · log P)` over strictly positive unit-trace
`P` is attained at the **Gibbs state** `P* := Z⁻¹ • exp H` where
`Z := Re tr (exp H)`. The bound is achieved with equality, giving

  `log Z = Re tr (P* · H) - Re tr (P* · log P*)`.

This is the *achievability direction* needed for the Lieb–Tropp/Lindblad
bridge in the matrix Bernstein chain. -/

/-- **Gibbs variational equality (achievability direction).**

For any Hermitian matrix `H : Matrix n n ℂ`, the Gibbs state
`P* := Z⁻¹ • exp H` (where `Z := Re tr (exp H)`) is strictly positive,
has unit real-trace, and achieves the Gibbs variational bound with
equality:

  `Re tr (P* · H) - Re tr (P* · log P*) = log (Re tr (exp H))`.

Combined with `gibbs_variational_inequality`, this shows that
`log (Re tr (exp H))` is the **supremum** of
`Re tr (P · H) - Re tr (P · log P)` over strictly positive unit-trace
`P`, with the supremum attained at the Gibbs state.

The proof is purely algebraic: substitute `P = Z⁻¹ • exp H`, use
`CFC.log_smul'` and `CFC.log_exp` to rewrite `log P` as `log Z⁻¹ • 1 + H`,
distribute the trace, and use `Re tr P = 1` to cancel. -/
theorem gibbs_variational_equality
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    ∃ (P : Matrix n n ℂ) (_ : IsStrictlyPositive P) (_ : (Matrix.trace P).re = 1),
      (Matrix.trace (P * H)).re - (Matrix.trace (P * CFC.log P)).re =
        Real.log (Matrix.trace (NormedSpace.exp H : Matrix n n ℂ)).re := by
  classical
  -- Set `E := exp H`, mirroring the Part 4 proof.
  set E : Matrix n n ℂ := NormedSpace.exp H with hE_def
  have hH_sa : IsSelfAdjoint H := hH
  have hE_herm : E.IsHermitian := Matrix.IsHermitian.exp hH
  have hE_nn : (0 : Matrix n n ℂ) ≤ E := hH_sa.exp_nonneg
  have hE_unit : IsUnit E := Matrix.isUnit_exp H
  have hE_sp : IsStrictlyPositive E := hE_unit.isStrictlyPositive hE_nn
  have hE_pd : E.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp hE_sp
  -- `Z := (trace E).re` and `0 < Z`.
  set Z : ℝ := (Matrix.trace E).re with hZ_def
  have hE_diag_pos : ∀ i, 0 < (E i i).re := by
    intro i
    have hd : (0 : ℂ) < E i i := hE_pd.diag_pos
    rw [Complex.lt_def] at hd
    exact hd.1
  have hZ_pos : 0 < Z := by
    rw [hZ_def, Matrix.trace, Complex.re_sum]
    have hpos := fun i (_ : i ∈ (Finset.univ : Finset n)) => hE_diag_pos i
    have hne : (Finset.univ : Finset n).Nonempty := Finset.univ_nonempty
    exact Finset.sum_pos (fun i hi => hpos i hi) hne
  have hZ_ne : Z ≠ 0 := ne_of_gt hZ_pos
  have hZ_inv_pos : 0 < Z⁻¹ := inv_pos.mpr hZ_pos
  -- The Gibbs state `P := Z⁻¹ • E` is strictly positive.
  set P : Matrix n n ℂ := Z⁻¹ • E with hP_def
  have hP_sp : IsStrictlyPositive P := hE_sp.smul hZ_inv_pos
  -- `(trace E).re = ∑ i, (E i i).re` and `trace E` is real.
  have htraceE_real : ((Matrix.trace E).re : ℂ) = Matrix.trace E := by
    rw [Matrix.trace]
    rw [show (∑ i, Matrix.diag E i) = ∑ i, (((Matrix.diag E i).re : ℝ) : ℂ) from ?_]
    · simp [Complex.re_sum]
    · apply Finset.sum_congr rfl
      intro i _
      exact (hE_herm.coe_re_apply_self i).symm
  have htraceE_im : (Matrix.trace E).im = 0 := by
    have h := congrArg Complex.im htraceE_real
    simp at h
    linarith [h]
  -- `(trace P).re = 1`.
  have hPtrace : (Matrix.trace P).re = 1 := by
    rw [hP_def, Matrix.trace_smul]
    show (((Z⁻¹ : ℝ) : ℂ) * Matrix.trace E).re = 1
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [htraceE_im]
    ring_nf
    rw [← hZ_def]
    exact inv_mul_cancel₀ hZ_ne
  -- `CFC.log E = H`.
  have hlog_E : CFC.log E = H := by
    rw [hE_def]
    exact CFC.log_exp H hH_sa
  -- `CFC.log P = algebraMap ℝ _ (log Z⁻¹) + H`.
  have hlog_P : CFC.log P = algebraMap ℝ (Matrix n n ℂ) (Real.log Z⁻¹) + H := by
    rw [hP_def]
    rw [CFC.log_smul' E hZ_inv_pos hE_sp]
    rw [hlog_E]
  -- `Real.log Z⁻¹ = -Real.log Z`.
  have hlogZ_inv : Real.log Z⁻¹ = -Real.log Z := Real.log_inv Z
  -- `algebraMap ℝ (Matrix n n ℂ) r = r • 1`.
  have halg_eq : algebraMap ℝ (Matrix n n ℂ) (Real.log Z⁻¹)
                  = (Real.log Z⁻¹) • (1 : Matrix n n ℂ) :=
    Algebra.algebraMap_eq_smul_one (Real.log Z⁻¹)
  -- `trace (P * CFC.log P) = log Z⁻¹ • trace P + trace (P * H)`.
  have htr_PlogP :
      Matrix.trace (P * CFC.log P)
        = (Real.log Z⁻¹) • Matrix.trace P + Matrix.trace (P * H) := by
    rw [hlog_P, halg_eq]
    rw [show P * ((Real.log Z⁻¹) • (1 : Matrix n n ℂ) + H)
          = (Real.log Z⁻¹) • (P * 1) + P * H from by
        rw [mul_add, Matrix.mul_smul]]
    rw [Matrix.mul_one, Matrix.trace_add, Matrix.trace_smul]
  -- The real part: `(trace (P * CFC.log P)).re = log Z⁻¹ * (trace P).re + (trace (P * H)).re`.
  have htr_PlogP_re :
      (Matrix.trace (P * CFC.log P)).re
        = Real.log Z⁻¹ * (Matrix.trace P).re + (Matrix.trace (P * H)).re := by
    rw [htr_PlogP]
    simp [Complex.add_re, Complex.real_smul, Complex.ofReal_re, Complex.ofReal_im,
          Complex.mul_re]
  -- Now assemble: `Re tr(P · H) - Re tr(P · log P)
  --   = Re tr(P · H) - (log Z⁻¹ · 1 + Re tr(P · H))
  --   = -log Z⁻¹
  --   = log Z`.
  refine ⟨P, hP_sp, hPtrace, ?_⟩
  rw [htr_PlogP_re, hPtrace, hlogZ_inv]
  ring

end Matrix
