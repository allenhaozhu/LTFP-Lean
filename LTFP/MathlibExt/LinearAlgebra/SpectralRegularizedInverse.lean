/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Topology.Algebra.Order.Field

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

/-- **Step 2-impl (B4 Node 3), general form.** Spectral form of the
regularized-inverse trace identity, parameterized by the weakest
nonvanishing hypothesis on the shifted eigenvalues:
```
trace ((A + lam • 1)⁻¹ * A) = ∑ i, eig i / (eig i + lam)
```
for a real positive-definite `A`, eigenvalues `eig`, and any `lam`
such that `eig i + lam ≠ 0` for every `i`.

This is the load-bearing version used by both the `0 ≤ lam` corollary
(`trace_regularized_inv_mul_eq_eigenvalue_sum`) and the `lam → 0`
limit carrier (`trace_regularized_inv_mul_tendsto_card_spectral`),
which needs the identity to hold in an *open* neighborhood of `0`
(including small negative `lam`). -/
theorem trace_regularized_inv_mul_eq_eigenvalue_sum_of_ne
    (A : Matrix d d ℝ) (hA : A.PosDef) {lam : ℝ}
    (h_ne : ∀ i, hA.1.eigenvalues i + lam ≠ 0) :
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
  -- Step 4: invertibility of the diagonal (via `det_diagonal` and the hypothesis).
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

/-- **Step 2-impl (B4 Node 3).** Spectral form of the regularized-
inverse trace identity:
```
trace ((A + lam • 1)⁻¹ * A) = ∑ i, eig i / (eig i + lam)
```
for a real positive-definite `A`, with `eig` the eigenvalues of `A`
and `0 ≤ lam`.

This is the corollary of `trace_regularized_inv_mul_eq_eigenvalue_sum_of_ne`
specialized to the non-negative-`lam` regime: positivity of every
eigenvalue (`Matrix.PosDef.eigenvalues_pos`) combined with
`0 ≤ lam` gives `0 < eig i + lam`, which discharges the
non-vanishing hypothesis. -/
theorem trace_regularized_inv_mul_eq_eigenvalue_sum
    (A : Matrix d d ℝ) (hA : A.PosDef) {lam : ℝ} (hlam : 0 ≤ lam) :
    ((A + lam • (1 : Matrix d d ℝ))⁻¹ * A).trace
      = ∑ i, hA.1.eigenvalues i / (hA.1.eigenvalues i + lam) :=
  trace_regularized_inv_mul_eq_eigenvalue_sum_of_ne A hA fun i =>
    (add_pos_of_pos_of_nonneg (hA.eigenvalues_pos i) hlam).ne'

/-! ## Limit consequence — the B4 Node 3 carrier (Spike 4)

Composing the spectral identity above with the elementary fact that
each summand `lam ↦ eig i / (eig i + lam)` is continuous at `lam = 0`
(where `eig i > 0` by `PosDef`), the trace tends to
`∑ i, eig i / eig i = ∑ i, 1 = Fintype.card d` as `lam → 0`.

This is the *spectral-route* carrier for B4 Node 3: it factors the
limit through the per-eigenvalue identity, making visible the
per-eigenvalue Bayes-risk structure that the Bach §3.7 lower-bound
chain is intended to consume. (The shorter inverse-continuity route
landed earlier as `Matrix.trace_regularized_inv_mul_tendsto_card` in
`LTFP.MathlibExt.LinearAlgebra.MatrixInverseLimit`; that version
covers any `det ≠ 0` matrix and is what `SpectralSpike` currently
cites in its Spike-4 example block.) -/

/-- The shifted eigenvalue `eig i + lam` is non-zero in a
neighborhood of `lam = 0`, for every index `i`, when `A` is
positive-definite. -/
private lemma eventually_eigenvalues_add_ne_zero
    (A : Matrix d d ℝ) (hA : A.PosDef) :
    ∀ᶠ lam : ℝ in nhds 0, ∀ i, hA.1.eigenvalues i + lam ≠ 0 := by
  rw [Filter.eventually_all]
  intro i
  -- For each fixed `i`, openness of `{x | x ≠ 0}` around `eig i > 0`
  -- pulls back through continuity of `lam ↦ eig i + lam` at `0`.
  have h_tendsto :
      Filter.Tendsto (fun lam : ℝ => hA.1.eigenvalues i + lam)
        (nhds (0 : ℝ)) (nhds (hA.1.eigenvalues i + 0)) :=
    Filter.Tendsto.const_add _ Filter.tendsto_id
  rw [add_zero] at h_tendsto
  exact h_tendsto.eventually
    (isOpen_ne.mem_nhds (hA.eigenvalues_pos i).ne')

/-- **B4 Node 3 carrier (spectral route).** The trace of
`(A + lam • 1)⁻¹ * A` tends to `Fintype.card d` as `lam → 0`,
proved by composing the spectral identity
`trace_regularized_inv_mul_eq_eigenvalue_sum_of_ne` with the
per-eigenvalue limit `eig i / (eig i + lam) → 1`. -/
theorem trace_regularized_inv_mul_tendsto_card_spectral
    (A : Matrix d d ℝ) (hA : A.PosDef) :
    Filter.Tendsto (fun lam : ℝ => ((A + lam • (1 : Matrix d d ℝ))⁻¹ * A).trace)
      (nhds 0) (nhds ((Fintype.card d : ℕ) : ℝ)) := by
  classical
  set eig : d → ℝ := hA.1.eigenvalues with heig_def
  -- (a) The eigenvalue-sum function tends to ∑ i, 1.
  have h_each : ∀ i : d,
      Filter.Tendsto (fun lam : ℝ => eig i / (eig i + lam))
        (nhds (0 : ℝ)) (nhds 1) := by
    intro i
    have h_denom :
        Filter.Tendsto (fun lam : ℝ => eig i + lam)
          (nhds (0 : ℝ)) (nhds (eig i + 0)) :=
      Filter.Tendsto.const_add _ Filter.tendsto_id
    rw [add_zero] at h_denom
    have h_num : Filter.Tendsto (fun _ : ℝ => eig i) (nhds (0 : ℝ)) (nhds (eig i)) :=
      tendsto_const_nhds
    have h_div := h_num.div h_denom (hA.eigenvalues_pos i).ne'
    -- `Tendsto.div` returns the limit phrased with the pointwise
    -- `Pi.instDiv` (i.e. `(fun _ => eig i) / (fun lam => eig i + lam)`).
    -- Convert to the explicit pointwise form and collapse `eig i / eig i = 1`.
    have h_div' :
        Filter.Tendsto (fun lam : ℝ => eig i / (eig i + lam))
          (nhds (0 : ℝ)) (nhds (eig i / eig i)) := h_div
    rw [div_self (hA.eigenvalues_pos i).ne'] at h_div'
    exact h_div'
  have h_sum_tendsto :
      Filter.Tendsto (fun lam : ℝ => ∑ i, eig i / (eig i + lam))
        (nhds (0 : ℝ)) (nhds (∑ _i : d, (1 : ℝ))) :=
    tendsto_finset_sum Finset.univ (fun i _ => h_each i)
  -- (b) Convert the constant-1 sum to `Fintype.card d`.
  have h_const_sum : (∑ _i : d, (1 : ℝ)) = ((Fintype.card d : ℕ) : ℝ) := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [h_const_sum] at h_sum_tendsto
  -- (c) Transfer to the trace expression via eventual equality
  -- (using `trace_regularized_inv_mul_eq_eigenvalue_sum_of_ne` on
  -- the neighborhood where every shifted eigenvalue is non-zero).
  refine h_sum_tendsto.congr' ?_
  filter_upwards [eventually_eigenvalues_add_ne_zero A hA] with lam h_ne
  exact (trace_regularized_inv_mul_eq_eigenvalue_sum_of_ne A hA h_ne).symm

end LTFP.MathlibExt.LinearAlgebra
