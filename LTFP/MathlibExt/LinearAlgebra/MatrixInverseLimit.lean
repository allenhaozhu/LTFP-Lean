/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Instances.Matrix

/-!
# Regularized matrix inverse limit and trace continuity

For an invertible real square matrix `M`, the *Tikhonov-regularized*
expression `(M + lam • 1)⁻¹ * M` converges to the identity as the
regularization parameter `lam` tends to zero, and consequently its
trace converges to `tr 1 = card d`.

This identity is the matrix component of Bach's *Learning Theory from
First Principles* (2024) §3.7, where it appears in the final step of
the ordinary-least-squares minimax lower bound: when the empirical
second-moment matrix has full rank,
`(M + lam I)⁻¹ M → I` as `lam → 0`.

Mathlib already provides the analytic ingredients (continuity of
`det`, `adjugate`, and matrix multiplication, plus continuity of
`Ring.inverse` at units of a complete normed ring). This module
assembles them into the regularized-inverse limit statement.

## Main results

* `Matrix.regularized_inv_mul_tendsto_one` :
  `(M + lam • 1)⁻¹ * M ⟶ 1` as `lam → 0`, for `M` with `det M ≠ 0`.
* `Matrix.trace_regularized_inv_mul_tendsto` :
  `tr ((M + lam • 1)⁻¹ * M) ⟶ tr 1` as `lam → 0`.
* `Matrix.trace_regularized_inv_mul_tendsto_card` :
  the specialization stating the limit equals `Fintype.card d`.

The carrier algebraic identities (`lam = 0` reduction and the trace
value at the identity) are also recorded for downstream reuse.
-/

namespace Matrix

open Filter Topology

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- At `lam = 0`, the regularized expression collapses to `M⁻¹ * M`. -/
theorem regularized_inv_mul_zero (M : Matrix d d ℝ) :
    (M + (0 : ℝ) • (1 : Matrix d d ℝ))⁻¹ * M = M⁻¹ * M := by
  simp

/-- Algebraic anchor: for an invertible square matrix `M`, the
inverse-then-multiply identity `M⁻¹ * M = 1` is the value the
regularized expression takes in the limit. -/
theorem inv_mul_of_det_ne_zero (M : Matrix d d ℝ) (hM : M.det ≠ 0) :
    M⁻¹ * M = 1 :=
  Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM)

/-- For an invertible real square matrix `M`, the regularized inverse
`(M + lam • 1)⁻¹ * M` tends to the identity as `lam → 0`. -/
theorem regularized_inv_mul_tendsto_one
    (M : Matrix d d ℝ) (hM : M.det ≠ 0) :
    Tendsto (fun lam : ℝ => (M + lam • (1 : Matrix d d ℝ))⁻¹ * M)
      (nhds 0) (nhds (1 : Matrix d d ℝ)) := by
  -- Step 1. The perturbation `lam ↦ M + lam • 1` is continuous.
  have h_add : Continuous (fun lam : ℝ => M + lam • (1 : Matrix d d ℝ)) :=
    continuous_const.add (continuous_id.smul continuous_const)
  -- Step 2. `Ring.inverse` is continuous at the (nonzero) determinant
  -- of `M`, since `ℝ` is a complete normed field.
  have h_det_unit : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  have h_ring_inv : ContinuousAt Ring.inverse M.det := by
    have := NormedRing.inverse_continuousAt h_det_unit.unit
    simpa [IsUnit.unit_spec] using this
  -- Step 3. Hence `Inv.inv` on matrices is continuous at `M`.
  have h_mat_inv : ContinuousAt (Inv.inv : Matrix d d ℝ → Matrix d d ℝ) M :=
    continuousAt_matrix_inv M h_ring_inv
  -- Step 4. The composition `lam ↦ (M + lam • 1)⁻¹` is continuous at
  -- `lam = 0`. The perturbation evaluates to `M` at `lam = 0`, so
  -- `ContinuousAt.comp_of_eq` carries the inverse's continuity at `M`
  -- across the composition.
  have h_g0 : M + (0 : ℝ) • (1 : Matrix d d ℝ) = M := by simp
  have h_add_at0 :
      ContinuousAt (fun lam : ℝ => M + lam • (1 : Matrix d d ℝ)) 0 :=
    h_add.continuousAt
  have h_inv_comp :
      ContinuousAt (fun lam : ℝ => (M + lam • (1 : Matrix d d ℝ))⁻¹) 0 :=
    h_mat_inv.comp_of_eq h_add_at0 h_g0
  -- Step 5. Multiply on the right by the constant `M`.
  have h_mul :
      ContinuousAt (fun lam : ℝ => (M + lam • (1 : Matrix d d ℝ))⁻¹ * M) 0 :=
    h_inv_comp.mul continuousAt_const
  -- Step 6. Identify the value at `lam = 0` as the identity matrix
  -- via `M⁻¹ * M = 1`, then convert `ContinuousAt` to `Tendsto`.
  have h_tendsto := h_mul.tendsto
  have h_value :
      (M + (0 : ℝ) • (1 : Matrix d d ℝ))⁻¹ * M = (1 : Matrix d d ℝ) := by
    rw [h_g0]; exact inv_mul_of_det_ne_zero M hM
  rw [h_value] at h_tendsto
  exact h_tendsto

/-- Trace continuity corollary of `regularized_inv_mul_tendsto_one`:
the trace of `(M + lam • 1)⁻¹ * M` tends to `tr 1` as `lam → 0`. -/
theorem trace_regularized_inv_mul_tendsto
    (M : Matrix d d ℝ) (hM : M.det ≠ 0) :
    Tendsto (fun lam : ℝ => ((M + lam • (1 : Matrix d d ℝ))⁻¹ * M).trace)
      (nhds 0) (nhds ((1 : Matrix d d ℝ).trace)) := by
  have h_trace : Continuous (Matrix.trace : Matrix d d ℝ → ℝ) :=
    continuous_id.matrix_trace
  exact (h_trace.tendsto _).comp (regularized_inv_mul_tendsto_one M hM)

/-- Specialization of `trace_regularized_inv_mul_tendsto` using
Mathlib's `Matrix.trace_one`: the trace of the regularized expression
tends to `Fintype.card d`. -/
theorem trace_regularized_inv_mul_tendsto_card
    (M : Matrix d d ℝ) (hM : M.det ≠ 0) :
    Tendsto (fun lam : ℝ => ((M + lam • (1 : Matrix d d ℝ))⁻¹ * M).trace)
      (nhds 0) (nhds ((Fintype.card d : ℕ) : ℝ)) := by
  have h := trace_regularized_inv_mul_tendsto M hM
  simpa [Matrix.trace_one] using h

end Matrix
