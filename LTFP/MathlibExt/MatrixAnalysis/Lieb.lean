/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lieb's concavity theorem -- scalar algebraic anchor

Lieb's concavity theorem (1973) states that for any Hermitian matrix
`H` and positive-definite matrix `K`, the map
`(H, K) ↦ tr exp(H + log K)` is jointly concave in `(H, K)`. The full
theorem is a foundational result in matrix analysis and quantum
information theory; its proof relies on operator-monotone-function
theory (Loewner's theorem) and the Lieb concavity machinery, neither
of which is currently available in Mathlib.

This module supplies the *scalar* `1 × 1` algebraic anchor of the
theorem. In the scalar case `H = h`, `K = k > 0`, the trace exponential
reduces to `exp(h + log k) = k · exp h`, and concavity follows from
direct calculus. We package the basic algebraic identities
(positivity, equivalence to the original form, monotonicity, sanity
values at the boundary, and the geometric-mean / log-affine
identities) that any future matrix-level Mathlib proof must specialize
to in dimension one.

The matrix theorem is a documented Mathlib gap; promoting this anchor
to the full statement is multi-week analytic work and is deferred.

## Main definitions

* `liebScalar` : the scalar reduction `(h, k) ↦ k * exp h` of the Lieb
  trace exponential.

## Main results

* `liebScalar_pos`                  : `liebScalar h k` is strictly
  positive when `0 < k`.
* `liebScalar_equiv_exp_add_log`    : `liebScalar h k = exp (h + log k)`
  when `0 < k`, the equivalence with the original Lieb form.
* `liebScalar_mono_h`               : monotonicity in `h`.
* `liebScalar_mono_k`               : monotonicity in `k`.
* `liebScalar_zero_h`               : `liebScalar 0 k = k`.
* `liebScalar_one_k`                : `liebScalar h 1 = exp h`.
* `liebScalar_AMGM_anchor`          : the geometric mean of
  `liebScalar h₁ k` and `liebScalar h₂ k` equals the midpoint value
  `liebScalar ((h₁ + h₂) / 2) k`.
* `liebScalar_log_concave_anchor`   : `log ∘ liebScalar (·) k` is
  exactly affine in `h`, witnessing log-concavity with equality.
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace LTFP.MathlibExt.MatrixAnalysis

open Real

/-- Scalar reduction of the Lieb trace exponential. For real `h` and
positive `k`, this is `k * exp h`, which equals `exp (h + log k)`. -/
noncomputable def liebScalar (h k : ℝ) : ℝ := k * Real.exp h

/-- Positivity: for `0 < k`, the scalar Lieb value is strictly
positive. -/
theorem liebScalar_pos (h k : ℝ) (hk : 0 < k) : 0 < liebScalar h k := by
  unfold liebScalar
  exact mul_pos hk (Real.exp_pos h)

/-- Equivalence with the original Lieb form: for `0 < k`, the scalar
reduction `k * exp h` agrees with `exp (h + log k)`. -/
theorem liebScalar_equiv_exp_add_log (h k : ℝ) (hk : 0 < k) :
    liebScalar h k = Real.exp (h + Real.log k) := by
  unfold liebScalar
  rw [Real.exp_add, Real.exp_log hk, mul_comm]

/-- Monotonicity in `h` (for any `0 ≤ k`). -/
theorem liebScalar_mono_h (k : ℝ) (hk : 0 ≤ k) :
    Monotone (fun h : ℝ => liebScalar h k) := by
  intro a b hab
  unfold liebScalar
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hab) hk

/-- Monotonicity in `k` (for any real `h`). -/
theorem liebScalar_mono_k (h : ℝ) :
    Monotone (fun k : ℝ => liebScalar h k) := by
  intro a b hab
  unfold liebScalar
  exact mul_le_mul_of_nonneg_right hab (Real.exp_pos h).le

/-- Sanity: at `h = 0`, the scalar Lieb value collapses to `k`. -/
theorem liebScalar_zero_h (k : ℝ) : liebScalar 0 k = k := by
  unfold liebScalar
  rw [Real.exp_zero, mul_one]

/-- Sanity: at `k = 1`, the scalar Lieb value collapses to `exp h`. -/
theorem liebScalar_one_k (h : ℝ) : liebScalar h 1 = Real.exp h := by
  unfold liebScalar
  rw [one_mul]

/-- Geometric-mean identity: the square root of the product of two
scalar Lieb values at the same `k` equals the value at the midpoint
`(h₁ + h₂) / 2`. This is the AM-GM anchor underlying log-concavity in
`h`. -/
theorem liebScalar_AMGM_anchor (h₁ h₂ k : ℝ) (hk : 0 < k) :
    Real.sqrt (liebScalar h₁ k * liebScalar h₂ k)
      = liebScalar ((h₁ + h₂) / 2) k := by
  -- `liebScalar h₁ k * liebScalar h₂ k = k^2 * exp (h₁ + h₂)`
  have hk0 : (0 : ℝ) ≤ k := hk.le
  have hprod :
      liebScalar h₁ k * liebScalar h₂ k = k ^ 2 * Real.exp (h₁ + h₂) := by
    unfold liebScalar
    rw [Real.exp_add]; ring
  rw [hprod]
  -- `√(k^2 * exp (h₁ + h₂)) = k * √(exp (h₁ + h₂)) = k * exp ((h₁ + h₂) / 2)`
  have hexp_nonneg : (0 : ℝ) ≤ Real.exp (h₁ + h₂) := (Real.exp_pos _).le
  rw [Real.sqrt_mul (sq_nonneg k), Real.sqrt_sq hk0]
  -- Now goal: `k * √(exp (h₁ + h₂)) = liebScalar ((h₁ + h₂) / 2) k`
  unfold liebScalar
  -- `exp ((h₁ + h₂) / 2) = √(exp (h₁ + h₂))`
  have hhalf :
      Real.exp ((h₁ + h₂) / 2) = Real.sqrt (Real.exp (h₁ + h₂)) :=
    Real.exp_half (h₁ + h₂)
  rw [hhalf]

/-- Log-affine identity: `log` of the scalar Lieb value is exactly
affine in `h` for fixed positive `k`. This is the log-concavity anchor
with equality. -/
theorem liebScalar_log_concave_anchor (h₁ h₂ k : ℝ) (hk : 0 < k) :
    Real.log (liebScalar ((h₁ + h₂) / 2) k)
      = (Real.log (liebScalar h₁ k) + Real.log (liebScalar h₂ k)) / 2 := by
  have hk_ne : k ≠ 0 := ne_of_gt hk
  have hexp_ne : ∀ x : ℝ, Real.exp x ≠ 0 := fun x => (Real.exp_pos x).ne'
  -- Expand both sides via `log_mul` and `log_exp`.
  unfold liebScalar
  rw [Real.log_mul hk_ne (hexp_ne _),
      Real.log_mul hk_ne (hexp_ne _),
      Real.log_mul hk_ne (hexp_ne _),
      Real.log_exp, Real.log_exp, Real.log_exp]
  ring

end LTFP.MathlibExt.MatrixAnalysis
