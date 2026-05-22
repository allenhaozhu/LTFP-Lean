/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Calculus.TaylorRemainderRightSided

/-!
# Taylor remainder bound on a right-half ball with explicit polynomial

Bridge from round 19's `taylor_remainder_bound_right` (which keeps the
Mathlib `taylorWithinEval f 1 ...` polynomial) to the downstream-usable
explicit form `f x₀ + deriv f x₀ * (x - x₀)`, and to the symmetric ball
form bounded by the radius squared.

This is the right-half of the ball. The reflected left-half + sign algebra
is still missing for the full two-sided ball form.
-/

open Set

lemma taylorWithinEval_one_eq
    {f : ℝ → ℝ} {x₀ x : ℝ} (hf : ContDiff ℝ 2 f) (hx : x₀ < x) :
    taylorWithinEval f 1 (Icc x₀ x) x₀ x = f x₀ + deriv f x₀ * (x - x₀) := by
  have hderiv : derivWithin f (Icc x₀ x) x₀ = deriv f x₀ :=
    (hf.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0) x₀).derivWithin
      ((uniqueDiffOn_Icc hx) x₀ (left_mem_Icc.mpr hx.le))
  rw [show (1 : ℕ) = 0 + 1 by norm_num]
  rw [taylorWithinEval_succ]
  simp [hderiv, mul_comm]

theorem taylor_remainder_bound_ball_right_explicit
    {f : ℝ → ℝ} {x₀ M r : ℝ} (hf : ContDiff ℝ 2 f) (hr : 0 < r)
    (hM : ∀ y ∈ Icc (x₀ - r) (x₀ + r), |iteratedDeriv 2 f y| ≤ M) :
    ∀ x ∈ Icc x₀ (x₀ + r),
      |f x - (f x₀ + deriv f x₀ * (x - x₀))| ≤ (M / 2) * r ^ 2 := by
  have hnonnegM : 0 ≤ M := by
    have hx₀mem : x₀ ∈ Icc (x₀ - r) (x₀ + r) := by constructor <;> linarith [hr]
    exact (abs_nonneg (iteratedDeriv 2 f x₀)).trans (hM x₀ hx₀mem)
  intro x hx
  rcases lt_or_eq_of_le hx.1 with hlt | rfl
  · have hM' : ∀ y ∈ Icc x₀ x, |iteratedDeriv 2 f y| ≤ M := by
      intro y hy
      exact hM y ⟨by linarith [hr, hy.1], by linarith [hy.2, hx.2]⟩
    have hright := taylor_remainder_bound_right (f := f) (x₀ := x₀) (x := x)
        (M := M) hf hlt hM'
    have hexp := taylorWithinEval_one_eq (f := f) hf hlt
    have hsq : (x - x₀) ^ 2 ≤ r ^ 2 := by
      nlinarith [sub_nonneg.mpr hx.1, sub_le_iff_le_add'.mpr hx.2]
    calc
      |f x - (f x₀ + deriv f x₀ * (x - x₀))|
          = |f x - taylorWithinEval f 1 (Icc x₀ x) x₀ x| := by rw [hexp]
      _ ≤ (M / 2) * (x - x₀) ^ 2 := hright
      _ ≤ (M / 2) * r ^ 2 := mul_le_mul_of_nonneg_left hsq (by linarith)
  · simp [mul_nonneg (by linarith : 0 ≤ M / 2) (sq_nonneg r)]
