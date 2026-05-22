/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Calculus.TaylorRemainderRightSided
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Taylor remainder bound on a right-half ball with explicit polynomial

Bridge from round 19's `taylor_remainder_bound_right` (which keeps the
Mathlib `taylorWithinEval f 1 ...` polynomial) to the downstream-usable
explicit form `f x₀ + deriv f x₀ * (x - x₀)`, and to the symmetric ball
form bounded by the radius squared.

The right-half is proved directly; the two-sided ball form follows by
reflecting through the center `t ↦ 2 * x₀ - t` and reusing the right-half
bound.
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

lemma iteratedDeriv_two_reflect {f : ℝ → ℝ} {x₀ x : ℝ} :
    iteratedDeriv 2 (fun t : ℝ => f (2 * x₀ - t)) x =
      iteratedDeriv 2 f (2 * x₀ - x) := by
  let k : ℝ → ℝ := fun z => f (-z)
  have htrans := congr_fun
    (iteratedDeriv_comp_add_const (n := 2) (f := k) (s := -2 * x₀)) x
  have hneg := iteratedDeriv_comp_neg (n := 2) (f := f) (a := x + -2 * x₀)
  dsimp [k] at htrans hneg
  calc
    iteratedDeriv 2 (fun t : ℝ => f (2 * x₀ - t)) x
        = iteratedDeriv 2 (fun z : ℝ => f (-(z + -2 * x₀))) x := by
            congr 2; funext z; congr 1; ring
    _ = iteratedDeriv 2 (fun z : ℝ => f (-z)) (x + -2 * x₀) := htrans
    _ = (-1 : ℝ) ^ 2 * iteratedDeriv 2 f (-(x + -2 * x₀)) := hneg
    _ = iteratedDeriv 2 f (2 * x₀ - x) := by ring_nf

lemma deriv_reflect_at_center {f : ℝ → ℝ} {x₀ : ℝ} (hf : ContDiff ℝ 2 f) :
    deriv (fun t : ℝ => f (2 * x₀ - t)) x₀ = - deriv f x₀ := by
  have hlin : HasDerivAt (fun t : ℝ => 2 * x₀ - t) (-1) x₀ := by
    simpa using (hasDerivAt_const (x := x₀) (c := 2 * x₀)).sub (hasDerivAt_id x₀)
  have hfder0 : HasDerivAt f (deriv f x₀) x₀ :=
    (hf.differentiable (by norm_num : (2 : WithTop ℕ∞) ≠ 0) x₀).hasDerivAt
  have hfder : HasDerivAt f (deriv f x₀) (2 * x₀ - x₀) := by
    convert hfder0 using 1
    ring
  simpa [mul_comm] using (hfder.comp x₀ hlin).deriv

theorem taylor_remainder_bound_ball_two_sided
    {f : ℝ → ℝ} {x₀ M r : ℝ} (hf : ContDiff ℝ 2 f) (hr : 0 < r)
    (hM : ∀ y ∈ Set.Icc (x₀ - r) (x₀ + r), |iteratedDeriv 2 f y| ≤ M) :
    ∀ x ∈ Set.Icc (x₀ - r) (x₀ + r),
      |f x - (f x₀ + deriv f x₀ * (x - x₀))| ≤ (M / 2) * r ^ 2 := by
  intro x hx
  rcases le_total x₀ x with hx₀x | hxx₀
  · exact taylor_remainder_bound_ball_right_explicit hf hr hM x ⟨hx₀x, hx.2⟩
  · let g : ℝ → ℝ := fun t => f (2 * x₀ - t)
    have hg : ContDiff ℝ 2 g :=
      hf.comp (by
        simpa using
          (ContDiff.sub (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => 2 * x₀)) contDiff_id))
    have hMg : ∀ y ∈ Icc (x₀ - r) (x₀ + r), |iteratedDeriv 2 g y| ≤ M := by
      intro y hy
      have hreflect_mem : 2 * x₀ - y ∈ Icc (x₀ - r) (x₀ + r) := by
        constructor <;> linarith [hy.1, hy.2]
      simpa [g, iteratedDeriv_two_reflect] using hM (2 * x₀ - y) hreflect_mem
    let x' : ℝ := 2 * x₀ - x
    have hx' : x' ∈ Icc x₀ (x₀ + r) := by
      constructor <;> dsimp [x'] <;> linarith [hxx₀, hx.1]
    have hbound := taylor_remainder_bound_ball_right_explicit hg hr hMg x' hx'
    have hderiv : deriv g x₀ = - deriv f x₀ := by
      simpa [g] using deriv_reflect_at_center (f := f) (x₀ := x₀) hf
    convert hbound using 1
    dsimp [g, x']; rw [hderiv]; ring_nf
