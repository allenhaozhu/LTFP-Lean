/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Normed.Module.Multilinear.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Multivariate Hessian Taylor remainder via line-restriction

Given a globally `ContDiff ℝ 2` function `f : E → ℝ` on a real normed
space and two points `x₀ x₁ : E`, if the operator norm of the Hessian
`iteratedFDeriv ℝ 2 f` is bounded by `L` on the segment `[x₀, x₁]`,
then

  `|f x₁ - f x₀ - (fderiv ℝ f x₀) (x₁ - x₀)| ≤ (L / 2) * ‖x₁ - x₀‖^2`.

The proof reduces to the one-dimensional Lagrange form of the Taylor
remainder for the line-restriction `g(t) := f (x₀ + t • (x₁ - x₀))`.
The chain rule expresses `iteratedFDeriv ℝ 2 g t` as the Hessian of
`f` post-composed with the rank-one map `t ↦ t • d`, whose norm
equals `‖d‖`. This gives the sharp `(L/2) * ‖d‖^2` constant.

This lemma is used downstream by the B8 N5 framework's `hbridge`
hypothesis.
-/

namespace LTFP.MathlibExt.Calculus

open Set ContinuousLinearMap

/-- Multivariate Hessian Taylor remainder along the segment `[x₀, x₁]`.

For `f : E → ℝ` of class `C²` on a real normed space, if the operator
norm of the Hessian is bounded by `L` along the closed segment, then
the first-order remainder of `f` at `x₀` evaluated at `x₁` is at most
`(L/2) * ‖x₁ - x₀‖²` in absolute value. -/
theorem hessian_taylor_remainder_along_segment
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} {x₀ x₁ : E} {L : ℝ}
    (hf : ContDiff ℝ 2 f)
    (hH : ∀ z ∈ segment ℝ x₀ x₁,
        ‖iteratedFDeriv ℝ 2 f z‖ ≤ L) :
    |f x₁ - f x₀ - (fderiv ℝ f x₀) (x₁ - x₀)|
      ≤ (L / 2) * ‖x₁ - x₀‖ ^ 2 := by
  -- Set up notation for the displacement and the line restriction.
  set d : E := x₁ - x₀ with hd_def
  -- `Ld : ℝ →L[ℝ] E`, `Ld t = t • d`, `‖Ld‖ = ‖d‖`.
  set Ld : ℝ →L[ℝ] E := ContinuousLinearMap.toSpanSingleton ℝ d with hLd_def
  -- The affine line through `x₀` in direction `d`.
  set φ : ℝ → E := fun t => x₀ + Ld t with hφ_def
  -- The line-restriction `g(t) = f(x₀ + t • d)`.
  set g : ℝ → ℝ := f ∘ φ with hg_def
  -- Norm of `Ld` equals `‖d‖`.
  have hLd_norm : ‖Ld‖ = ‖d‖ := ContinuousLinearMap.norm_toSpanSingleton (𝕜 := ℝ) d
  -- `φ` is `C^∞`, hence `C²`.
  have hLd_contDiff : ContDiff ℝ 2 (fun t : ℝ => Ld t) := Ld.contDiff
  have hConst_contDiff : ContDiff ℝ 2 (fun _ : ℝ => x₀) := contDiff_const
  have hφ_contDiff : ContDiff ℝ 2 φ := by
    show ContDiff ℝ 2 (fun t : ℝ => x₀ + Ld t)
    exact hConst_contDiff.add hLd_contDiff
  -- `g = f ∘ φ` is `C²`.
  have hg_contDiff : ContDiff ℝ 2 g := hf.comp hφ_contDiff
  -- `g` is `ContDiffOn` on `Icc 0 1`.
  have hg_contDiffOn : ContDiffOn ℝ ((1 : ℕ) + 1) g (Icc (0 : ℝ) 1) := by
    simpa using hg_contDiff.contDiffOn
  -- Apply 1D Lagrange remainder to `g` on `[0, 1]` with `n = 1`.
  obtain ⟨ξ, hξIoo, hrem⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (f := g) (x := (1 : ℝ))
      (x₀ := (0 : ℝ)) (n := 1) (by norm_num) hg_contDiffOn
  -- Identify `g 0 = f x₀`, `g 1 = f x₁`.
  have hg0 : g 0 = f x₀ := by
    simp [hg_def, hφ_def, hLd_def, ContinuousLinearMap.toSpanSingleton_apply]
  have hg1 : g 1 = f x₁ := by
    simp [hg_def, hφ_def, hLd_def, ContinuousLinearMap.toSpanSingleton_apply,
      hd_def]
  -- Compute `taylorWithinEval g 1 (Icc 0 1) 0 1`.
  -- It equals `g 0 + iteratedDerivWithin 1 g (Icc 0 1) 0 = f x₀ + g'(0)`.
  -- We then identify `g'(0) = (fderiv ℝ f x₀) d` via chain rule.
  have hg_deriv0 : deriv g 0 = (fderiv ℝ f x₀) d := by
    have h_const : HasDerivAt (fun _ : ℝ => x₀) (0 : E) 0 := hasDerivAt_const _ _
    have h_lin : HasDerivAt (fun t : ℝ => Ld t) d 0 := by
      have h := Ld.hasFDerivAt (x := (0 : ℝ)) |>.hasDerivAt
      have hLd1 : Ld 1 = d := by
        simp [hLd_def, ContinuousLinearMap.toSpanSingleton_apply]
      rw [hLd1] at h
      exact h
    have hφ_hasDeriv : HasDerivAt φ d 0 := by
      have h_sum : HasDerivAt (fun t : ℝ => x₀ + Ld t) (0 + d) 0 := h_const.add h_lin
      simpa [hφ_def, zero_add] using h_sum
    have hf_diff : Differentiable ℝ f := hf.differentiable (by norm_num)
    have hf_hasFDeriv : HasFDerivAt f (fderiv ℝ f (φ 0)) (φ 0) :=
      hf_diff.differentiableAt.hasFDerivAt
    have hg_hasDeriv : HasDerivAt g ((fderiv ℝ f (φ 0)) d) 0 :=
      hf_hasFDeriv.comp_hasDerivAt 0 hφ_hasDeriv
    have hφ0 : φ 0 = x₀ := by
      simp [hφ_def, hLd_def, ContinuousLinearMap.toSpanSingleton_apply]
    rw [hφ0] at hg_hasDeriv
    exact hg_hasDeriv.deriv
  -- `taylorWithinEval g 1 (Icc 0 1) 0 1 = g 0 + 1 * deriv g 0 = f x₀ + (fderiv ℝ f x₀) d`.
  have h_taylor1 : taylorWithinEval g 1 (Icc (0 : ℝ) 1) 0 1 = f x₀ + (fderiv ℝ f x₀) d := by
    have hu : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc (by norm_num : (0 : ℝ) < 1)
    have h0mem : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
    -- Unfold one step of `taylorWithinEval`.
    rw [show (1 : ℕ) = 0 + 1 from rfl, taylorWithinEval_succ, taylor_within_zero_eval]
    -- Now we have `g 0 + ((0+1) * 0!)⁻¹ * (1-0)^(0+1) • iteratedDerivWithin 1 g (Icc 0 1) 0`.
    -- This simplifies to `g 0 + iteratedDerivWithin 1 g (Icc 0 1) 0`.
    -- `iteratedDerivWithin 1 g (Icc 0 1) 0 = derivWithin g (Icc 0 1) 0 = deriv g 0`.
    have hg_diff : Differentiable ℝ g := hg_contDiff.differentiable (by norm_num)
    have hd1 : iteratedDerivWithin 1 g (Icc (0 : ℝ) 1) 0 = deriv g 0 := by
      rw [iteratedDerivWithin_one]
      exact hg_diff.differentiableAt.derivWithin (hu 0 h0mem)
    rw [hd1, hg0, hg_deriv0]
    -- Coefficient: `((0+1) * 0!)⁻¹ * (1-0)^(0+1) = 1`.
    simp
  -- Bound the second iterated derivative of `g` at `ξ`.
  -- Step: identify `iteratedFDeriv ℝ 2 g ξ` via chain rule and bound by `‖iteratedFDeriv ℝ 2 f (φ ξ)‖ * ‖d‖^2`.
  -- We use: `g = h ∘ Ld` where `h y := f (x₀ + y)`. Then
  --   `iteratedFDeriv ℝ 2 g = iteratedFDeriv ℝ 2 h (Ld ·) .compContinuousLinearMap (fun _ => Ld)`,
  --   `iteratedFDeriv ℝ 2 h y = iteratedFDeriv ℝ 2 f (x₀ + y)`.
  set h : E → ℝ := fun y => f (x₀ + y) with hh_def
  have hh_contDiff : ContDiff ℝ 2 h := by
    have hConstE : ContDiff ℝ 2 (fun _ : E => x₀) := contDiff_const
    have hIdE : ContDiff ℝ 2 (fun y : E => y) := contDiff_id
    have hshift : ContDiff ℝ 2 (fun y : E => x₀ + y) := hConstE.add hIdE
    exact hf.comp hshift
  have hg_eq_hL : g = h ∘ Ld := by
    funext t
    simp [hg_def, hh_def, hφ_def]
  have hh_iter : ∀ y : E, iteratedFDeriv ℝ 2 h y = iteratedFDeriv ℝ 2 f (x₀ + y) := by
    intro y
    simpa [hh_def] using iteratedFDeriv_comp_add_left (f := f) 2 x₀ y
  have hg_iter : ∀ t : ℝ, iteratedFDeriv ℝ 2 g t =
      (iteratedFDeriv ℝ 2 f (φ t)).compContinuousLinearMap (fun _ : Fin 2 => Ld) := by
    intro t
    rw [hg_eq_hL]
    rw [Ld.iteratedFDeriv_comp_right (f := h) hh_contDiff t (le_refl 2)]
    rw [hh_iter (Ld t)]
  -- Norm bound on `iteratedFDeriv ℝ 2 g ξ`.
  have h_norm_g : ‖iteratedFDeriv ℝ 2 g ξ‖ ≤ ‖iteratedFDeriv ℝ 2 f (φ ξ)‖ * ‖d‖ ^ 2 := by
    rw [hg_iter]
    calc ‖(iteratedFDeriv ℝ 2 f (φ ξ)).compContinuousLinearMap (fun _ : Fin 2 => Ld)‖
        ≤ ‖iteratedFDeriv ℝ 2 f (φ ξ)‖ * ∏ _i : Fin 2, ‖Ld‖ :=
          ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _
      _ = ‖iteratedFDeriv ℝ 2 f (φ ξ)‖ * ‖Ld‖ ^ 2 := by
          rw [Finset.prod_const]; simp
      _ = ‖iteratedFDeriv ℝ 2 f (φ ξ)‖ * ‖d‖ ^ 2 := by rw [hLd_norm]
  -- `φ ξ ∈ segment ℝ x₀ x₁` for `ξ ∈ Ioo 0 1`.
  have hφξ_seg : φ ξ ∈ segment ℝ x₀ x₁ := by
    refine ⟨1 - ξ, ξ, ?_, le_of_lt hξIoo.1, ?_, ?_⟩
    · linarith [hξIoo.2]
    · linarith [hξIoo.1, hξIoo.2]
    · -- `(1 - ξ) • x₀ + ξ • x₁ = x₀ + ξ • (x₁ - x₀) = φ ξ`.
      simp [hφ_def, hLd_def, ContinuousLinearMap.toSpanSingleton_apply, hd_def,
        smul_sub, sub_smul, one_smul]
      abel
  have h_iter_le_L : ‖iteratedFDeriv ℝ 2 f (φ ξ)‖ ≤ L := hH (φ ξ) hφξ_seg
  have hd_nonneg : (0 : ℝ) ≤ ‖d‖ ^ 2 := sq_nonneg _
  have h_norm_g_le_Ld2 : ‖iteratedFDeriv ℝ 2 g ξ‖ ≤ L * ‖d‖ ^ 2 := by
    calc ‖iteratedFDeriv ℝ 2 g ξ‖
        ≤ ‖iteratedFDeriv ℝ 2 f (φ ξ)‖ * ‖d‖ ^ 2 := h_norm_g
      _ ≤ L * ‖d‖ ^ 2 := mul_le_mul_of_nonneg_right h_iter_le_L hd_nonneg
  -- `|iteratedDeriv 2 g ξ| = ‖iteratedFDeriv ℝ 2 g ξ‖` in 1D.
  have h_iterDeriv_eq : |iteratedDeriv 2 g ξ| = ‖iteratedFDeriv ℝ 2 g ξ‖ := by
    rw [← Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  -- Now assemble.
  rw [hg1, h_taylor1] at hrem
  -- Simplify the right-hand side of `hrem`.
  -- `hrem : f x₁ - (f x₀ + (fderiv ℝ f x₀) d) = iteratedDeriv 2 g ξ * (1 - 0)^(1+1) / (1+1)!`
  -- `(1 - 0)^(1+1) / (1+1)! = 1 / 2`.
  have hrem' : f x₁ - (f x₀ + (fderiv ℝ f x₀) d) = iteratedDeriv 2 g ξ / 2 := by
    have := hrem
    simp [Nat.factorial] at this
    linarith
  -- Take absolute values.
  have : |f x₁ - (f x₀ + (fderiv ℝ f x₀) d)| = |iteratedDeriv 2 g ξ| / 2 := by
    rw [hrem']
    rw [abs_div]; congr 1
    exact abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
  rw [show f x₁ - f x₀ - (fderiv ℝ f x₀) (x₁ - x₀)
      = f x₁ - (f x₀ + (fderiv ℝ f x₀) d) by rw [hd_def]; ring, this]
  rw [h_iterDeriv_eq]
  -- `‖iteratedFDeriv ℝ 2 g ξ‖ / 2 ≤ (L * ‖d‖^2) / 2 = (L/2) * ‖d‖^2`.
  have : ‖iteratedFDeriv ℝ 2 g ξ‖ / 2 ≤ L * ‖d‖ ^ 2 / 2 :=
    div_le_div_of_nonneg_right h_norm_g_le_Ld2 (by norm_num)
  refine this.trans ?_
  rw [hd_def]
  ring_nf
  rfl

/-- Zero-displacement corollary: the Hessian Taylor remainder vanishes at `x₁ = x₀`.

This is an instantiation of `hessian_taylor_remainder_along_segment` at the
degenerate segment `[x₀, x₀] = {x₀}`. The bound is trivial (both sides are 0),
but the equality form is sometimes useful for rewriting in downstream callers
(e.g. base cases of inductive arguments on displacement). -/
theorem hessian_taylor_remainder_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (x₀ : E) :
    |f x₀ - f x₀ - (fderiv ℝ f x₀) (x₀ - x₀)| = 0 := by
  simp

/-- Named EuclideanSpace specialization of `hessian_taylor_remainder_along_segment`.

For `f : EuclideanSpace ℝ (Fin n) → ℝ` of class `C²`, if the Hessian operator
norm is bounded by `L` along the segment `[x₀, x₁]`, then the first-order
remainder of `f` at `x₀` evaluated at `x₁` is at most `(L/2) * ‖x₁ - x₀‖²`.

Convenience wrapper for downstream NTK lazy-linearization callers that work
with `EuclideanSpace ℝ (Fin n)` rather than a generic real normed space. -/
theorem hessian_taylor_remainder_along_segment_euclidean
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x₀ x₁ : EuclideanSpace ℝ (Fin n)} {L : ℝ}
    (hf : ContDiff ℝ 2 f)
    (hH : ∀ z ∈ segment ℝ x₀ x₁,
        ‖iteratedFDeriv ℝ 2 f z‖ ≤ L) :
    |f x₁ - f x₀ - (fderiv ℝ f x₀) (x₁ - x₀)|
      ≤ (L / 2) * ‖x₁ - x₀‖ ^ 2 :=
  hessian_taylor_remainder_along_segment hf hH

end LTFP.MathlibExt.Calculus
