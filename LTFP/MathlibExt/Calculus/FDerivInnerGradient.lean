/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Riesz bridge: `fderiv` and the gradient on a real Hilbert space

On a real Hilbert space `E`, the Riesz representation identifies the
Fréchet derivative `fderiv ℝ f x : E →L[ℝ] ℝ` of a differentiable
real-valued function `f : E → ℝ` with the inner product against the
gradient vector `gradient f x : E`. Mathlib provides this in the
`inner_gradient_left` orientation:

  `⟪gradient f x, y⟫ = fderiv ℝ f x y`.

Downstream LTFP-Lean clients (notably §56's
`ntk_concentration_to_lazy_linearization_via_hessian_bound`) need the
reverse orientation:

  `fderiv ℝ f x v = ⟪gradient f x, v⟫`,

and a convenient packaging when the only available regularity is
`ContDiff ℝ 2 f`. This file provides both wrappers.
-/

open scoped RealInnerProductSpace
open scoped Gradient

namespace LTFP.MathlibExt.Calculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Riesz bridge in the `fderiv = ⟪gradient, ·⟫` orientation.

This is just `Mathlib.Analysis.Calculus.Gradient.Basic.inner_gradient_left`
with sides swapped, packaged for downstream LTFP clients that consume the
Riesz bridge in this direction. -/
theorem fderiv_eq_inner_gradient
    {f : E → ℝ} {x : E} (h : DifferentiableAt ℝ f x) (v : E) :
    fderiv ℝ f x v = inner ℝ (gradient f x) v :=
  (inner_gradient_left h).symm

/-- Riesz bridge when the only available regularity is `ContDiff ℝ 2 f`.

`ContDiff ℝ 2 f` implies `Differentiable ℝ f` via `ContDiff.differentiable`
(`n ≠ 0`), and hence `DifferentiableAt ℝ f x` at every point. We then
apply `fderiv_eq_inner_gradient`. -/
theorem fderiv_eq_inner_gradient_of_contDiff
    {f : E → ℝ} (hf : ContDiff ℝ 2 f) (x v : E) :
    fderiv ℝ f x v = inner ℝ (gradient f x) v :=
  fderiv_eq_inner_gradient (hf.differentiable (by norm_num) x) v

end LTFP.MathlibExt.Calculus
