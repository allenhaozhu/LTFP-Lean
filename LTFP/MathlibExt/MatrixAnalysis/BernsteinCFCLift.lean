/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Analysis.Exp.BernsteinRemainder
import LTFP.MathlibExt.MatrixAnalysis.MatrixCFCContinuity
import LTFP.MathlibExt.MatrixAnalysis.MatrixExpPositivity
import LTFP.MathlibExt.MatrixAnalysis.LiebTraceComplementary
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Hermitian CFC lift of the Bennett-Bernstein remainder bound

This module lifts the scalar Bennett-Bernstein remainder bound

  `Real.exp y ≤ 1 + y + y^2 / (2 * (1 - b / 3))`   for `|y| ≤ b` with `0 ≤ b < 3`

(see `Real.exp_le_one_add_self_add_sq_div_of_abs_le` in
`LTFP/MathlibExt/Analysis/Exp/BernsteinRemainder.lean`) to a **Loewner**
operator inequality on Hermitian matrices via the continuous functional
calculus.

For a Hermitian matrix `X : Matrix n n ℂ` with `‖X‖ ≤ R`, and real scalars
`0 ≤ θ`, `0 ≤ R`, `θ * R < 3`, we have

  `exp (θ • X) ≤ 1 + θ • X + (θ² / (2 (1 - θR/3))) • (X * X)`

in the Loewner order on `Matrix n n ℂ` (under the `MatrixOrder` scope).

## Proof strategy

We apply `cfc_mono` (monotonicity of the continuous functional calculus
on the Loewner order) to the two functions

  `f x = Real.exp (θ * x)`,   `g x = 1 + θ * x + c * x^2`,

where `c := θ^2 / (2 * (1 - θR/3))`.  The pointwise inequality
`f x ≤ g x` for `x ∈ spectrum ℝ X` reduces, via the scalar bound, to
the hypothesis `|θ * x| ≤ θ * R < 3`, which holds because

* `|x| ≤ ‖X‖ ≤ R`  (for `x` real eigenvalues of a Hermitian `X` in a
  C⋆-algebra with norm `‖·‖` from the L2-operator scope);
* `θ ≥ 0`;
* `θ * R < 3`.

The LHS `cfc (Real.exp ∘ (θ * ·)) X = cfc Real.exp (θ • X) = exp (θ • X)`
via `cfc_comp_const_mul` and `CFC.real_exp_eq_normedSpace_exp`.

The RHS decomposes by linearity of `cfc`:

* `cfc (1 + θ * x) X = 1 + θ • X`  via `cfc_const_add` and `cfc_const_mul_id`;
* `cfc (c * x^2) X  = c • (X * X)`  via `cfc_const_mul` and `cfc_pow_id` (with `sq`).

## Main result

* `Matrix.exp_smul_le_one_add_smul_add_sq_smul_of_hermitian_norm_le` —
  the Bennett-Bernstein remainder bound, lifted to Hermitian matrices.

## References

* The scalar bound `Real.exp_le_one_add_self_add_sq_div_of_abs_le`
  in Part 8a of the matrix Bernstein chain.
* The continuous functional calculus monotonicity
  `Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital.cfc_mono`.
* The CFC/`NormedSpace.exp` bridge
  `Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic.CFC.real_exp_eq_normedSpace_exp`.
-/

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-! ### Spectrum bound for a Hermitian matrix from the operator norm -/

/-- For a Hermitian matrix `X : Matrix n n ℂ` with `‖X‖ ≤ R`, every real
spectrum element `x` satisfies `|x| ≤ R`.

This is the `ℝ`-spectrum form of the standard C⋆-algebra spectrum bound
`spectrum.norm_le_norm_of_mem`, transported through the canonical
embedding `spectrum ℝ X → spectrum ℂ X` (`spectrum.algebraMap_mem_iff`),
and using `‖(x : ℂ)‖ = |x|` (`Complex.norm_ofReal`).
-/
lemma abs_le_of_mem_spectrum_real_of_hermitian
    {X : Matrix n n ℂ} (_hX : X.IsHermitian)
    {R : ℝ} (hbound : ‖X‖ ≤ R)
    {x : ℝ} (hx : x ∈ spectrum ℝ X) :
    |x| ≤ R := by
  -- `(x : ℂ) ∈ spectrum ℂ X` via `algebraMap_mem`.
  have hx_C : (x : ℂ) ∈ spectrum ℂ X := by
    have := (spectrum.algebraMap_mem_iff ℂ (R := ℝ) (A := Matrix n n ℂ)
      (a := X) (r := x)).mpr hx
    simpa using this
  -- Spectrum bound: `‖(x : ℂ)‖ ≤ ‖X‖` (using `NormOneClass`).
  have h_norm : ‖(x : ℂ)‖ ≤ ‖X‖ := spectrum.norm_le_norm_of_mem hx_C
  -- `‖(x : ℂ)‖ = |x|`.
  have h_eq : ‖(x : ℂ)‖ = |x| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  -- Chain.
  linarith [h_eq ▸ h_norm]

/-! ### Pointwise scalar inequality on the spectrum -/

/-- The pointwise form of the Bennett-Bernstein inequality, specialised to
`y = θ * x` with `|x| ≤ R`, `0 ≤ θ`, `0 ≤ R`, `θ * R < 3`.

This is the scalar input to `cfc_mono` in the main lift below.
-/
private lemma exp_theta_mul_le_of_abs_le
    {R θ : ℝ} (hR : 0 ≤ R) (hθ : 0 ≤ θ) (hθR : θ * R < 3)
    {x : ℝ} (hx : |x| ≤ R) :
    Real.exp (θ * x) ≤
      1 + θ * x + θ ^ 2 / (2 * (1 - θ * R / 3)) * x ^ 2 := by
  -- Set `y := θ * x`, `b := θ * R`.
  set y : ℝ := θ * x
  set b : ℝ := θ * R
  have hb0 : 0 ≤ b := mul_nonneg hθ hR
  have hb3 : b < 3 := hθR
  have habs_x : |x| ≤ R := hx
  -- `|y| = |θ| * |x| = θ * |x| ≤ θ * R = b`.
  have hy_abs : |y| ≤ b := by
    have habsy : |y| = θ * |x| := by
      rw [show y = θ * x from rfl, abs_mul, abs_of_nonneg hθ]
    rw [habsy]
    exact mul_le_mul_of_nonneg_left habs_x hθ
  -- Apply Part 8a.
  have h_scalar := Real.exp_le_one_add_self_add_sq_div_of_abs_le hb0 hb3 hy_abs
  -- The bound: `Real.exp y ≤ 1 + y + y^2 / (2 * (1 - b / 3))`.
  -- We rewrite `y^2 = (θ * x)^2 = θ^2 * x^2` and pull out the coefficient.
  have h_alg :
      y ^ 2 / (2 * (1 - b / 3))
        = θ ^ 2 / (2 * (1 - θ * R / 3)) * x ^ 2 := by
    show (θ * x) ^ 2 / (2 * (1 - θ * R / 3))
        = θ ^ 2 / (2 * (1 - θ * R / 3)) * x ^ 2
    ring
  linarith [h_scalar, h_alg.symm]

/-! ### Main result: Hermitian CFC lift -/

set_option maxHeartbeats 800000 in
/-- **Bennett-Bernstein remainder bound, lifted to Hermitian matrices.**

For a Hermitian matrix `X : Matrix n n ℂ` with `‖X‖ ≤ R`, and real scalars
`0 ≤ R`, `0 ≤ θ`, `θ * R < 3`, the matrix exponential satisfies the
Loewner inequality

  `NormedSpace.exp (θ • X) ≤ 1 + θ • X + (θ^2 / (2 * (1 - θ * R / 3))) • (X * X)`.

The proof is a direct application of `cfc_mono` (monotonicity of the
continuous functional calculus on the Loewner order) to the scalar
Bennett-Bernstein bound `Real.exp_le_one_add_self_add_sq_div_of_abs_le`,
using

* `cfc_comp_const_mul` to identify `cfc (Real.exp ∘ (θ * ·)) X` with
  `cfc Real.exp (θ • X)`;
* `CFC.real_exp_eq_normedSpace_exp` to identify the latter with
  `NormedSpace.exp (θ • X)`;
* `cfc_add`, `cfc_const_add`, `cfc_const_mul`, `cfc_pow_id` to expand the
  affine-plus-quadratic RHS as `1 + θ • X + c • (X * X)`.
-/
theorem exp_smul_le_one_add_smul_add_sq_smul_of_hermitian_norm_le
    {X : Matrix n n ℂ} (hX : X.IsHermitian)
    {R θ : ℝ} (hR : 0 ≤ R) (hθ : 0 ≤ θ) (hθR : θ * R < 3)
    (hbound : ‖X‖ ≤ R) :
    NormedSpace.exp ((θ : ℝ) • X)
      ≤ (1 : Matrix n n ℂ) + (θ : ℝ) • X +
        (θ ^ 2 / (2 * (1 - θ * R / 3))) • (X * X) := by
  -- Coefficient name.
  set c : ℝ := θ ^ 2 / (2 * (1 - θ * R / 3)) with hc_def
  -- `X` is self-adjoint as a C⋆-algebra element.
  have hX_sa : IsSelfAdjoint X := hX.isSelfAdjoint
  -- Spectrum bound: `∀ x ∈ spectrum ℝ X, |x| ≤ R`.
  have h_spec : ∀ x ∈ spectrum ℝ X, |x| ≤ R :=
    fun x hx => abs_le_of_mem_spectrum_real_of_hermitian hX hbound hx
  -- The two functions for `cfc_mono`.
  let f : ℝ → ℝ := fun x => Real.exp (θ * x)
  let g : ℝ → ℝ := fun x => 1 + θ * x + c * x ^ 2
  -- Continuity of `f` and `g` on `ℝ` (hence on the spectrum).
  have hf_cont : Continuous f := by show Continuous (fun x : ℝ => Real.exp (θ * x)); fun_prop
  have hg_cont : Continuous g := by
    show Continuous (fun x : ℝ => 1 + θ * x + c * x ^ 2); fun_prop
  -- Pointwise inequality on the spectrum.
  have h_point : ∀ x ∈ spectrum ℝ X, f x ≤ g x := by
    intro x hx
    have habs := h_spec x hx
    show Real.exp (θ * x) ≤ 1 + θ * x + c * x ^ 2
    have h := exp_theta_mul_le_of_abs_le hR hθ hθR habs
    -- Match `c` with the explicit coefficient.
    show Real.exp (θ * x) ≤ 1 + θ * x + c * x ^ 2
    have : c = θ ^ 2 / (2 * (1 - θ * R / 3)) := hc_def
    rw [this]
    linarith
  -- Apply `cfc_mono`.
  have h_cfc_mono : cfc f X ≤ cfc g X :=
    cfc_mono (a := X) (f := f) (g := g) h_point hf_cont.continuousOn hg_cont.continuousOn
  -- Identify LHS: `cfc f X = NormedSpace.exp (θ • X)`.
  have h_LHS : cfc f X = NormedSpace.exp ((θ : ℝ) • X) := by
    -- `f = (fun x => Real.exp (θ * x)) = Real.exp ∘ (θ * ·)`.
    -- `cfc (Real.exp ∘ (θ * ·)) X = cfc Real.exp (θ • X)` (cfc_comp_const_mul).
    -- `cfc Real.exp (θ • X) = NormedSpace.exp (θ • X)` (real_exp_eq_normedSpace_exp).
    show cfc (fun x : ℝ => Real.exp (θ * x)) X = NormedSpace.exp ((θ : ℝ) • X)
    have hsmul_sa : IsSelfAdjoint ((θ : ℝ) • X) :=
      (IsSelfAdjoint.all θ).smul hX_sa
    have hcomp :
        cfc (fun x : ℝ => Real.exp (θ * x)) X
          = cfc Real.exp ((θ : ℝ) • X) := by
      -- `cfc_comp_const_mul` with `r := θ`, `f := Real.exp`.
      have := cfc_comp_const_mul (R := ℝ) (A := Matrix n n ℂ) (p := IsSelfAdjoint)
        (r := θ) (f := Real.exp) (a := X)
        (by exact Real.continuous_exp.continuousOn) hX_sa
      -- The conclusion is exactly `cfc (Real.exp <| θ * ·) X = cfc Real.exp (θ • X)`.
      exact this
    rw [hcomp]
    -- `cfc Real.exp (θ • X) = NormedSpace.exp (θ • X)`.
    exact CFC.real_exp_eq_normedSpace_exp (a := (θ : ℝ) • X) hsmul_sa
  -- Identify RHS: `cfc g X = 1 + θ • X + c • (X * X)`.
  have h_RHS : cfc g X
      = (1 : Matrix n n ℂ) + (θ : ℝ) • X + c • (X * X) := by
    show cfc (fun x : ℝ => 1 + θ * x + c * x ^ 2) X
        = (1 : Matrix n n ℂ) + (θ : ℝ) • X + c • (X * X)
    -- Continuity of the two parts.
    have h_part1 : Continuous (fun x : ℝ => 1 + θ * x) := by fun_prop
    have h_part2 : Continuous (fun x : ℝ => c * x ^ 2) := by fun_prop
    -- Split as `(1 + θ * x) + (c * x^2)`.
    have h_split :
        (fun x : ℝ => 1 + θ * x + c * x ^ 2)
          = (fun x : ℝ => (fun y => 1 + θ * y) x + (fun y => c * y ^ 2) x) := by
      funext x; ring
    rw [h_split]
    rw [cfc_add (a := X) (f := fun y : ℝ => 1 + θ * y) (g := fun y : ℝ => c * y ^ 2)
        h_part1.continuousOn h_part2.continuousOn]
    -- Affine part: `cfc (fun y => 1 + θ * y) X = 1 + θ • X`.
    have h_aff : cfc (fun y : ℝ => 1 + θ * y) X
        = (1 : Matrix n n ℂ) + (θ : ℝ) • X := by
      have hcm : Continuous (fun y : ℝ => θ * y) := by fun_prop
      rw [cfc_const_add (R := ℝ) (a := X) (r := 1) (f := fun y : ℝ => θ * y)
          hcm.continuousOn hX_sa]
      -- `cfc (fun y => θ * y) X = θ • X` via `cfc_const_mul_id`.
      have : cfc (fun y : ℝ => θ * y) X = (θ : ℝ) • X :=
        cfc_const_mul_id (R := ℝ) (A := Matrix n n ℂ) (p := IsSelfAdjoint)
          (r := θ) (a := X) hX_sa
      rw [this]
      -- `algebraMap ℝ (Matrix n n ℂ) 1 = 1`.
      simp
    -- Quadratic part: `cfc (fun y => c * y^2) X = c • (X * X)`.
    have h_quad : cfc (fun y : ℝ => c * y ^ 2) X = c • (X * X) := by
      -- Step 1: pull out the constant `c` via `cfc_const_mul`.
      have hpow_cont : Continuous (fun y : ℝ => y ^ 2) := by fun_prop
      have hstep1 : cfc (fun y : ℝ => c * y ^ 2) X = c • cfc (fun y : ℝ => y ^ 2) X :=
        cfc_const_mul (R := ℝ) (A := Matrix n n ℂ) (p := IsSelfAdjoint)
          (r := c) (f := fun y : ℝ => y ^ 2) (a := X) hpow_cont.continuousOn
      rw [hstep1]
      -- Step 2: `cfc (fun y => y^2) X = X^2 = X * X`.
      have hstep2 : cfc (fun y : ℝ => y ^ 2) X = X * X := by
        have : cfc (fun y : ℝ => y ^ 2) X = X ^ 2 :=
          cfc_pow_id (R := ℝ) (A := Matrix n n ℂ) (p := IsSelfAdjoint)
            (a := X) (n := 2) hX_sa
        rw [this, sq]
      rw [hstep2]
    rw [h_aff, h_quad]
  -- Combine: `LHS ≤ RHS` via `cfc_mono`.
  calc NormedSpace.exp ((θ : ℝ) • X)
      = cfc f X := h_LHS.symm
    _ ≤ cfc g X := h_cfc_mono
    _ = (1 : Matrix n n ℂ) + (θ : ℝ) • X + c • (X * X) := h_RHS

end Matrix
