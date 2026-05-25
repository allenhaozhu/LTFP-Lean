/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.MatrixAnalysis.LiebTraceComplementary
import LTFP.MathlibExt.MatrixAnalysis.PosSemidefClosed
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Norm-to-Loewner bridges for Hermitian / positive-semidefinite matrices

This module provides two small but load-bearing inequalities that lift a
`norm` bound on a matrix to a Loewner-order bound against the identity:

* `Matrix.IsHermitian.sq_le_norm_sq_smul_one` —
  for Hermitian `H : Matrix n n ℂ`,

      `H * H ≤ (‖H‖^2 : ℝ) • (1 : Matrix n n ℂ)`

  in the Loewner order on `Matrix n n ℂ` (under the `MatrixOrder` scope).

* `Matrix.PosSemidef.le_norm_smul_one_of_isHermitian` —
  for positive-semidefinite `M : Matrix n n ℂ`,

      `M ≤ (‖M‖ : ℝ) • (1 : Matrix n n ℂ)`

  in the same order.

These are the bridge inequalities needed to convert NORM-form variance
proxy bounds (of the form `‖∑ ∫ X² ∂ν‖ ≤ σ²`) into the LOEWNER-form
hypothesis `∑ ∫ X·X ∂ν ≤ σ² • 1` consumed by the matrix Bernstein
inequality (`Matrix.bernstein_full`, `Matrix.bernstein_op_norm_full`).

## Proof strategy

Both proofs follow the continuous functional calculus pattern already
used in `BernsteinCFCLift.lean`:

1.  Embed both sides as `cfc f H` for an appropriate function `f`.
2.  Verify the scalar inequality `f x ≤ g x` on the real spectrum
    `spectrum ℝ H ⊆ [-‖H‖, ‖H‖]`.
3.  Apply `cfc_mono` to obtain the Loewner inequality.

For the Hermitian case:
* LHS `= cfc (· ^ 2) H` via `cfc_pow_id`,
* RHS `= cfc (fun _ => ‖H‖^2) H` via `cfc_const` and
  `Algebra.algebraMap_eq_smul_one`,
* Scalar inequality: for `x ∈ spectrum ℝ H`, `|x| ≤ ‖H‖`, so
  `x^2 ≤ ‖H‖^2`.

For the PosSemidef case the simpler route is direct: the Mathlib lemma
`IsSelfAdjoint.le_algebraMap_norm_self` (from
`Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Order.lean`)
already gives `a ≤ algebraMap ℝ A ‖a‖`, and
`Algebra.algebraMap_eq_smul_one` converts `algebraMap ℝ A ‖a‖` to
`‖a‖ • 1`.

## References

* `Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order` —
  `IsSelfAdjoint.le_algebraMap_norm_self` and `cfc_mono`.
* `Mathlib.Analysis.Matrix.Order` — Loewner order on `Matrix n n ℂ`,
  scoped to `MatrixOrder`.
* `LTFP.MathlibExt.MatrixAnalysis.LiebTraceComplementary` — `CStarAlgebra`
  instance on `Matrix n n ℂ` under the L2 operator norm, scoped to
  `Matrix.Norms.L2Operator`.
-/

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-! ### Spectrum-vs-norm bound for Hermitian matrices -/

/-- For a Hermitian matrix `H : Matrix n n ℂ` and any real spectrum
element `x`, we have `|x| ≤ ‖H‖`.

This is the `ℝ`-spectrum form of the standard C⋆-algebra spectrum bound
`spectrum.norm_le_norm_of_mem`, transported through the canonical
embedding `spectrum ℝ H → spectrum ℂ H` (`spectrum.algebraMap_mem_iff`),
and using `‖(x : ℂ)‖ = |x|` (`Complex.norm_real`).
-/
private lemma abs_le_norm_of_mem_spectrum_real_of_hermitian
    {H : Matrix n n ℂ} (_hH : H.IsHermitian)
    {x : ℝ} (hx : x ∈ spectrum ℝ H) :
    |x| ≤ ‖H‖ := by
  -- `(x : ℂ) ∈ spectrum ℂ H` via `algebraMap_mem`.
  have hx_C : (x : ℂ) ∈ spectrum ℂ H := by
    have := (spectrum.algebraMap_mem_iff ℂ (R := ℝ) (A := Matrix n n ℂ)
      (a := H) (r := x)).mpr hx
    simpa using this
  -- Spectrum bound: `‖(x : ℂ)‖ ≤ ‖H‖`.
  have h_norm : ‖(x : ℂ)‖ ≤ ‖H‖ := spectrum.norm_le_norm_of_mem hx_C
  -- `‖(x : ℂ)‖ = |x|`.
  have h_eq : ‖(x : ℂ)‖ = |x| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  linarith [h_eq ▸ h_norm]

/-! ### Hermitian case: `H * H ≤ ‖H‖² • 1` -/

set_option maxHeartbeats 400000 in
/-- **Norm-to-Loewner bridge for Hermitian matrices.**

For a Hermitian matrix `H : Matrix n n ℂ`, the square `H * H` is bounded
above by `‖H‖^2 • 1` in the Loewner order on `Matrix n n ℂ`:

  `H * H ≤ (‖H‖^2 : ℝ) • (1 : Matrix n n ℂ)`.

The proof applies `cfc_mono` (monotonicity of the continuous functional
calculus on the Loewner order) to the scalar inequality
`x^2 ≤ ‖H‖^2` on `spectrum ℝ H ⊆ [-‖H‖, ‖H‖]`.
-/
theorem IsHermitian.sq_le_norm_sq_smul_one
    {H : Matrix n n ℂ} (hH : H.IsHermitian) :
    H * H ≤ (‖H‖ ^ 2 : ℝ) • (1 : Matrix n n ℂ) := by
  -- `H` is self-adjoint as a C⋆-algebra element.
  have hH_sa : IsSelfAdjoint H := hH.isSelfAdjoint
  -- The two functions for `cfc_mono`.
  let f : ℝ → ℝ := fun x => x ^ 2
  let g : ℝ → ℝ := fun _ => ‖H‖ ^ 2
  -- Continuity.
  have hf_cont : Continuous f := by fun_prop
  have hg_cont : Continuous g := by fun_prop
  -- Pointwise inequality on the spectrum: `x^2 ≤ ‖H‖^2`.
  have h_point : ∀ x ∈ spectrum ℝ H, f x ≤ g x := by
    intro x hx
    have habs := abs_le_norm_of_mem_spectrum_real_of_hermitian hH hx
    show x ^ 2 ≤ ‖H‖ ^ 2
    have h1 : |x| ^ 2 ≤ ‖H‖ ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg x) habs 2
    have h2 : |x| ^ 2 = x ^ 2 := by rw [sq_abs]
    linarith
  -- Apply `cfc_mono`: `cfc f H ≤ cfc g H`.
  have h_cfc_mono : cfc f H ≤ cfc g H :=
    cfc_mono (a := H) (f := f) (g := g) h_point
      hf_cont.continuousOn hg_cont.continuousOn
  -- Identify LHS: `cfc (·^2) H = H * H`.
  have h_LHS : cfc f H = H * H := by
    show cfc (fun x : ℝ => x ^ 2) H = H * H
    have hstep : cfc (fun x : ℝ => x ^ 2) H = H ^ 2 :=
      cfc_pow_id (R := ℝ) (A := Matrix n n ℂ) (p := IsSelfAdjoint)
        (a := H) (n := 2) hH_sa
    rw [hstep, sq]
  -- Identify RHS: `cfc (fun _ => ‖H‖^2) H = ‖H‖^2 • 1`.
  have h_RHS : cfc g H = (‖H‖ ^ 2 : ℝ) • (1 : Matrix n n ℂ) := by
    show cfc (fun _ : ℝ => ‖H‖ ^ 2) H = (‖H‖ ^ 2 : ℝ) • (1 : Matrix n n ℂ)
    rw [cfc_const (R := ℝ) (A := Matrix n n ℂ) (p := IsSelfAdjoint)
        (r := ‖H‖ ^ 2) (a := H) hH_sa]
    rw [Algebra.algebraMap_eq_smul_one]
  -- Combine.
  calc H * H
      = cfc f H := h_LHS.symm
    _ ≤ cfc g H := h_cfc_mono
    _ = (‖H‖ ^ 2 : ℝ) • (1 : Matrix n n ℂ) := h_RHS

/-! ### PosSemidef case: `M ≤ ‖M‖ • 1` -/

set_option maxHeartbeats 400000 in
/-- **Norm-to-Loewner bridge for positive-semidefinite matrices.**

For a positive-semidefinite matrix `M : Matrix n n ℂ`, we have

  `M ≤ (‖M‖ : ℝ) • (1 : Matrix n n ℂ)`

in the Loewner order on `Matrix n n ℂ`.

The proof applies `cfc_mono` (monotonicity of the continuous functional
calculus on the Loewner order) to the scalar inequality `x ≤ ‖M‖` on
`spectrum ℝ M ⊆ [0, ‖M‖]` (the spectrum of a PSD matrix is contained
in `[0, ‖M‖]` because every spectrum element is nonnegative and bounded
in absolute value by the operator norm).
-/
theorem PosSemidef.le_norm_smul_one_of_isHermitian
    {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    M ≤ (‖M‖ : ℝ) • (1 : Matrix n n ℂ) := by
  -- `M` is self-adjoint as a C⋆-algebra element.
  have hM_sa : IsSelfAdjoint M := hM.isHermitian.isSelfAdjoint
  -- The two functions for `cfc_mono`.
  let f : ℝ → ℝ := fun x => x
  let g : ℝ → ℝ := fun _ => ‖M‖
  -- Continuity.
  have hf_cont : Continuous f := by fun_prop
  have hg_cont : Continuous g := by fun_prop
  -- Pointwise inequality on the spectrum: `x ≤ ‖M‖` for `x ∈ spectrum ℝ M`.
  have h_point : ∀ x ∈ spectrum ℝ M, f x ≤ g x := by
    intro x hx
    -- `|x| ≤ ‖M‖` by the spectrum norm bound for the Hermitian `M`.
    have habs := abs_le_norm_of_mem_spectrum_real_of_hermitian
      hM.isHermitian hx
    -- `x ≤ |x|`.
    have hx_le_abs : x ≤ |x| := le_abs_self x
    show x ≤ ‖M‖
    linarith
  -- Apply `cfc_mono`: `cfc f M ≤ cfc g M`.
  have h_cfc_mono : cfc f M ≤ cfc g M :=
    cfc_mono (a := M) (f := f) (g := g) h_point
      hf_cont.continuousOn hg_cont.continuousOn
  -- Identify LHS: `cfc id M = M`.
  have h_LHS : cfc f M = M := by
    show cfc (fun x : ℝ => x) M = M
    exact cfc_id' ℝ M hM_sa
  -- Identify RHS: `cfc (fun _ => ‖M‖) M = ‖M‖ • 1`.
  have h_RHS : cfc g M = (‖M‖ : ℝ) • (1 : Matrix n n ℂ) := by
    show cfc (fun _ : ℝ => ‖M‖) M = (‖M‖ : ℝ) • (1 : Matrix n n ℂ)
    rw [cfc_const (R := ℝ) (A := Matrix n n ℂ) (p := IsSelfAdjoint)
        (r := ‖M‖) (a := M) hM_sa]
    rw [Algebra.algebraMap_eq_smul_one]
  -- Combine.
  calc M
      = cfc f M := h_LHS.symm
    _ ≤ cfc g M := h_cfc_mono
    _ = (‖M‖ : ℝ) • (1 : Matrix n n ℂ) := h_RHS

end Matrix
