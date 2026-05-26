/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.MatrixAnalysis.HermitianSqLeNormSqOne
import LTFP.MathlibExt.MatrixAnalysis.PosSemidefClosed
import LTFP.MathlibExt.MatrixAnalysis.LiebTraceComplementary
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Loewner coercivity transfer under operator-norm perturbation

This module proves the standard perturbation transfer lemma in the
Loewner order on `Matrix n n ℂ`:

> If `A` is Hermitian, `B` is Hermitian, `A ≽ ρ • 1` in the Loewner
> order, and `‖A - B‖ ≤ ε`, then `B ≽ (ρ - ε) • 1`.

This is the bridge that converts a coercivity bound on one matrix
(e.g. the population NTK at initialization) into a coercivity bound
on a nearby matrix (e.g. the empirical NTK after a small training
step), via an operator-norm perturbation control on their difference.

It is used in the NTK bootstrap (`E3e_full`) chain to transfer the
spectral floor from the population NTK to the empirical NTK
(via the matrix-Bernstein concentration of `E2`) and from the
initialization NTK to the time-`T` NTK (via the gradient-flow drift
bound of `E3e_simple`).

## Auxiliary lemmas

* `Matrix.IsHermitian.le_norm_smul_one` — for Hermitian
  `M : Matrix n n ℂ`, the **upper-side** Loewner bound
  `M ≤ ‖M‖ • 1`. Strictly more general than the existing
  `PosSemidef.le_norm_smul_one_of_isHermitian`: the same CFC proof
  works without assuming `M.PosSemidef`.

* `Matrix.IsHermitian.neg_norm_smul_one_le` — for Hermitian
  `M : Matrix n n ℂ`, the **lower-side** Loewner bound
  `-‖M‖ • 1 ≤ M`. Derived from the upper-side bound applied to
  `-M`, using `‖-M‖ = ‖M‖`.

* `Matrix.IsHermitian.le_smul_one_of_norm_le` — packaged
  ε-form `M ≤ ε • 1` when `‖M‖ ≤ ε`.

* `Matrix.IsHermitian.neg_smul_one_le_of_norm_le` — packaged
  ε-form `-ε • 1 ≤ M` when `‖M‖ ≤ ε`.

## Main result

* `Matrix.PosSemidef.le_smul_one_perturb` — Loewner coercivity
  transfer:

  `(hA : A.IsHermitian) (hB : B.IsHermitian)`
  `(hAρ : ρ • 1 ≤ A) (hAB : ‖A - B‖ ≤ ε) ⊢ (ρ - ε) • 1 ≤ B`.

## Proof strategy

Algebraic decomposition of the target difference:

  `B - (ρ - ε) • 1 = (B - A) + (A - ρ • 1) + ε • 1`.

Each summand is Loewner-nonnegative:

* `(A - ρ • 1) ≥ 0` is `hAρ` rewritten via `sub_nonneg`.
* `(B - A) + ε • 1 ≥ 0` ⟺ `-ε • 1 ≤ B - A`, which is the
  Hermitian lower-side ε-bound applied to `B - A` (Hermitian, with
  `‖B - A‖ = ‖A - B‖ ≤ ε`).

Adding the two nonnegative terms (under `IsOrderedAddMonoid` on
`Matrix n n ℂ` in the `MatrixOrder` scope) gives
`B - (ρ - ε) • 1 ≥ 0`, hence `(ρ - ε) • 1 ≤ B`.

## References

* `LTFP.MathlibExt.MatrixAnalysis.HermitianSqLeNormSqOne` — the
  template CFC proof we mirror (`PosSemidef.le_norm_smul_one_of_isHermitian`).
* `Mathlib.Analysis.Matrix.Order` — Loewner order on `Matrix n n ℂ`,
  scoped to `MatrixOrder`.
* `Mathlib.Analysis.CStarAlgebra.Matrix` — `CStarAlgebra` instance on
  `Matrix n n ℂ` under the L2 operator norm, scoped to
  `Matrix.Norms.L2Operator`.
-/

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-! ### Spectrum-vs-norm bound for Hermitian matrices (local helper)

The private helper `abs_le_norm_of_mem_spectrum_real_of_hermitian` in
`HermitianSqLeNormSqOne.lean` is not visible from this module. We
restate the same content locally for use in the upper-side bound below.
-/

private lemma abs_le_norm_of_mem_spectrum_real_of_hermitian'
    {H : Matrix n n ℂ} (_hH : H.IsHermitian)
    {x : ℝ} (hx : x ∈ spectrum ℝ H) :
    |x| ≤ ‖H‖ := by
  have hx_C : (x : ℂ) ∈ spectrum ℂ H := by
    have := (spectrum.algebraMap_mem_iff ℂ (R := ℝ) (A := Matrix n n ℂ)
      (a := H) (r := x)).mpr hx
    simpa using this
  have h_norm : ‖(x : ℂ)‖ ≤ ‖H‖ := spectrum.norm_le_norm_of_mem hx_C
  have h_eq : ‖(x : ℂ)‖ = |x| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  linarith [h_eq ▸ h_norm]

/-! ### Hermitian upper-side bound: `M ≤ ‖M‖ • 1` -/

set_option maxHeartbeats 400000 in
/-- **Hermitian upper-side norm-to-Loewner bridge.**

For any Hermitian matrix `M : Matrix n n ℂ`, we have

  `M ≤ (‖M‖ : ℝ) • (1 : Matrix n n ℂ)`

in the Loewner order on `Matrix n n ℂ`.

This generalises `PosSemidef.le_norm_smul_one_of_isHermitian` (which
required `M.PosSemidef` for cosmetic reasons; the same CFC proof works
under the weaker `IsHermitian` hypothesis).
-/
theorem IsHermitian.le_norm_smul_one
    {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    M ≤ (‖M‖ : ℝ) • (1 : Matrix n n ℂ) := by
  -- `M` is self-adjoint as a C⋆-algebra element.
  have hM_sa : IsSelfAdjoint M := hM.isSelfAdjoint
  -- The two functions for `cfc_mono`.
  let f : ℝ → ℝ := fun x => x
  let g : ℝ → ℝ := fun _ => ‖M‖
  -- Continuity.
  have hf_cont : Continuous f := by fun_prop
  have hg_cont : Continuous g := by fun_prop
  -- Pointwise inequality on the spectrum: `x ≤ ‖M‖` for `x ∈ spectrum ℝ M`.
  have h_point : ∀ x ∈ spectrum ℝ M, f x ≤ g x := by
    intro x hx
    have habs := abs_le_norm_of_mem_spectrum_real_of_hermitian' hM hx
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

/-! ### Hermitian lower-side bound: `-‖M‖ • 1 ≤ M` -/

/-- **Hermitian lower-side norm-to-Loewner bridge.**

For any Hermitian matrix `M : Matrix n n ℂ`, we have

  `-(‖M‖ : ℝ) • (1 : Matrix n n ℂ) ≤ M`

in the Loewner order on `Matrix n n ℂ`.

Derived from `IsHermitian.le_norm_smul_one` applied to `-M`, using
`‖-M‖ = ‖M‖`.
-/
theorem IsHermitian.neg_norm_smul_one_le
    {M : Matrix n n ℂ} (hM : M.IsHermitian) :
    -((‖M‖ : ℝ) • (1 : Matrix n n ℂ)) ≤ M := by
  -- Apply the upper-side bound to `-M`.
  have hM_neg : (-M).IsHermitian := hM.neg
  have h_norm_neg : ‖-M‖ = ‖M‖ := norm_neg M
  have h_upper : -M ≤ (‖-M‖ : ℝ) • (1 : Matrix n n ℂ) :=
    hM_neg.le_norm_smul_one
  -- Rewrite `‖-M‖ = ‖M‖`.
  rw [h_norm_neg] at h_upper
  -- `-M ≤ ‖M‖ • 1` ⟺ `-(‖M‖ • 1) ≤ -(-M) = M` by `neg_le_neg`.
  have h_neg : -((‖M‖ : ℝ) • (1 : Matrix n n ℂ)) ≤ -(-M) :=
    neg_le_neg h_upper
  rwa [neg_neg] at h_neg

/-! ### Packaged ε-form bounds for Hermitian matrices -/

/-- Packaged upper-side ε-form: if `‖M‖ ≤ ε` and `M` is Hermitian,
then `M ≤ ε • 1` in the Loewner order. -/
theorem IsHermitian.le_smul_one_of_norm_le
    {M : Matrix n n ℂ} (hM : M.IsHermitian) {ε : ℝ} (hε : ‖M‖ ≤ ε) :
    M ≤ (ε : ℝ) • (1 : Matrix n n ℂ) := by
  -- `M ≤ ‖M‖ • 1 ≤ ε • 1`.
  have h1 : M ≤ (‖M‖ : ℝ) • (1 : Matrix n n ℂ) := hM.le_norm_smul_one
  have h_one_psd : (0 : Matrix n n ℂ) ≤ (1 : Matrix n n ℂ) :=
    PosSemidef.one.nonneg
  have h2 : (‖M‖ : ℝ) • (1 : Matrix n n ℂ) ≤ (ε : ℝ) • (1 : Matrix n n ℂ) :=
    smul_le_smul_of_nonneg_right hε h_one_psd
  exact h1.trans h2

/-- Packaged lower-side ε-form: if `‖M‖ ≤ ε` and `M` is Hermitian,
then `-ε • 1 ≤ M` in the Loewner order. -/
theorem IsHermitian.neg_smul_one_le_of_norm_le
    {M : Matrix n n ℂ} (hM : M.IsHermitian) {ε : ℝ} (hε : ‖M‖ ≤ ε) :
    -((ε : ℝ) • (1 : Matrix n n ℂ)) ≤ M := by
  -- `-(ε • 1) ≤ -(‖M‖ • 1) ≤ M`.
  have h1 : -((‖M‖ : ℝ) • (1 : Matrix n n ℂ)) ≤ M :=
    hM.neg_norm_smul_one_le
  have h_one_psd : (0 : Matrix n n ℂ) ≤ (1 : Matrix n n ℂ) :=
    PosSemidef.one.nonneg
  have h2 : (‖M‖ : ℝ) • (1 : Matrix n n ℂ) ≤ (ε : ℝ) • (1 : Matrix n n ℂ) :=
    smul_le_smul_of_nonneg_right hε h_one_psd
  have h3 : -((ε : ℝ) • (1 : Matrix n n ℂ)) ≤ -((‖M‖ : ℝ) • (1 : Matrix n n ℂ)) :=
    neg_le_neg h2
  exact h3.trans h1

/-! ### Main theorem: Loewner coercivity transfer -/

set_option maxHeartbeats 400000 in
/-- **Loewner coercivity transfer under operator-norm perturbation.**

If `A` is Hermitian, `B` is Hermitian, `A ≽ ρ • 1` in the Loewner
order on `Matrix n n ℂ`, and `‖A - B‖ ≤ ε`, then `B ≽ (ρ - ε) • 1`.

This is the standard tool for transferring a spectral coercivity floor
from one matrix to a nearby one under operator-norm control of their
difference. In the NTK bootstrap (`E3e_full`) it converts:

* Population NTK coercivity `K_pop ≽ ρ • 1` into empirical NTK
  coercivity `K_emp ≽ (ρ - ε) • 1`, via the operator-norm
  concentration `‖K_pop - K_emp‖ ≤ ε` (matrix Bernstein, `E2`).
* Initialization NTK coercivity `K_init ≽ ρ • 1` into time-`T` NTK
  coercivity `K_T ≽ (ρ - ε) • 1`, via the gradient-flow drift bound
  `‖K_init - K_T‖ ≤ ε` (`E3e_simple`).
-/
theorem PosSemidef.le_smul_one_perturb
    {A B : Matrix n n ℂ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    {ρ ε : ℝ}
    (hAρ : (ρ : ℝ) • (1 : Matrix n n ℂ) ≤ A)
    (hAB : ‖A - B‖ ≤ ε) :
    ((ρ - ε) : ℝ) • (1 : Matrix n n ℂ) ≤ B := by
  -- Step 1: `B - A` is Hermitian, with `‖B - A‖ = ‖A - B‖ ≤ ε`.
  have h_BA_herm : (B - A).IsHermitian := hB.sub hA
  have h_norm_BA : ‖B - A‖ ≤ ε := by
    rw [norm_sub_rev]; exact hAB
  -- Step 2: lower-side ε-bound on `B - A`: `-ε • 1 ≤ B - A`.
  have h_lower : -((ε : ℝ) • (1 : Matrix n n ℂ)) ≤ B - A :=
    h_BA_herm.neg_smul_one_le_of_norm_le h_norm_BA
  -- Step 3: nonnegativity of `(B - A) + ε • 1`.
  have h_term2 :
      (0 : Matrix n n ℂ) ≤ (B - A) + (ε : ℝ) • (1 : Matrix n n ℂ) := by
    have h := sub_nonneg.mpr h_lower
    -- `(B - A) - (-(ε • 1)) = (B - A) + ε • 1`.
    have h_alg :
        (B - A) - (-((ε : ℝ) • (1 : Matrix n n ℂ))) =
          (B - A) + (ε : ℝ) • (1 : Matrix n n ℂ) := by
      rw [sub_neg_eq_add]
    rw [h_alg] at h
    exact h
  -- Step 4: nonnegativity of `A - ρ • 1` from `hAρ`.
  have h_term1 :
      (0 : Matrix n n ℂ) ≤ A - (ρ : ℝ) • (1 : Matrix n n ℂ) :=
    sub_nonneg.mpr hAρ
  -- Step 5: sum the two nonnegative terms.
  have h_sum :
      (0 : Matrix n n ℂ) ≤
        (A - (ρ : ℝ) • (1 : Matrix n n ℂ)) +
          ((B - A) + (ε : ℝ) • (1 : Matrix n n ℂ)) :=
    add_nonneg h_term1 h_term2
  -- Step 6: algebraically rewrite the sum as `B - (ρ - ε) • 1`.
  have h_rewrite :
      (A - (ρ : ℝ) • (1 : Matrix n n ℂ)) +
        ((B - A) + (ε : ℝ) • (1 : Matrix n n ℂ)) =
      B - ((ρ - ε) : ℝ) • (1 : Matrix n n ℂ) := by
    have h_smul : ((ρ - ε) : ℝ) • (1 : Matrix n n ℂ) =
        (ρ : ℝ) • (1 : Matrix n n ℂ) - (ε : ℝ) • (1 : Matrix n n ℂ) := by
      rw [sub_smul]
    rw [h_smul]
    abel
  rw [h_rewrite] at h_sum
  -- Step 7: convert `0 ≤ B - (ρ - ε) • 1` to `(ρ - ε) • 1 ≤ B`.
  exact sub_nonneg.mp h_sum

end Matrix
