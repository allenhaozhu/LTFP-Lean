/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Finite-sample matrix Jensen for the Lieb–Tropp trace-exp functional

This module bundles the *finite-distribution* matrix Jensen inequality
for the direct Lieb–Tropp concave functional

  `A ↦ (Matrix.trace (NormedSpace.exp (H + CFC.log A))).re`.

Given a fixed Hermitian `H : Matrix n n ℂ`, a Hermitian family
`X : ι → Matrix n n ℂ` indexed by a nonempty `Fintype`, and a
probability vector `w : ι → ℝ` (`w i ≥ 0`, `∑ w i = 1`), we have

  `∑ i, w i · Re tr exp (H + X i)
      ≤ Re tr exp (H + log (∑ i, w i • exp (X i)))`.

This is the finite-sample version of Tropp 2012 Lemma 3.4 (matrix MGF
subadditivity), specialized to a probability distribution supported on
a finite index set.  The measure-theoretic version (general probability
measure) requires Bochner-integration / closed-slice infrastructure and
is deferred.

## Proof strategy

* Substrate: `Matrix.lieb_tropp_concave` provides concavity of
  `f A := Re tr exp (H + log A)` on the convex cone of strictly
  positive matrices `SP := {A | IsStrictlyPositive A}`.
* Apply the finite Jensen inequality `ConcaveOn.le_map_sum` at the
  sample points `A_i := exp (X i) ∈ SP` (each strict-pos since
  `X i` Hermitian, via `Matrix.IsHermitian.isStrictlyPositive_exp`).
* Identify `f (exp (X i)) = Re tr exp (H + X i)` via `CFC.log_exp`
  on the self-adjoint `X i`.
* `w i • r = w i * r` for `r : ℝ` finishes the LHS shape.

## Main result

* `Matrix.lieb_tropp_jensen_finite` — finite-distribution Jensen
  inequality for the direct Lieb–Tropp trace-exp functional.

## Reference

* J. A. Tropp, *User-friendly tail bounds for sums of random matrices*,
  Found. Comput. Math. (2012), Lemma 3.4.  The finite-support case is
  the Jensen step underlying the matrix MGF subadditivity inequality.
-/
import LTFP.MathlibExt.MatrixAnalysis.LiebTraceComplementary
import LTFP.MathlibExt.MatrixAnalysis.LiebTroppConcave
import LTFP.MathlibExt.MatrixAnalysis.MatrixExpPositivity
import Mathlib.Analysis.Convex.Jensen

namespace Matrix

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

/-- **Finite-sample Lieb–Tropp matrix Jensen inequality.**

For a Hermitian matrix `H : Matrix n n ℂ`, a Hermitian family
`X : ι → Matrix n n ℂ` indexed by a nonempty finite type, and a
probability vector `w : ι → ℝ` (`w i ≥ 0`, `∑ i, w i = 1`):

  `∑ i, w i * Re tr exp (H + X i)
      ≤ Re tr exp (H + log (∑ i, w i • exp (X i)))`.

This is the finite version of matrix MGF subadditivity (Tropp 2012,
Lemma 3.4) and the natural first step toward the measure-theoretic
matrix Bernstein inequality.

**Proof.**  Apply the finite Jensen inequality (`ConcaveOn.le_map_sum`)
to the Lieb–Tropp concave functional
`f A := Re tr exp (H + log A)` (concavity from `lieb_tropp_concave`)
sampled at the strict-positive points `A_i := exp (X i)`.  Identifying
`f (exp (X i)) = Re tr exp (H + X i)` via `CFC.log_exp` on the
self-adjoint `X i` closes the LHS. -/
theorem lieb_tropp_jensen_finite
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (X : ι → Matrix n n ℂ) (hX : ∀ i, (X i).IsHermitian)
    (w : ι → ℝ) (hw_nonneg : ∀ i, 0 ≤ w i) (hw_sum : ∑ i, w i = 1) :
    ∑ i, w i * (Matrix.trace (NormedSpace.exp (H + X i) :
        Matrix n n ℂ)).re ≤
      (Matrix.trace
        (NormedSpace.exp
          (H + CFC.log (∑ i, w i • (NormedSpace.exp (X i) :
            Matrix n n ℂ))) : Matrix n n ℂ)).re := by
  classical
  -- Set up the strict-positive cone and the Lieb–Tropp concave functional.
  set SP : Set (Matrix n n ℂ) := {A : Matrix n n ℂ | IsStrictlyPositive A}
    with hSP_def
  set f : Matrix n n ℂ → ℝ := fun A =>
    (Matrix.trace (NormedSpace.exp (H + CFC.log A) :
      Matrix n n ℂ)).re with hf_def
  -- Step 1.  Concavity of `f` on `SP` (Part 7 / `lieb_tropp_concave`).
  have hf_concave : ConcaveOn ℝ SP f :=
    Matrix.lieb_tropp_concave H hH
  -- Step 2.  Each sample point `exp (X i)` lies in `SP`.
  have h_sample_mem : ∀ i ∈ (Finset.univ : Finset ι),
      (NormedSpace.exp (X i) : Matrix n n ℂ) ∈ SP := by
    intro i _
    -- `X i` Hermitian → `exp (X i)` strict-positive.
    exact Matrix.IsHermitian.isStrictlyPositive_exp (hX i)
  -- Step 3.  Apply the finite concave Jensen inequality on `Finset.univ`.
  have hJensen :
      (∑ i, w i • f (NormedSpace.exp (X i) : Matrix n n ℂ)) ≤
        f (∑ i, w i • (NormedSpace.exp (X i) : Matrix n n ℂ)) := by
    have :=
      hf_concave.le_map_sum
        (t := (Finset.univ : Finset ι)) (w := w)
        (p := fun i => (NormedSpace.exp (X i) : Matrix n n ℂ))
        (fun i _ => hw_nonneg i) hw_sum h_sample_mem
    simpa using this
  -- Step 4.  Rewrite `f (exp (X i))` using `CFC.log_exp`.
  --
  -- `X i` is self-adjoint (`IsHermitian` is definitionally `IsSelfAdjoint`
  -- for matrices), so `CFC.log (exp (X i)) = X i`, hence
  --   f (exp (X i)) = Re tr exp (H + X i).
  have h_f_at_exp : ∀ i,
      f (NormedSpace.exp (X i) : Matrix n n ℂ) =
        (Matrix.trace (NormedSpace.exp (H + X i) :
          Matrix n n ℂ)).re := by
    intro i
    have hXi_sa : IsSelfAdjoint (X i) := (hX i).isSelfAdjoint
    have hlog_eq : CFC.log (NormedSpace.exp (X i) : Matrix n n ℂ) = X i :=
      CFC.log_exp (X i) hXi_sa
    show (Matrix.trace
        (NormedSpace.exp (H + CFC.log
          (NormedSpace.exp (X i) : Matrix n n ℂ)) :
          Matrix n n ℂ)).re =
      (Matrix.trace
        (NormedSpace.exp (H + X i) : Matrix n n ℂ)).re
    rw [hlog_eq]
  -- Step 5.  Identify `w i • f (exp X i) = w i * f (exp X i)` for `ℝ`-scalars.
  --
  -- Substituting Step 4 also turns the LHS sum into the target form.
  have h_lhs :
      (∑ i, w i • f (NormedSpace.exp (X i) : Matrix n n ℂ)) =
        ∑ i, w i * (Matrix.trace
            (NormedSpace.exp (H + X i) : Matrix n n ℂ)).re := by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [h_f_at_exp i, smul_eq_mul]
  -- Combine.
  rw [h_lhs] at hJensen
  -- The RHS of Jensen is exactly the RHS of the target by `hf_def`.
  exact hJensen

end Matrix
