/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.MatrixAnalysis.MatrixBernsteinFinal
import LTFP.MathlibExt.MatrixAnalysis.HermitianSqLeNormSqOne
import LTFP.MathlibExt.MatrixAnalysis.RowCovarianceLoewner
import LTFP.MathlibExt.Probability.NTKConcentrationMatrixBernstein
import LTFP.Ch01_Preliminaries.Concentration

/-!
# Row-covariance-tightened matrix Bernstein for the NTK

This module composes `Matrix.bernstein_full`
(`MatrixAnalysis/MatrixBernsteinFinal.lean`) with the row-covariance
Loewner tightening `Matrix.row_covariance_loewner_bound`
(`MatrixAnalysis/RowCovarianceLoewner.lean`) to produce a tightened
matrix Bernstein bound in which the variance proxy `σ²` is instantiated
as the **row-covariance operator norm** `‖Σ‖` for
`Σ := ∑ i, ∫ x, X i x * (X i x)ᴴ ∂μ i`, rather than the coarser
scalar proxy `R² · card ι`.

Under a bounded, centered, Hermitian family `X : ι → Ω i → Matrix dn dn ℂ`,
this yields the tightened tail bound

  `P(t ≤ λ_max(∑ i, X i (ω i)))`
    `≤ matrix_bernstein_bound (card dn) t ‖Σ‖ R`

where `‖Σ‖` can be much smaller than `R² · card ι` in problems with
strong correlation structure (Chizat-Bach lazy-training NTK,
Bach 2024 §12).

## Main result

* `ProbabilityTheory.ntk_matrix_bernstein_tightened` — the row-covariance
  tightened matrix Bernstein tail bound, packaged in the form required
  by `Matrix.bernstein_full`, with `σ² := ‖Σ‖`.

## Proof strategy

1. Set `Σ := ∑ i, ∫ x, X i x * (X i x)ᴴ ∂μ i` and `σ² := ‖Σ‖`.
2. Show `0 < σ²` from `Σ ≠ 0` via `norm_pos_iff.mpr hΣ_ne`.
3. Show each summand `X i x * (X i x)ᴴ` is positive semidefinite via
   `Matrix.posSemidef_self_mul_conjTranspose`.
4. Show the integrated summand `∫ x, X i x * (X i x)ᴴ ∂μ i` is
   positive semidefinite via `Matrix.posSemidef_of_integral`
   (LTFP-local, in `Probability/NTKConcentrationMatrixBernstein.lean`).
5. Show `Σ` itself is positive semidefinite by
   `Matrix.posSemidef_sum` over the finite family `ι`.
6. Apply the norm-to-Loewner bridge
   `Matrix.PosSemidef.le_norm_smul_one_of_isHermitian` to obtain
   `Σ ≤ ‖Σ‖ • 1`.
7. Rewrite `X * Xᴴ` as `X * X` under the pointwise Hermitian hypothesis
   `(hX i x).eq` (for Hermitian `H`, `Hᴴ = H`, so `H * Hᴴ = H * H`).
   Apply `Matrix.bernstein_full` with this reshaped Loewner-form
   variance bound.

## Numerical calibration

The tightening ratio `κ := (R² · card ι) / ‖Σ‖` depends on the input
distribution and activation clipping.  The `#eval` block below reports
`κ ≈ 84.08×` for the instance `(p=32, d=8, m=16)` and `κ ≈ 112.70×` for
`(p=64, d=16, m=32)` under an iid clipped-ReLU NTK model with `M = 1`,
per Bach 2024 §12 / Chizat-Bach 2018.

## References

* J. A. Tropp, *An introduction to matrix concentration inequalities*,
  Foundations and Trends in Machine Learning 8 (2015), §6.1.
* F. Bach, *Learning Theory from First Principles*, MIT Press 2024,
  Chapter 12 (matrix Bernstein for the NTK).
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace ProbabilityTheory

open MeasureTheory BigOperators Matrix

/-! ### Local wrapper: PSD-of-integral for a general `Fintype` index

`Matrix.posSemidef_of_integral` in
`Probability/NTKConcentrationMatrixBernstein.lean` is stated for the
concrete index type `Fin n`.  Here we lift it to any `Fintype dn` index
by transporting along the canonical `Fintype.equivFin` equivalence.

This is a purely structural adapter — the underlying content is
identical to the `Fin n`-specific statement. -/

/-- **PSD-of-integral (general Fintype index).** The Bochner integral of
a pointwise PSD-valued function `f : Ω → Matrix dn dn ℂ` (for any
`Fintype dn`) is positive-semidefinite. -/
lemma _root_.Matrix.posSemidef_of_integral_fintype
    {dn : Type*} [Fintype dn] [DecidableEq dn]
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → Matrix dn dn ℂ)
    (hf_int : Integrable f μ)
    (hf_psd : ∀ ω, (f ω).PosSemidef) :
    (∫ ω, f ω ∂μ).PosSemidef := by
  classical
  -- Transport `f` through the `dn ≃ Fin (card dn)` equivalence into
  -- `Matrix (Fin n) (Fin n) ℂ`, apply the `Fin n`-specific lemma, then
  -- transport back.
  set e : dn ≃ Fin (Fintype.card dn) := Fintype.equivFin dn with he_def
  -- Reindex map (linear, isomorphism).
  set reindex : Matrix dn dn ℂ ≃ₗ[ℂ] Matrix (Fin (Fintype.card dn))
      (Fin (Fintype.card dn)) ℂ := Matrix.reindexLinearEquiv ℂ ℂ e e with hreindex_def
  -- Continuous linear map form of the reindex (finite-dimensional, so
  -- every linear map is continuous).
  set reindexCLM : Matrix dn dn ℂ →L[ℂ] Matrix (Fin (Fintype.card dn))
      (Fin (Fintype.card dn)) ℂ :=
    LinearMap.toContinuousLinearMap reindex.toLinearMap with hreindexCLM_def
  -- `reindex` preserves `PosSemidef` pointwise (via `submatrix` reindexing).
  have h_reindex_psd :
      ∀ ω, (reindex (f ω)).PosSemidef := by
    intro ω
    -- `reindexLinearEquiv e e` acts as `submatrix e.symm e.symm`.
    have h_apply :
        reindex (f ω) = (f ω).submatrix e.symm e.symm := by
      rfl
    rw [h_apply]
    exact (hf_psd ω).submatrix e.symm
  -- Integrate: `∫ (reindex ∘ f) = reindex (∫ f)` since `reindex` is a CLM.
  have h_int_reindex :
      Integrable (fun ω => reindex (f ω)) μ :=
    reindexCLM.integrable_comp hf_int
  have h_int_swap :
      reindex (∫ ω, f ω ∂μ) = ∫ ω, reindex (f ω) ∂μ := by
    have h := ContinuousLinearMap.integral_comp_comm reindexCLM hf_int
    -- `h : ∫ x, reindexCLM (f x) ∂μ = reindexCLM (∫ x, f x ∂μ)`;
    -- `reindexCLM` and `reindex` coincide on values, so we symmetrise.
    exact h.symm
  -- Apply the `Fin n`-specific PSD-of-integral.
  have h_reindex_int_psd :
      (∫ ω, reindex (f ω) ∂μ).PosSemidef :=
    Matrix.posSemidef_of_integral μ _ h_int_reindex h_reindex_psd
  -- Transport back: `∫ f = reindex.symm (reindex (∫ f)) = reindex.symm (∫ reindex ∘ f)`.
  have h_back :
      (∫ ω, f ω ∂μ) = reindex.symm (∫ ω, reindex (f ω) ∂μ) := by
    rw [← h_int_swap, reindex.symm_apply_apply]
  rw [h_back]
  -- `reindex.symm = reindexLinearEquiv ℂ ℂ e.symm e.symm`, so
  -- `reindex.symm A = A.submatrix e e`.
  have h_symm_apply :
      ∀ A : Matrix (Fin (Fintype.card dn)) (Fin (Fintype.card dn)) ℂ,
        reindex.symm A = A.submatrix e e := by
    intro A; rfl
  rw [h_symm_apply]
  exact h_reindex_int_psd.submatrix e

set_option maxHeartbeats 800000 in
/-- **Row-covariance-tightened matrix Bernstein tail bound.**

For a centered Hermitian family `X : ∀ i : m, Ω i → Matrix dn dn ℂ` with
`‖X i ω‖ ≤ R` uniformly, the tail of the maximum eigenvalue of the
sample sum satisfies the tightened matrix Bernstein bound

  `P(t ≤ λ_max(∑ i, X i (ω i)))`
    `≤ matrix_bernstein_bound (card dn) t ‖Σ‖ R`

where `Σ := ∑ i, ∫ x, X i x * (X i x)ᴴ ∂μ i` is the **row covariance**.
The proxy `‖Σ‖` is Loewner-tighter than the standard scalar proxy
`R² · card m` (which the deterministic bridge
`Matrix.row_covariance_loewner_bound` shows sits above `‖Σ‖`).  Under
correlated NTK instances the tightening ratio
`κ := (R² · card m) / ‖Σ‖` can be substantial; see the `#eval` block
below for calibrated values under an iid clipped-ReLU NTK model.

Reference: Tropp 2015 §6.1; Bach 2024 §12. -/
theorem ntk_matrix_bernstein_tightened
    {dn m : Type*} [Fintype dn] [DecidableEq dn] [Nonempty dn]
    [Fintype m] [DecidableEq m]
    {Ω : m → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, MeasureTheory.Measure (Ω i))
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
    (X : ∀ i, Ω i → Matrix dn dn ℂ)
    (hX : ∀ i ω, (X i ω).IsHermitian)
    (hmeas : ∀ i, MeasureTheory.AEStronglyMeasurable (X i) (μ i))
    (hXX_int : ∀ i, MeasureTheory.Integrable
      (fun ω => X i ω * (X i ω)ᴴ) (μ i))
    (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ i ω, ‖X i ω‖ ≤ R)
    (hcenter : ∀ i, ∫ x, X i x ∂μ i = 0)
    (hRowCov_ne :
      (∑ i, ∫ x, X i x * (X i x)ᴴ ∂μ i) ≠
        (0 : Matrix dn dn ℂ))
    (t : ℝ) (ht : 0 < t)
    (hSum : ∀ ω : ∀ i, Ω i, (∑ i, X i (ω i)).IsHermitian)
    (hLamMeas : AEMeasurable
      (fun ω => Finset.sup' Finset.univ Finset.univ_nonempty
        (hSum ω).eigenvalues)
      (MeasureTheory.Measure.pi μ))
    (htrInt : MeasureTheory.Integrable
      (fun ω => (Matrix.trace (NormedSpace.exp
        (LTFP.matrix_bernstein_theta t
            (‖∑ i, ∫ x, X i x * (X i x)ᴴ ∂μ i‖) R •
          (∑ i, X i (ω i))))).re)
      (MeasureTheory.Measure.pi μ)) :
    (MeasureTheory.Measure.pi μ).real
      {ω | t ≤ Finset.sup' Finset.univ Finset.univ_nonempty
                    (hSum ω).eigenvalues}
    ≤ LTFP.matrix_bernstein_bound (Fintype.card dn) t
        (‖∑ i, ∫ x, X i x * (X i x)ᴴ ∂μ i‖) R := by
  classical
  -- Step 1: name the row-covariance `Σ` and the variance proxy `σ² := ‖Σ‖`.
  set RowCov : Matrix dn dn ℂ :=
    ∑ i, ∫ x, X i x * (X i x)ᴴ ∂μ i with hRowCov_def
  set σ2 : ℝ := ‖RowCov‖ with hσ2_def
  -- Step 2: positivity of `σ²` from `Σ ≠ 0`.
  have hσ2_pos : 0 < σ2 := by
    rw [hσ2_def]
    exact norm_pos_iff.mpr hRowCov_ne
  -- Step 3: per-summand `X i x * (X i x)ᴴ` is PSD.
  have h_summand_psd : ∀ i x, (X i x * (X i x)ᴴ).PosSemidef := by
    intro i x
    exact Matrix.posSemidef_self_mul_conjTranspose (X i x)
  -- Step 4: `∫ x, X i x * (X i x)ᴴ ∂μ i` is PSD (Bochner integral of a
  -- pointwise PSD function).
  have h_int_summand_psd :
      ∀ i, (∫ x, X i x * (X i x)ᴴ ∂μ i).PosSemidef := by
    intro i
    refine Matrix.posSemidef_of_integral_fintype (μ i) _ (hXX_int i) ?_
    intro x; exact h_summand_psd i x
  -- Step 5: `RowCov` is PSD by summing PSD summands.
  have hRowCov_psd : RowCov.PosSemidef := by
    rw [hRowCov_def]
    exact Matrix.posSemidef_sum (x := fun i => ∫ x, X i x * (X i x)ᴴ ∂μ i)
      (Finset.univ) (fun i _ => h_int_summand_psd i)
  -- Step 6: Loewner-form variance bound `RowCov ≤ σ² • 1`.
  have hRowCov_le : RowCov ≤ (σ2 : ℝ) • (1 : Matrix dn dn ℂ) := by
    -- `σ² = ‖RowCov‖` and `RowCov.PosSemidef`, so the bridge applies.
    rw [hσ2_def]
    exact hRowCov_psd.le_norm_smul_one_of_isHermitian
  -- Step 7: reshape `∫ X · Xᴴ` as `∫ X · X` using pointwise Hermitianness.
  --
  -- For each `i x`, `(X i x)ᴴ = X i x` (from `(hX i x).eq`), so
  -- `X i x * (X i x)ᴴ = X i x * X i x`.
  have h_XXH_eq_XX :
      ∀ i, (fun x => X i x * (X i x)ᴴ) = fun x => X i x * X i x := by
    intro i
    funext x
    -- `(X i x)ᴴ = X i x` by `IsHermitian.eq`.
    have h_H : (X i x)ᴴ = X i x := (hX i x).eq
    rw [h_H]
  -- Rewrite `RowCov` in the `X · X` form.
  have hRowCov_eq_XX :
      (∑ i, ∫ x, X i x * X i x ∂μ i) = RowCov := by
    rw [hRowCov_def]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    exact congrArg (fun f => ∫ x, f x ∂μ i) (h_XXH_eq_XX i) |>.symm
  -- Assemble the `X · X` form of the variance hypothesis.
  have h_var_XX :
      (∑ i, ∫ x, X i x * X i x ∂μ i) ≤ σ2 • (1 : Matrix dn dn ℂ) := by
    rw [hRowCov_eq_XX]; exact hRowCov_le
  -- Step 8: apply `Matrix.bernstein_full`.
  exact Matrix.bernstein_full μ X hX hmeas R hR hbound hcenter
    σ2 hσ2_pos h_var_XX t ht hSum hLamMeas htrInt

end ProbabilityTheory

/-! ### Numerical calibration of the tightening ratio

The tightening ratio `κ = (R² · card m) / ‖Σ‖` for the standard proxy
vs the row-covariance proxy on iid clipped-ReLU NTK instances.  Sphere
coordinate moments `q_0, q_1, r_1, r_2` are the first-second-order
moments of the sphere-coordinate integrand under the input distribution
`Unif(S^{d-1})` and the weight distribution `w ~ N(0, I_d)` with clipped
ReLU `M = 1` (per Bach 2024 §12 / Chizat-Bach 2018).

The two instances calibrated below:

- `(p=32, d=8, m=16)`  →  `‖Σ‖ = 0.3806`, `V_std = 32`, `κ ≈ 84.08×`
- `(p=64, d=16, m=32)` →  `‖Σ‖ = 0.5679`, `V_std = 64`, `κ ≈ 112.70×`

Row-covariance is Loewner-tighter in general (see
`Matrix.row_covariance_loewner_bound`); the specific ratio here reflects
the strong angular concentration of the NTK gram kernel under sphere
inputs and the additional variance reduction from clipping. -/

/-- Top eigenvalue of `E[A²]` in the sphere-coordinate exchangeability
model.  `A_ab = s(z_a) s(z_b) + ι(z_a) ι(z_b) ⟨x_a, x_b⟩`; by
exchangeability `E[A²] = (δ - o) I + o J` with `δ = q_0 + (m-1) q_1` and
`o = 2 r_1 + (m-2) r_2`.  The largest eigenvalue is `δ + (m-1) o`. -/
def lamEA2 (m q0 q1 r1 r2 : Float) : Float :=
  let δ := q0 + (m - 1.0) * q1
  let o := 2.0 * r1 + (m - 2.0) * r2
  δ + (m - 1.0) * o

/-- Standard-vs-tightened variance ratio: `κ = V_standard / ‖Σ‖`.
Uses `V_standard = 4 m² / p · p = 4 m²` inside `p` scaling; the
denominator `lam` is the row-covariance top eigenvalue scaled by `p`. -/
def kappa (m lam : Float) : Float :=
  4.0 * m * m / lam

-- Instance 1: p=32, d=8, m=16 → expected 84.0843
#eval kappa 16.0 (lamEA2 16.0 0.7548993832278547
  0.08895395440845057 0.1307942084265235 0.02935816751043612)

-- Instance 2: p=64, d=16, m=32 → expected 112.6958
#eval kappa 32.0 (lamEA2 32.0 0.7548993832278547
  0.07703769078003217 0.12582569830865648 0.02731329210258285)
