/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.MatrixAnalysis.MatrixChernoff
import LTFP.MathlibExt.MatrixAnalysis.LiebTroppSumIter
import LTFP.MathlibExt.MatrixAnalysis.BernsteinSummandMGF
import LTFP.MathlibExt.MatrixAnalysis.TraceExpMonotone
import LTFP.MathlibExt.MatrixAnalysis.MatrixExpPositivity

/-!
# Scalar matrix Bernstein one-tail bound

For an independent family `X i : Ω i → Matrix d d ℂ` of centered, Hermitian
random matrices with `‖X i ω‖ ≤ R` and second-moment bound
`∑ i, ∫ X i · X i ≤ σ² • 1` in the Loewner order, the upper-tail probability
of the maximum eigenvalue of the sum satisfies

  `P(λ_max(∑ X_i) ≥ t) ≤ d · exp(-θ t + θ² σ² / (2 (1 - θ R / 3)))`

for any `0 < θ` with `θ R < 3`. This is the sharp `d · exp(...)` form of the
matrix Bernstein upper tail bound, obtained by composing the Laplace transform
(matrix Markov), MGF subadditivity (Tropp 2012 Lemma 3.4 iterated), and the
centered bounded per-summand MGF bound (Tropp 2012 Lemma 6.7).

## Main results

* `Matrix.re_trace_exp_smul_one_eq` — the scalar-on-identity helper
  `Re tr exp (a • 1) = d · exp a`.
* `Matrix.bernstein_scalar_one_tail` — the sharp matrix Bernstein one-tail
  bound in `d · exp(...)` form.

## References

* J. A. Tropp, *User-friendly tail bounds for sums of random matrices*,
  Found. Comput. Math. 12 (2012), 389–434, Theorem 6.1 (matrix Bernstein,
  upper tail).
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace Matrix

/-! ### Scalar-on-identity helper -/

/-- For a scalar `a : ℝ`, the trace of the matrix exponential of `a • 1`
collapses to `(card d) * exp a`:

  `Re tr (exp (a • (1 : Matrix d d ℂ))) = (Fintype.card d) * Real.exp a`.

This identifies the RHS of the matrix Bernstein chain after the variance
bound `c • Σ E[X_i²] ≤ c σ² • 1` has reduced the dominator to a scalar
multiple of the identity. -/
theorem re_trace_exp_smul_one_eq
    {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    (a : ℝ) :
    (Matrix.trace (NormedSpace.exp (a • (1 : Matrix d d ℂ)))).re =
      (Fintype.card d : ℝ) * Real.exp a := by
  classical
  -- Identify `a • 1 = algebraMap ℝ (Matrix d d ℂ) a`.
  have h_alg : (a • (1 : Matrix d d ℂ)) =
      algebraMap ℝ (Matrix d d ℂ) a := by
    rw [Algebra.algebraMap_eq_smul_one]
  -- `exp(algebraMap ℝ a) = algebraMap ℝ (exp a)` by `algebraMap_exp_comm`.
  -- The `exp a` on the RHS is `NormedSpace.exp ℝ a = Real.exp a`.
  have h_comm : NormedSpace.exp (algebraMap ℝ (Matrix d d ℂ) a) =
      algebraMap ℝ (Matrix d d ℂ) (NormedSpace.exp a) :=
    (NormedSpace.algebraMap_exp_comm (𝕂 := ℝ) (𝔸 := Matrix d d ℂ) a).symm
  -- `NormedSpace.exp (a : ℝ) = Real.exp a`.
  have h_real_exp : NormedSpace.exp (a : ℝ) = Real.exp a := by
    rw [Real.exp_eq_exp_ℝ]
  -- Combine: `exp (a • 1) = Real.exp a • 1`.
  have h_exp_smul : NormedSpace.exp (a • (1 : Matrix d d ℂ)) =
      (Real.exp a) • (1 : Matrix d d ℂ) := by
    rw [h_alg, h_comm, h_real_exp, Algebra.algebraMap_eq_smul_one]
  -- Take trace: `tr (Real.exp a • 1) = Real.exp a • tr 1 = Real.exp a * card d`.
  rw [h_exp_smul, Matrix.trace_smul, Matrix.trace_one]
  -- Now goal: `((Real.exp a) • ((Fintype.card d : ℕ) : ℂ)).re
  --   = (Fintype.card d : ℝ) * Real.exp a`.
  rw [show ((Real.exp a) • ((Fintype.card d : ℕ) : ℂ)) =
      ((Real.exp a * Fintype.card d : ℝ) : ℂ) by
    rw [Complex.real_smul]
    push_cast
    ring]
  rw [Complex.ofReal_re]
  ring

/-! ### Main: sharp `d · exp(...)` one-tail bound -/

set_option maxHeartbeats 6400000 in
/-- **Matrix Bernstein upper tail bound (sharp `d · exp(...)` form).**

For an independent family `X i : Ω i → Matrix d d ℂ` of Hermitian random
matrices on probability spaces `(Ω i, μ i)` with `‖X i ω‖ ≤ R`, centering
`∫ X i = 0`, and second-moment Loewner bound
`∑ i, ∫ X i · X i ≤ σ² • 1`, and for any `0 < θ` with `θ R < 3`,

  `P(λ_max(∑ i, X i (ω i)) ≥ t)
    ≤ (card d) · exp(-θ t + θ² σ² / (2 (1 - θ R / 3)))`.

This is the sharp one-tail bound. Composing it with the union bound on the
two tails of the (signed) eigenvalues yields the carrier-facing
`2d · exp(...)` form. -/
theorem bernstein_scalar_one_tail
    {d m : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    [Fintype m] [DecidableEq m]
    {Ω : m → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, MeasureTheory.Measure (Ω i))
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
    (X : ∀ i, Ω i → Matrix d d ℂ)
    (hX : ∀ i ω, (X i ω).IsHermitian)
    (hmeas : ∀ i, MeasureTheory.AEStronglyMeasurable (X i) (μ i))
    (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ i ω, ‖X i ω‖ ≤ R)
    (hcenter : ∀ i, ∫ x, X i x ∂μ i = 0)
    (σ2 : ℝ) (_hσ2 : 0 ≤ σ2)
    (hvar : ∑ i, ∫ x, X i x * X i x ∂μ i ≤ σ2 • (1 : Matrix d d ℂ))
    (t θ : ℝ) (hθ : 0 < θ) (hθR : θ * R < 3)
    (hSum : ∀ ω : ∀ i, Ω i, (∑ i, X i (ω i)).IsHermitian)
    (hLamMeas : AEMeasurable
      (fun ω => Finset.sup' Finset.univ Finset.univ_nonempty
        (hSum ω).eigenvalues) (MeasureTheory.Measure.pi μ))
    (htrInt : MeasureTheory.Integrable
      (fun ω => (Matrix.trace (NormedSpace.exp
        (θ • (∑ i, X i (ω i))))).re) (MeasureTheory.Measure.pi μ)) :
    (MeasureTheory.Measure.pi μ).real
      {ω | t ≤ Finset.sup' Finset.univ Finset.univ_nonempty (hSum ω).eigenvalues}
    ≤ (Fintype.card d : ℝ) * Real.exp
        (-θ * t + θ^2 * σ2 / (2 * (1 - θ * R / 3))) := by
  classical
  -- ─── Notation ────────────────────────────────────────────────────────
  set c : ℝ := θ^2 / (2 * (1 - θ * R / 3)) with hc_def
  have hθ_nn : 0 ≤ θ := hθ.le
  have h_one_sub_pos : 0 < 1 - θ * R / 3 := by linarith
  have hc_nn : 0 ≤ c := by
    have h1 : 0 ≤ θ^2 := sq_nonneg θ
    have h2 : 0 < 2 * (1 - θ * R / 3) := by linarith
    exact div_nonneg h1 h2.le
  -- ─── Step A.  θ-scaled family Y i := θ • X i. ────────────────────────
  let Y : ∀ i, Ω i → Matrix d d ℂ := fun i ω => θ • X i ω
  have hY_herm : ∀ i ω, (Y i ω).IsHermitian := fun i ω => by
    have hi_sa : IsSelfAdjoint (X i ω) := (hX i ω).isSelfAdjoint
    exact ((IsSelfAdjoint.all θ).smul hi_sa : IsSelfAdjoint (Y i ω))
  have hY_bound : ∀ i ω, ‖Y i ω‖ ≤ θ * R := fun i ω => by
    show ‖θ • X i ω‖ ≤ θ * R
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ_nn]
    exact mul_le_mul_of_nonneg_left (hbound i ω) hθ_nn
  have hY_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (Y i) (μ i) := fun i =>
    (hmeas i).const_smul θ
  have hθR_nn : 0 ≤ θ * R := mul_nonneg hθ_nn hR
  -- ─── Step B.  Pointwise sum equality: `Σ Y i ω_i = θ • Σ X i ω_i`. ────
  have h_sum_smul : ∀ ω : ∀ i, Ω i,
      ∑ i, Y i (ω i) = θ • (∑ i, X i (ω i)) := fun ω => by
    show (∑ i, θ • X i (ω i)) = θ • ∑ i, X i (ω i)
    rw [← Finset.smul_sum]
  -- ─── Step 1.  Matrix Markov (Part 2) applied to S ω := Σ_i X i (ω i). ────
  -- Introduce `S` as a named abbreviation so the Π-typeclass synthesis in
  -- Mathlib's matrix Markov lemma does not have to unify against the inline
  -- sum (which causes a `isDefEq` whnf blow-up).
  let S : (∀ i, Ω i) → Matrix d d ℂ := fun ω => ∑ i, X i (ω i)
  have hS_herm : ∀ ω, (S ω).IsHermitian := hSum
  have hLamMeas' : AEMeasurable
      (fun ω => Finset.sup' Finset.univ Finset.univ_nonempty
        (hS_herm ω).eigenvalues) (MeasureTheory.Measure.pi μ) := hLamMeas
  have htrInt' : MeasureTheory.Integrable
      (fun ω => (Matrix.trace (NormedSpace.exp (θ • S ω))).re)
      (MeasureTheory.Measure.pi μ) := htrInt
  have h_markov :
      (MeasureTheory.Measure.pi μ).real
        {ω | t ≤ Finset.sup' Finset.univ Finset.univ_nonempty
          (hS_herm ω).eigenvalues} ≤
      Real.exp (-θ * t) *
        ∫ ω, (Matrix.trace (NormedSpace.exp (θ • S ω))).re
          ∂MeasureTheory.Measure.pi μ :=
    CFC.matrix_markov_lambdaMax_trace_exp S hS_herm t θ hθ hLamMeas' htrInt'
  -- ─── Step 2.  MGF subadditivity (Part 7c) with H = 0, X' := Y. ──────
  -- Rewrite the integrand of the matrix Markov bound to match Part 7c's
  -- shape with H = 0.
  have h_int_eq :
      (∫ ω, (Matrix.trace (NormedSpace.exp
        (θ • (∑ i, X i (ω i))))).re ∂(MeasureTheory.Measure.pi μ)) =
      (∫ ω, (Matrix.trace (NormedSpace.exp
        ((0 : Matrix d d ℂ) + ∑ i, Y i (ω i)))).re
          ∂(MeasureTheory.Measure.pi μ)) := by
    refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ ?_)
    intro ω
    show (Matrix.trace (NormedSpace.exp (θ • (∑ i, X i (ω i))))).re =
      (Matrix.trace (NormedSpace.exp
        ((0 : Matrix d d ℂ) + ∑ i, Y i (ω i)))).re
    rw [← h_sum_smul ω, zero_add]
  -- Apply Part 7c.
  have h0_herm : ((0 : Matrix d d ℂ)).IsHermitian := isHermitian_zero
  have h_part7c :
      (∫ ω, (Matrix.trace (NormedSpace.exp
        ((0 : Matrix d d ℂ) + ∑ i, Y i (ω i)))).re ∂MeasureTheory.Measure.pi μ) ≤
      (Matrix.trace (NormedSpace.exp
        ((0 : Matrix d d ℂ) + ∑ i, CFC.log
          (∫ x, NormedSpace.exp (Y i x) ∂μ i)))).re :=
    Matrix.matrix_mgf_sum_pi_bounded (μ := μ) (H := 0) h0_herm
      Y hY_herm (θ * R) hθR_nn hY_bound hY_meas
  -- Strip the `0 + ` in the bound's RHS.
  have h_zero_add_log :
      ((0 : Matrix d d ℂ) + ∑ i, CFC.log
        (∫ x, NormedSpace.exp (Y i x) ∂μ i)) =
      ∑ i, CFC.log (∫ x, NormedSpace.exp (Y i x) ∂μ i) := zero_add _
  -- ─── Step 3.  Per-summand MGF log bound (Part 8c). ───────────────────
  have h_part8c : ∀ i,
      CFC.log (∫ x, NormedSpace.exp (Y i x) ∂μ i) ≤
        c • (∫ x, (X i x) * (X i x) ∂μ i) := by
    intro i
    have h := Matrix.log_integral_exp_smul_le_of_centered_bounded
      (μ := μ i) (X := X i) (hX i) (hmeas i) R θ hR hθ_nn hθR
      (hbound i) (hcenter i)
    -- `Y i x = θ • X i x` and `c = θ^2 / (2 * (1 - θ * R / 3))`.
    show CFC.log (∫ x, NormedSpace.exp ((θ : ℝ) • X i x) ∂μ i) ≤
        (θ ^ 2 / (2 * (1 - θ * R / 3))) • (∫ x, (X i x) * (X i x) ∂μ i)
    exact h
  -- ─── Step 4.  Aggregate: Σ log E[exp(Y_i)] ≤ c • Σ E[X_i²]. ──────────
  have h_aggregate :
      ∑ i, CFC.log (∫ x, NormedSpace.exp (Y i x) ∂μ i) ≤
      ∑ i, c • (∫ x, (X i x) * (X i x) ∂μ i) :=
    Finset.sum_le_sum (fun i _ => h_part8c i)
  have h_smul_sum_factor :
      ∑ i, c • (∫ x, (X i x) * (X i x) ∂μ i) =
      c • (∑ i, ∫ x, (X i x) * (X i x) ∂μ i) := by
    rw [← Finset.smul_sum]
  -- ─── Step 5.  Variance bound: c • Σ E[X_i²] ≤ c σ² • 1 = (c σ²) • 1. ──
  have h_variance_smul :
      c • (∑ i, ∫ x, (X i x) * (X i x) ∂μ i) ≤
      c • (σ2 • (1 : Matrix d d ℂ)) :=
    smul_le_smul_of_nonneg_left hvar hc_nn
  have h_smul_smul :
      c • (σ2 • (1 : Matrix d d ℂ)) = (c * σ2) • (1 : Matrix d d ℂ) := by
    rw [smul_smul]
  have h_sum_log_le_smul_one :
      ∑ i, CFC.log (∫ x, NormedSpace.exp (Y i x) ∂μ i) ≤
        (c * σ2) • (1 : Matrix d d ℂ) := by
    calc ∑ i, CFC.log (∫ x, NormedSpace.exp (Y i x) ∂μ i)
        ≤ ∑ i, c • (∫ x, (X i x) * (X i x) ∂μ i) := h_aggregate
      _ = c • (∑ i, ∫ x, (X i x) * (X i x) ∂μ i) := h_smul_sum_factor
      _ ≤ c • (σ2 • (1 : Matrix d d ℂ)) := h_variance_smul
      _ = (c * σ2) • (1 : Matrix d d ℂ) := h_smul_smul
  -- ─── Step 6.  Trace-exp monotone (Part 9a). ──────────────────────────
  -- Both sides are Hermitian.
  -- LHS: each `CFC.log (∫ exp Y_i)` is self-adjoint (CFC of real function is SA);
  --      a finite sum of self-adjoint matrices is self-adjoint.
  have h_log_herm : ∀ i,
      (CFC.log (∫ x, NormedSpace.exp (Y i x) ∂μ i) : Matrix d d ℂ).IsHermitian := by
    intro i
    -- `cfc f a` is self-adjoint by `cfc_predicate` (Mathlib).
    have : IsSelfAdjoint
        (CFC.log (∫ x, NormedSpace.exp (Y i x) ∂μ i) : Matrix d d ℂ) := by
      show IsSelfAdjoint (cfc Real.log
        (∫ x, NormedSpace.exp (Y i x) ∂μ i) : Matrix d d ℂ)
      exact cfc_predicate (R := ℝ) _ _
    exact this
  have h_sum_log_herm :
      (∑ i, CFC.log (∫ x, NormedSpace.exp (Y i x) ∂μ i) :
        Matrix d d ℂ).IsHermitian := by
    -- Sum of self-adjoint matrices is self-adjoint.
    have : IsSelfAdjoint
        (∑ i, CFC.log (∫ x, NormedSpace.exp (Y i x) ∂μ i) :
          Matrix d d ℂ) :=
      isSelfAdjoint_sum (R := Matrix d d ℂ) _
        (fun i _ => (h_log_herm i).isSelfAdjoint)
    exact this
  have h_scaled_one_herm :
      ((c * σ2) • (1 : Matrix d d ℂ)).IsHermitian := by
    have h1_sa : IsSelfAdjoint (1 : Matrix d d ℂ) := Matrix.isHermitian_one
    have : IsSelfAdjoint ((c * σ2) • (1 : Matrix d d ℂ)) :=
      (IsSelfAdjoint.all (c * σ2)).smul h1_sa
    exact this
  -- Apply Part 9a.
  have h_trace_exp_mono :
      (Matrix.trace (NormedSpace.exp
        (∑ i, CFC.log (∫ x, NormedSpace.exp (Y i x) ∂μ i)))).re ≤
      (Matrix.trace (NormedSpace.exp ((c * σ2) • (1 : Matrix d d ℂ)))).re :=
    Matrix.re_trace_exp_mono_of_hermitian_le h_sum_log_herm h_scaled_one_herm
      h_sum_log_le_smul_one
  -- ─── Step 7.  Scalar-identity helper. ────────────────────────────────
  have h_scalar_identity :
      (Matrix.trace (NormedSpace.exp ((c * σ2) • (1 : Matrix d d ℂ)))).re =
        (Fintype.card d : ℝ) * Real.exp (c * σ2) :=
    Matrix.re_trace_exp_smul_one_eq (d := d) (c * σ2)
  -- ─── Step 8.  Combine the chain. ─────────────────────────────────────
  -- First chain together the inequalities on the integral side.
  have h_chain_integral :
      (∫ ω, (Matrix.trace (NormedSpace.exp
        (θ • (∑ i, X i (ω i))))).re ∂MeasureTheory.Measure.pi μ) ≤
      (Fintype.card d : ℝ) * Real.exp (c * σ2) := by
    calc (∫ ω, (Matrix.trace (NormedSpace.exp
            (θ • (∑ i, X i (ω i))))).re ∂MeasureTheory.Measure.pi μ)
        = (∫ ω, (Matrix.trace (NormedSpace.exp
              ((0 : Matrix d d ℂ) + ∑ i, Y i (ω i)))).re
              ∂MeasureTheory.Measure.pi μ) := h_int_eq
      _ ≤ (Matrix.trace (NormedSpace.exp
            ((0 : Matrix d d ℂ) + ∑ i, CFC.log
              (∫ x, NormedSpace.exp (Y i x) ∂μ i)))).re := h_part7c
      _ = (Matrix.trace (NormedSpace.exp
            (∑ i, CFC.log
              (∫ x, NormedSpace.exp (Y i x) ∂μ i)))).re := by
            rw [h_zero_add_log]
      _ ≤ (Matrix.trace (NormedSpace.exp
            ((c * σ2) • (1 : Matrix d d ℂ)))).re := h_trace_exp_mono
      _ = (Fintype.card d : ℝ) * Real.exp (c * σ2) := h_scalar_identity
  -- Multiply by `exp(-θ t) ≥ 0` and combine with matrix Markov.
  have h_exp_factor_nn : 0 ≤ Real.exp (-θ * t) := (Real.exp_pos _).le
  have h_mul_chain :
      Real.exp (-θ * t) *
        (∫ ω, (Matrix.trace (NormedSpace.exp
          (θ • (∑ i, X i (ω i))))).re ∂MeasureTheory.Measure.pi μ) ≤
      Real.exp (-θ * t) *
        ((Fintype.card d : ℝ) * Real.exp (c * σ2)) :=
    mul_le_mul_of_nonneg_left h_chain_integral h_exp_factor_nn
  -- Combine the exponents: `exp(-θ t) * (card d * exp(c σ²))
  --                        = card d * exp(-θ t + c σ²)`.
  have h_exp_combine :
      Real.exp (-θ * t) * ((Fintype.card d : ℝ) * Real.exp (c * σ2)) =
        (Fintype.card d : ℝ) * Real.exp (-θ * t + c * σ2) := by
    rw [Real.exp_add]; ring
  -- Final chain.
  calc (MeasureTheory.Measure.pi μ).real
        {ω | t ≤ Finset.sup' Finset.univ Finset.univ_nonempty (hSum ω).eigenvalues}
      ≤ Real.exp (-θ * t) *
          (∫ ω, (Matrix.trace (NormedSpace.exp
            (θ • (∑ i, X i (ω i))))).re ∂MeasureTheory.Measure.pi μ) := h_markov
    _ ≤ Real.exp (-θ * t) *
          ((Fintype.card d : ℝ) * Real.exp (c * σ2)) := h_mul_chain
    _ = (Fintype.card d : ℝ) * Real.exp (-θ * t + c * σ2) := h_exp_combine
    _ = (Fintype.card d : ℝ) * Real.exp
          (-θ * t + θ^2 * σ2 / (2 * (1 - θ * R / 3))) := by
        congr 2
        show -θ * t + c * σ2 =
          -θ * t + θ^2 * σ2 / (2 * (1 - θ * R / 3))
        rw [hc_def]
        ring

/-! ### Carrier-facing `2d · exp(...)` wrapper -/

/-- **Matrix Bernstein upper tail bound (`2d · exp(...)` carrier-facing form).**

A trivial weakening of `Matrix.bernstein_scalar_one_tail` that produces the
`2 · (card d) · exp(...)` shape matching the carrier `matrix_bernstein_via_lieb`
(which uses the `2d` factor by convention for the two-tail union bound).

The factor-of-2 weakening is sound because `(card d) * exp(...) ≥ 0`. -/
theorem bernstein_scalar_one_tail_2d_wrapper
    {d m : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    [Fintype m] [DecidableEq m]
    {Ω : m → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, MeasureTheory.Measure (Ω i))
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
    (X : ∀ i, Ω i → Matrix d d ℂ)
    (hX : ∀ i ω, (X i ω).IsHermitian)
    (hmeas : ∀ i, MeasureTheory.AEStronglyMeasurable (X i) (μ i))
    (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ i ω, ‖X i ω‖ ≤ R)
    (hcenter : ∀ i, ∫ x, X i x ∂μ i = 0)
    (σ2 : ℝ) (hσ2 : 0 ≤ σ2)
    (hvar : ∑ i, ∫ x, X i x * X i x ∂μ i ≤ σ2 • (1 : Matrix d d ℂ))
    (t θ : ℝ) (hθ : 0 < θ) (hθR : θ * R < 3)
    (hSum : ∀ ω : ∀ i, Ω i, (∑ i, X i (ω i)).IsHermitian)
    (hLamMeas : AEMeasurable
      (fun ω => Finset.sup' Finset.univ Finset.univ_nonempty (hSum ω).eigenvalues)
      (MeasureTheory.Measure.pi μ))
    (htrInt : MeasureTheory.Integrable
      (fun ω => (Matrix.trace (NormedSpace.exp (θ • (∑ i, X i (ω i))))).re)
      (MeasureTheory.Measure.pi μ)) :
    (MeasureTheory.Measure.pi μ).real
      {ω | t ≤ Finset.sup' Finset.univ Finset.univ_nonempty (hSum ω).eigenvalues}
    ≤ 2 * (Fintype.card d : ℝ) * Real.exp
        (-θ * t + θ^2 * σ2 / (2 * (1 - θ * R / 3))) := by
  have h1 := Matrix.bernstein_scalar_one_tail μ X hX hmeas R hR hbound hcenter
    σ2 hσ2 hvar t θ hθ hθR hSum hLamMeas htrInt
  have hcard_pos : 0 < (Fintype.card d : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hexp_pos : 0 < Real.exp (-θ * t + θ^2 * σ2 / (2 * (1 - θ * R / 3))) :=
    Real.exp_pos _
  have hpos : 0 ≤ (Fintype.card d : ℝ) *
      Real.exp (-θ * t + θ^2 * σ2 / (2 * (1 - θ * R / 3))) :=
    le_of_lt (mul_pos hcard_pos hexp_pos)
  linarith

end Matrix
