/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bochner-integration matrix Jensen for the Lieb–Tropp trace-exp functional

This module extends `Matrix.lieb_tropp_jensen_finite` from finite
probability distributions to general probability measures, restricted
to bounded summands. For a fixed Hermitian `H : Matrix n n ℂ` and a
family `X : Ω → Matrix n n ℂ` of Hermitian matrices uniformly bounded
in operator norm by `R ≥ 0`, the inequality

  `∫ Re tr exp (H + X ω) dμ ≤ Re tr exp (H + log ∫ exp (X ω) dμ)`

holds for any probability measure `μ` on `Ω`.

## Proof outline

The argument follows Bochner Jensen on a closed slice:

* Set `r := exp (-R)` and `R' := exp R`. The closed Loewner-spectral box

    `s := {A | A.IsHermitian ∧ r • 1 ≤ A ∧ A ≤ R' • 1}`

  is closed (`Matrix.isClosed_Icc_smul_one`) and convex (intersection of
  three convex sets). Every `A ∈ s` is strictly positive because
  `r > 0` (`IsStrictlyPositive.of_le` from
  `algebraMap ℝ _ r = r • 1 ≤ A`).

* For each `ω`, `exp (X ω) ∈ s`: hermicity of `X ω` together with
  `‖X ω‖ ≤ R` gives spectrum bounds `-R ≤ x ≤ R` for `x ∈ spectrum X ω`,
  which lift to spectrum bounds `r ≤ y ≤ R'` on `spectrum (exp (X ω))`
  via the spectral mapping theorem, hence the Loewner bounds.

* The Lieb–Tropp functional `f A := Re tr exp (H + log A)` is concave
  on the strict-positive cone (`Matrix.lieb_tropp_concave`); since
  `s` ⊆ strict-pos, `f` is concave on `s` (`ConcaveOn.subset`).
  Continuity of `f` on `s` is `Matrix.continuousOn_re_trace_exp_H_plus_log`.
  Boundedness of `f` on `s` (`s` is closed + bounded in finite-dim, so
  compact, and continuous functions are bounded on compact sets) supplies
  integrability of `f ∘ exp ∘ X` under the probability measure `μ`.

* Bochner Jensen (`ConcaveOn.le_map_integral`) then yields

    `∫ f (exp (X ω)) dμ ≤ f (∫ exp (X ω) dμ)`.

* Finally, `f (exp (X ω)) = Re tr exp (H + log (exp (X ω))) =
  Re tr exp (H + X ω)` via `CFC.log_exp` on the Hermitian `X ω`.

## Main result

* `Matrix.lieb_tropp_jensen_bochner_bounded` — Bochner-integration
  matrix Jensen on the bounded Hermitian slice.

## Reference

* J. A. Tropp, *User-friendly tail bounds for sums of random matrices*,
  Found. Comput. Math. (2012), Lemma 3.4. The measure-theoretic version
  of matrix MGF subadditivity is the key technical step for matrix
  Bernstein chains under continuous summand distributions.
-/
import LTFP.MathlibExt.MatrixAnalysis.LiebTroppConcave
import LTFP.MathlibExt.MatrixAnalysis.MatrixCFCContinuity
import LTFP.MathlibExt.MatrixAnalysis.MatrixExpPositivity
import LTFP.MathlibExt.MatrixAnalysis.PosSemidefClosed
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

namespace Matrix

open scoped MatrixOrder Matrix.Norms.L2Operator CFC.Matrix.Norms.L2Operator ComplexOrder

/-! ### Helper: Loewner bounds on `exp X` from `‖X‖ ≤ R` -/

set_option maxHeartbeats 800000 in
/-- For a Hermitian matrix `X : Matrix n n ℂ` with `‖X‖ ≤ R`, the
exponential `exp X` is Hermitian and satisfies the Loewner bounds
`exp (-R) • 1 ≤ exp X ≤ exp R • 1`.

This is the spectral-mapping bound: `spectrum X ⊆ [-‖X‖, ‖X‖] ⊆ [-R, R]`,
so `spectrum (exp X) ⊆ [exp (-R), exp R]`, which is equivalent to the
Loewner bounds via `algebraMap_le_iff_le_spectrum` /
`le_algebraMap_iff_spectrum_le`. -/
theorem exp_isHermitian_and_Icc_smul_one_of_norm_le
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {X : Matrix n n ℂ} (hX : X.IsHermitian)
    {R : ℝ} (hXR : ‖X‖ ≤ R) :
    (NormedSpace.exp X : Matrix n n ℂ).IsHermitian ∧
      (Real.exp (-R) • (1 : Matrix n n ℂ)) ≤ NormedSpace.exp X ∧
      (NormedSpace.exp X : Matrix n n ℂ) ≤ Real.exp R • (1 : Matrix n n ℂ) := by
  classical
  have hX_sa : IsSelfAdjoint X := hX.isSelfAdjoint
  -- Step 1.  Spectrum of `X` is contained in `[-R, R]`.
  have h_spec_X : spectrum ℝ X ⊆ Set.Icc (-R) R := by
    intro x hx
    have h_abs : |x| ≤ ‖X‖ := by
      simpa [Real.norm_eq_abs] using spectrum.norm_le_norm_of_mem (𝕜 := ℝ) hx
    have h_abs_R : |x| ≤ R := h_abs.trans hXR
    exact abs_le.mp h_abs_R
  -- Step 2.  Identify `exp X = cfc Real.exp X` (under `IsSelfAdjoint`).
  have h_exp_eq : (NormedSpace.exp X : Matrix n n ℂ) = cfc Real.exp X :=
    (CFC.real_exp_eq_normedSpace_exp (a := X) hX_sa).symm
  -- Step 3.  Hermicity of `exp X` via cfc.
  have h_exp_sa : IsSelfAdjoint (NormedSpace.exp X : Matrix n n ℂ) := by
    rw [h_exp_eq]; exact cfc_predicate Real.exp X
  -- Step 4.  Spectrum of `exp X = cfc Real.exp X` is `Real.exp '' spectrum X`.
  have h_spec_exp :
      spectrum ℝ (NormedSpace.exp X : Matrix n n ℂ) = Real.exp '' spectrum ℝ X := by
    rw [h_exp_eq]
    exact cfc_map_spectrum Real.exp X
  -- Step 5.  Spectrum bound on `exp X`.
  have h_spec_exp_subset :
      spectrum ℝ (NormedSpace.exp X : Matrix n n ℂ) ⊆
        Set.Icc (Real.exp (-R)) (Real.exp R) := by
    rw [h_spec_exp]
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨Real.exp_le_exp.mpr (h_spec_X hx).1, Real.exp_le_exp.mpr (h_spec_X hx).2⟩
  -- Step 6.  Lift spectrum bounds to Loewner bounds via `algebraMap`.
  have h_upper :
      (NormedSpace.exp X : Matrix n n ℂ) ≤
        algebraMap ℝ (Matrix n n ℂ) (Real.exp R) := by
    rw [le_algebraMap_iff_spectrum_le (a := NormedSpace.exp X) h_exp_sa]
    intro y hy; exact (h_spec_exp_subset hy).2
  have h_lower :
      algebraMap ℝ (Matrix n n ℂ) (Real.exp (-R)) ≤
        (NormedSpace.exp X : Matrix n n ℂ) := by
    rw [algebraMap_le_iff_le_spectrum (a := NormedSpace.exp X) h_exp_sa]
    intro y hy; exact (h_spec_exp_subset hy).1
  refine ⟨h_exp_sa, ?_, ?_⟩
  · rw [← Algebra.algebraMap_eq_smul_one]; exact h_lower
  · rw [← Algebra.algebraMap_eq_smul_one]; exact h_upper

/-! ### Helper: closed Loewner slice is convex -/

/-- The closed Loewner-spectral box
`{A | A.IsHermitian ∧ r • 1 ≤ A ∧ A ≤ R' • 1}` is convex in `Matrix n n ℂ`. -/
theorem convex_Icc_smul_one
    {n : Type*} [Fintype n] [DecidableEq n] (r R' : ℝ) :
    Convex ℝ {A : Matrix n n ℂ |
      A.IsHermitian ∧ r • (1 : Matrix n n ℂ) ≤ A ∧ A ≤ R' • (1 : Matrix n n ℂ)} := by
  -- Convexity of each conjunct separately, then intersection.
  have h_herm : Convex ℝ {A : Matrix n n ℂ | A.IsHermitian} := by
    intro A hA B hB t u ht hu _
    have hA_sa : IsSelfAdjoint A := hA
    have hB_sa : IsSelfAdjoint B := hB
    -- t • A + u • B is self-adjoint since t, u ∈ ℝ (trivial-star).
    have htA : IsSelfAdjoint (t • A) := (IsSelfAdjoint.all t).smul hA_sa
    have huB : IsSelfAdjoint (u • B) := (IsSelfAdjoint.all u).smul hB_sa
    exact (htA.add huB : IsSelfAdjoint (t • A + u • B))
  have h_lower : Convex ℝ {A : Matrix n n ℂ |
      (r • (1 : Matrix n n ℂ)) ≤ A} := by
    intro A hA B hB t u ht hu htu
    simp only [Set.mem_setOf_eq] at hA hB ⊢
    calc r • (1 : Matrix n n ℂ)
        = (t + u) • r • (1 : Matrix n n ℂ) := by rw [htu, one_smul]
      _ = t • (r • (1 : Matrix n n ℂ)) + u • (r • (1 : Matrix n n ℂ)) := add_smul _ _ _
      _ ≤ t • A + u • B := by
          exact add_le_add (smul_le_smul_of_nonneg_left hA ht)
            (smul_le_smul_of_nonneg_left hB hu)
  have h_upper : Convex ℝ {A : Matrix n n ℂ |
      A ≤ R' • (1 : Matrix n n ℂ)} := by
    intro A hA B hB t u ht hu htu
    simp only [Set.mem_setOf_eq] at hA hB ⊢
    calc t • A + u • B
        ≤ t • (R' • (1 : Matrix n n ℂ)) + u • (R' • (1 : Matrix n n ℂ)) := by
          exact add_le_add (smul_le_smul_of_nonneg_left hA ht)
            (smul_le_smul_of_nonneg_left hB hu)
      _ = (t + u) • R' • (1 : Matrix n n ℂ) := (add_smul _ _ _).symm
      _ = R' • (1 : Matrix n n ℂ) := by rw [htu, one_smul]
  have hset_eq :
      ({A : Matrix n n ℂ |
        A.IsHermitian ∧ r • (1 : Matrix n n ℂ) ≤ A ∧ A ≤ R' • (1 : Matrix n n ℂ)})
        = {A : Matrix n n ℂ | A.IsHermitian} ∩
          {A : Matrix n n ℂ | (r • (1 : Matrix n n ℂ)) ≤ A} ∩
          {A : Matrix n n ℂ | A ≤ R' • (1 : Matrix n n ℂ)} := by
    ext A; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]; tauto
  rw [hset_eq]
  exact (h_herm.inter h_lower).inter h_upper

/-! ### Main theorem -/

set_option maxHeartbeats 1600000 in
/-- **Bochner Jensen for the Lieb–Tropp trace-exp functional with
bounded summands.**

For a Hermitian `H : Matrix n n ℂ`, a probability measure `μ` on `Ω`,
and a family `X : Ω → Matrix n n ℂ` of Hermitian matrices uniformly
bounded in operator norm by `R ≥ 0`, with mild measurability hypotheses
on `ω ↦ exp (X ω)` and `ω ↦ Re tr exp (H + X ω)`,

  `∫ Re tr exp (H + X ω) dμ ≤ Re tr exp (H + log (∫ exp (X ω) dμ))`.

This is the measure-theoretic version of matrix MGF subadditivity
(Tropp 2012, Lemma 3.4), which underlies the matrix Bernstein chain
for continuous summand distributions. The proof is Bochner Jensen
applied on the closed convex Loewner slice
`{A | A.IsHermitian ∧ exp (-R) • 1 ≤ A ∧ A ≤ exp R • 1}`. -/
theorem lieb_tropp_jensen_bochner_bounded
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (H : Matrix n n ℂ) (hH : H.IsHermitian)
    (X : Ω → Matrix n n ℂ) (hX : ∀ ω, (X ω).IsHermitian)
    (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ ω, ‖X ω‖ ≤ R)
    (hAEMeas_exp : MeasureTheory.AEStronglyMeasurable
      (fun ω => (NormedSpace.exp (X ω) : Matrix n n ℂ)) μ)
    (hAEMeas_trace : MeasureTheory.AEStronglyMeasurable
      (fun ω => (Matrix.trace (NormedSpace.exp (H + X ω))).re) μ) :
    (∫ ω, (Matrix.trace (NormedSpace.exp (H + X ω))).re ∂μ) ≤
      (Matrix.trace
        (NormedSpace.exp
          (H + CFC.log (∫ ω, NormedSpace.exp (X ω) ∂μ)))).re := by
  classical
  -- ─── Setup: the closed Loewner slice ────────────────────────────────
  set r : ℝ := Real.exp (-R) with hr_def
  set R' : ℝ := Real.exp R with hR'_def
  have hr_pos : 0 < r := Real.exp_pos _
  have hR'_pos : 0 < R' := Real.exp_pos _
  set s : Set (Matrix n n ℂ) := {A : Matrix n n ℂ |
      A.IsHermitian ∧ r • (1 : Matrix n n ℂ) ≤ A ∧ A ≤ R' • (1 : Matrix n n ℂ)}
    with hs_def
  -- ─── Step 1.  s is closed and convex. ───────────────────────────────
  have hs_closed : IsClosed s := Matrix.isClosed_Icc_smul_one r R'
  have hs_conv : Convex ℝ s := Matrix.convex_Icc_smul_one r R'
  -- ─── Step 2.  Every A ∈ s is strictly positive. ──────────────────────
  -- `r • 1 = algebraMap ℝ _ r`, strictly positive for `0 < r`; lift via
  -- `IsStrictlyPositive.of_le`.
  have h_algMap_sp : IsStrictlyPositive (algebraMap ℝ (Matrix n n ℂ) r) :=
    isStrictlyPositive_algebraMap (𝕜 := ℝ) (A := Matrix n n ℂ) hr_pos
  have hs_sub_sp : s ⊆ {A : Matrix n n ℂ | IsStrictlyPositive A} := by
    intro A hA
    obtain ⟨_, hA_low, _⟩ := hA
    have h_algMap_low : algebraMap ℝ (Matrix n n ℂ) r ≤ A := by
      rw [Algebra.algebraMap_eq_smul_one]; exact hA_low
    exact h_algMap_sp.of_le h_algMap_low
  -- ─── Step 3.  For each ω, exp (X ω) ∈ s. ─────────────────────────────
  have h_exp_mem : ∀ ω, (NormedSpace.exp (X ω) : Matrix n n ℂ) ∈ s := by
    intro ω
    obtain ⟨h_herm, h_low, h_up⟩ :=
      exp_isHermitian_and_Icc_smul_one_of_norm_le (hX ω) (hbound ω)
    exact ⟨h_herm, h_low, h_up⟩
  have h_exp_mem_ae :
      ∀ᵐ ω ∂μ, (NormedSpace.exp (X ω) : Matrix n n ℂ) ∈ s :=
    MeasureTheory.ae_of_all μ h_exp_mem
  -- ─── Step 4.  Continuity and concavity of f on s. ───────────────────
  set f : Matrix n n ℂ → ℝ := fun A =>
    (Matrix.trace (NormedSpace.exp (H + CFC.log A))).re with hf_def
  have hf_cont : ContinuousOn f s :=
    Matrix.continuousOn_re_trace_exp_H_plus_log H r R' hr_pos
  have hf_concave_sp :
      ConcaveOn ℝ {A : Matrix n n ℂ | IsStrictlyPositive A} f :=
    Matrix.lieb_tropp_concave H hH
  have hf_concave : ConcaveOn ℝ s f := hf_concave_sp.subset hs_sub_sp hs_conv
  -- ─── Step 5.  Bounded norm on `s`, integrability of ω ↦ exp (X ω). ──
  -- Bound `‖A‖ ≤ R'` for `A ∈ s`: since `s ⊆ {0 ≤ · ≤ R'•1}`, use
  -- `norm_le_iff_le_algebraMap`.
  have h_norm_s : ∀ A ∈ s, ‖A‖ ≤ R' := by
    intro A ⟨h_herm, h_low, h_up⟩
    have h_zero_le_r1 : (0 : Matrix n n ℂ) ≤ r • (1 : Matrix n n ℂ) := by
      rw [← Algebra.algebraMap_eq_smul_one]; exact h_algMap_sp.nonneg
    have h_nn : (0 : Matrix n n ℂ) ≤ A := h_zero_le_r1.trans h_low
    have hR'_nn : (0 : ℝ) ≤ R' := hR'_pos.le
    rw [CStarAlgebra.norm_le_iff_le_algebraMap (a := A) (r := R') hR'_nn h_nn]
    rw [Algebra.algebraMap_eq_smul_one]; exact h_up
  -- For all ω, ‖exp (X ω)‖ ≤ R'.
  have h_exp_norm_bound : ∀ ω,
      ‖(NormedSpace.exp (X ω) : Matrix n n ℂ)‖ ≤ R' :=
    fun ω => h_norm_s _ (h_exp_mem ω)
  -- Bochner integrability of ω ↦ exp (X ω) from the uniform bound.
  have h_int_const : MeasureTheory.Integrable (fun _ : Ω => R') μ :=
    MeasureTheory.integrable_const _
  have h_int_exp : MeasureTheory.Integrable
      (fun ω => (NormedSpace.exp (X ω) : Matrix n n ℂ)) μ := by
    refine h_int_const.mono hAEMeas_exp ?_
    refine MeasureTheory.ae_of_all μ ?_
    intro ω
    have h1 : ‖(NormedSpace.exp (X ω) : Matrix n n ℂ)‖ ≤ R' := h_exp_norm_bound ω
    have h2 : R' ≤ ‖R'‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
    exact h1.trans h2
  -- ─── Step 6.  ∫ exp (X ω) dμ ∈ s. ────────────────────────────────────
  have h_int_in_s : (∫ ω, (NormedSpace.exp (X ω) : Matrix n n ℂ) ∂μ) ∈ s :=
    hs_conv.integral_mem hs_closed h_exp_mem_ae h_int_exp
  -- ─── Step 7.  Identify f (exp (X ω)) = Re tr exp (H + X ω). ──────────
  have h_f_at_exp : ∀ ω,
      f (NormedSpace.exp (X ω) : Matrix n n ℂ) =
        (Matrix.trace (NormedSpace.exp (H + X ω))).re := by
    intro ω
    have hXω_sa : IsSelfAdjoint (X ω) := (hX ω).isSelfAdjoint
    have hlog_eq : CFC.log (NormedSpace.exp (X ω) : Matrix n n ℂ) = X ω :=
      CFC.log_exp (X ω) hXω_sa
    show (Matrix.trace (NormedSpace.exp
              (H + CFC.log (NormedSpace.exp (X ω) : Matrix n n ℂ)))).re =
        (Matrix.trace (NormedSpace.exp (H + X ω))).re
    rw [hlog_eq]
  -- ─── Step 8.  Integrability of ω ↦ Re tr exp (H + X ω). ──────────────
  -- Use that `s` is compact (closed + bounded in finite-dim) and `f` is
  -- continuous on `s`, so `f` is bounded on `s`. Then `f ∘ exp ∘ X` is
  -- bounded, hence integrable under the probability measure `μ`.
  have h_s_bounded : Bornology.IsBounded s := by
    refine (Metric.isBounded_iff_subset_closedBall (0 : Matrix n n ℂ)).mpr ?_
    refine ⟨R', ?_⟩
    intro A hA
    rw [Metric.mem_closedBall, dist_zero_right]
    exact h_norm_s A hA
  have h_s_compact : IsCompact s := by
    have : ProperSpace (Matrix n n ℂ) := FiniteDimensional.proper_real (Matrix n n ℂ)
    exact Metric.isCompact_of_isClosed_isBounded hs_closed h_s_bounded
  obtain ⟨C, hC⟩ : ∃ C, ∀ A ∈ s, ‖f A‖ ≤ C :=
    h_s_compact.exists_bound_of_continuousOn hf_cont
  -- Bound on the integrand: for each ω, `|f (exp (X ω))| ≤ C`.
  have h_integrand_bound : ∀ ω,
      ‖(Matrix.trace (NormedSpace.exp (H + X ω) : Matrix n n ℂ)).re‖ ≤ C := by
    intro ω
    rw [← h_f_at_exp ω]
    exact hC _ (h_exp_mem ω)
  have h_int_const_C : MeasureTheory.Integrable (fun _ : Ω => C) μ :=
    MeasureTheory.integrable_const _
  have h_int_integrand : MeasureTheory.Integrable
      (fun ω => (Matrix.trace (NormedSpace.exp (H + X ω) : Matrix n n ℂ)).re) μ := by
    refine h_int_const_C.mono hAEMeas_trace ?_
    refine MeasureTheory.ae_of_all μ ?_
    intro ω
    have h1 := h_integrand_bound ω
    have h2 : C ≤ ‖C‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
    exact h1.trans h2
  -- Integrability of `f ∘ exp ∘ X` (= the original integrand, via h_f_at_exp).
  have h_int_fcomp : MeasureTheory.Integrable
      (fun ω => f (NormedSpace.exp (X ω) : Matrix n n ℂ)) μ := by
    have h_eq : (fun ω => f (NormedSpace.exp (X ω) : Matrix n n ℂ)) =
                (fun ω => (Matrix.trace (NormedSpace.exp (H + X ω))).re) := by
      funext ω; exact h_f_at_exp ω
    rw [h_eq]; exact h_int_integrand
  -- ─── Step 9.  Apply Bochner Jensen on the closed slice. ─────────────
  have h_jensen :
      (∫ ω, f (NormedSpace.exp (X ω) : Matrix n n ℂ) ∂μ) ≤
        f (∫ ω, (NormedSpace.exp (X ω) : Matrix n n ℂ) ∂μ) :=
    hf_concave.le_map_integral hf_cont hs_closed h_exp_mem_ae h_int_exp h_int_fcomp
  -- ─── Step 10.  Rewrite LHS using f(exp X ω) = Re tr exp (H + X ω). ───
  have h_lhs_eq :
      (∫ ω, f (NormedSpace.exp (X ω) : Matrix n n ℂ) ∂μ) =
        ∫ ω, (Matrix.trace (NormedSpace.exp (H + X ω))).re ∂μ := by
    refine MeasureTheory.integral_congr_ae ?_
    refine MeasureTheory.ae_of_all μ ?_
    intro ω; exact h_f_at_exp ω
  rw [h_lhs_eq] at h_jensen
  exact h_jensen

end Matrix
