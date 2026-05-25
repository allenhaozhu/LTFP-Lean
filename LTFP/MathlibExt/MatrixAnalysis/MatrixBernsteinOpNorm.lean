/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.MatrixAnalysis.MatrixBernsteinFinal
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Operator-norm matrix Bernstein adapter

The carrier `Matrix.bernstein_full` gives upper-tail concentration for the
largest eigenvalue `λ_max(∑ i, X i (ω i))` of a sum of centred Hermitian
random matrices. For NTK applications and many other downstream uses we
need a two-sided bound on the **operator norm** `‖∑ i, X i (ω i)‖`.

For a Hermitian matrix `S`, the L2 operator norm equals the spectral
radius `max_i |λ_i(S)| = max(λ_max(S), λ_max(-S))`. We therefore obtain
the operator-norm bound by applying `Matrix.bernstein_full` to both the
family `X i` and the negated family `-X i`, and combining the resulting
upper-tail events via a union bound. The price is a factor of two in
front of the carrier bound.

## Main result

* `Matrix.bernstein_op_norm_full` — operator-norm matrix Bernstein bound

  `P(‖∑ i, X i (ω i)‖ ≥ t) ≤ 2 · matrix_bernstein_bound (card d) t σ² R`.

## Proof strategy

For Hermitian `S` and `0 < t`,
`‖S‖_op ∈ spectrum ℝ S` or `-‖S‖_op ∈ spectrum ℝ S`
(`CStarAlgebra.norm_or_neg_norm_mem_spectrum`). By
`Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues`, the spectrum is
the range of `S.IsHermitian.eigenvalues`, so in the first case
`‖S‖ ≤ λ_max S` and in the second case `‖S‖ ∈ spectrum ℝ (-S)` (via
`spectrum.neg_eq`), so `‖S‖ ≤ λ_max (-S)`. Hence
`t ≤ ‖S‖ → t ≤ λ_max S ∨ t ≤ λ_max (-S)`. A union bound on the two
events followed by `Matrix.bernstein_full` applied to `X` and to `-X`
yields the operator-norm bound.

## References

* J. A. Tropp, *User-friendly tail bounds for sums of random matrices*,
  Found. Comput. Math. 12 (2012), 389–434, Corollary 6.1.2.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace Matrix

/-! ### Step 1. Hermitian operator-norm event-inclusion helper -/

open Unitary in
/-- Auxiliary: the L2 operator norm of a Hermitian matrix is bounded by the
maximum of the magnitudes of its eigenvalues. The proof uses the spectral
theorem (`Matrix.IsHermitian.spectral_theorem`) to diagonalise `S` and
`Matrix.l2_opNorm_diagonal` to evaluate the norm of the diagonal factor.
Unitary conjugation preserves the L2 operator norm because each factor of
the unitary has norm `1` (via `CStarRing.norm_of_mem_unitary`). -/
private lemma IsHermitian.opNorm_le_sup_abs_eigenvalues
    {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    {S : Matrix d d ℂ} (hS : S.IsHermitian) :
    ‖S‖ ≤ Finset.sup' Finset.univ Finset.univ_nonempty (fun i => |hS.eigenvalues i|) := by
  classical
  haveI : Nontrivial (Matrix d d ℂ) := inferInstance
  set U : Matrix.unitaryGroup d ℂ := hS.eigenvectorUnitary with hU_def
  set D : Matrix d d ℂ := Matrix.diagonal (RCLike.ofReal ∘ hS.eigenvalues) with hD_def
  -- Spectral theorem identity: `S = U * D * star U` (after unfolding `conjStarAlgAut`).
  have hspec : S = (U : Matrix d d ℂ) * D * (star U : Matrix d d ℂ) := by
    rw [hS.spectral_theorem]
    rfl
  -- Norm of `U` (as a matrix) is 1.
  have hU_norm : ‖(U : Matrix d d ℂ)‖ = 1 :=
    CStarRing.norm_of_mem_unitary U.2
  -- Norm of `star U` (as a matrix) is also 1.
  have hstarU_norm : ‖((star U : Matrix.unitaryGroup d ℂ) : Matrix d d ℂ)‖ = 1 :=
    CStarRing.norm_of_mem_unitary (star U).2
  -- Bound `‖S‖ ≤ ‖D‖` via two applications of the submultiplicative norm.
  have hSnorm : ‖S‖ ≤ ‖D‖ := by
    have hSU_star_eq :
        (star U : Matrix d d ℂ) = ((star U : Matrix.unitaryGroup d ℂ) : Matrix d d ℂ) := rfl
    rw [hspec]
    calc ‖(U : Matrix d d ℂ) * D * (star U : Matrix d d ℂ)‖
        ≤ ‖(U : Matrix d d ℂ) * D‖ * ‖(star U : Matrix d d ℂ)‖ := norm_mul_le _ _
      _ ≤ (‖(U : Matrix d d ℂ)‖ * ‖D‖) * ‖(star U : Matrix d d ℂ)‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ = 1 * ‖D‖ * 1 := by rw [hU_norm, hSU_star_eq, hstarU_norm]
      _ = ‖D‖ := by ring
  -- Now `‖D‖ = ‖(RCLike.ofReal ∘ hS.eigenvalues : d → ℂ)‖` (Pi-norm L∞).
  have hD_eq : ‖D‖ = ‖(RCLike.ofReal ∘ hS.eigenvalues : d → ℂ)‖ :=
    Matrix.l2_opNorm_diagonal _
  rw [hD_eq] at hSnorm
  refine hSnorm.trans ?_
  -- Pi-norm `‖v‖ ≤ sup_i ‖v_i‖` for `v : d → ℂ`; here we go directly via
  -- `pi_norm_le_iff_of_nonneg`.
  have hbound_nn : 0 ≤ Finset.sup' Finset.univ Finset.univ_nonempty
      (fun i => |hS.eigenvalues i|) := by
    obtain ⟨i₀⟩ := ‹Nonempty d›
    exact (abs_nonneg _).trans
      (Finset.le_sup' (f := fun j => |hS.eigenvalues j|) (Finset.mem_univ i₀))
  rw [pi_norm_le_iff_of_nonneg hbound_nn]
  intro i
  show ‖(hS.eigenvalues i : ℂ)‖ ≤ _
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact Finset.le_sup' (f := fun j => |hS.eigenvalues j|) (Finset.mem_univ i)

set_option maxHeartbeats 800000 in
/-- **Event inclusion for the Hermitian operator norm.**

For a Hermitian matrix `S : Matrix d d ℂ` over a nonempty fintype index
`d`, and any `t : ℝ`,

  `t ≤ ‖S‖  →  t ≤ λ_max(S) ∨ t ≤ λ_max(-S)`

where `λ_max(S) := Finset.sup' Finset.univ Finset.univ_nonempty
hS.eigenvalues`. This is the deterministic core of the two-sided union
bound used to derive `Matrix.bernstein_op_norm_full`.

The proof uses the spectral theorem
(`Matrix.IsHermitian.spectral_theorem`) to bound `‖S‖` by the maximum
absolute eigenvalue, and then case-splits on the sign of the achieving
eigenvalue. The negative case uses
`Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues` together with
`spectrum.neg_eq` to transfer the eigenvalue from `S` to `-S`. -/
theorem IsHermitian.norm_le_max_lambdaMax_neg
    {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    {S : Matrix d d ℂ} (hS : S.IsHermitian) {t : ℝ} (ht : t ≤ ‖S‖) :
    t ≤ Finset.sup' Finset.univ Finset.univ_nonempty hS.eigenvalues
      ∨ t ≤ Finset.sup' Finset.univ Finset.univ_nonempty hS.neg.eigenvalues := by
  classical
  -- Step 1: `‖S‖ ≤ sup_i |eigenvalues i|` (operator-norm spectral bound).
  have hSnorm := hS.opNorm_le_sup_abs_eigenvalues
  -- Step 2: the sup is attained at some `j`.
  obtain ⟨j, _, hj_eq⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty (f := fun i => |hS.eigenvalues i|)
  -- After step 2: `sup' (|·| ∘ eigenvalues) = |eigenvalues j|`.
  -- Combine with step 1: `‖S‖ ≤ |eigenvalues j|`, so `t ≤ |eigenvalues j|`.
  have ht' : t ≤ |hS.eigenvalues j| := by
    -- `hSnorm : ‖S‖ ≤ sup' (|·| ∘ eigenvalues)` and `hj_eq : sup' = |eigenvalues j|`.
    have := hSnorm.trans_eq hj_eq
    linarith
  -- Step 3: split on the sign of `eigenvalues j`.
  rcases abs_choice (hS.eigenvalues j) with hpos | hneg
  · -- `|eigenvalues j| = eigenvalues j`, so `t ≤ eigenvalues j ≤ sup' eigenvalues`.
    left
    have hsup : hS.eigenvalues j ≤
        Finset.sup' Finset.univ Finset.univ_nonempty hS.eigenvalues :=
      Finset.le_sup' (f := hS.eigenvalues) (Finset.mem_univ j)
    have : t ≤ hS.eigenvalues j := by rw [← hpos]; exact ht'
    linarith
  · -- `|eigenvalues j| = -eigenvalues j`. We need `-eigenvalues j ≤ sup' (-S).eigenvalues`.
    right
    -- Show `-eigenvalues j ∈ spectrum ℝ (-S) = range (-S).eigenvalues`.
    have h2 : (-hS.eigenvalues j) ∈ spectrum ℝ (-S) := by
      rw [← spectrum.neg_eq]
      refine Set.mem_neg.mpr ?_
      rw [hS.spectrum_real_eq_range_eigenvalues]
      exact ⟨j, by simp⟩
    have hmem_neg : -hS.eigenvalues j ∈ Set.range hS.neg.eigenvalues := by
      rwa [← hS.neg.spectrum_real_eq_range_eigenvalues]
    obtain ⟨k, hk⟩ := hmem_neg
    have hsup : hS.neg.eigenvalues k ≤
        Finset.sup' Finset.univ Finset.univ_nonempty hS.neg.eigenvalues :=
      Finset.le_sup' (f := hS.neg.eigenvalues) (Finset.mem_univ k)
    -- Combine: `t ≤ |eigenvalues j| = -eigenvalues j = hS.neg.eigenvalues k ≤ sup'`.
    have h_eig_j_neg : t ≤ -hS.eigenvalues j := by rw [← hneg]; exact ht'
    have h_eig_k : t ≤ hS.neg.eigenvalues k := by linarith [hk]
    linarith

/-! ### Step 2. Operator-norm matrix Bernstein -/

set_option maxHeartbeats 800000 in
/-- **Matrix Bernstein operator-norm bound (two-sided form).**

For an independent family `X i : Ω i → Matrix d d ℂ` of centred Hermitian
random matrices with `‖X i ω‖ ≤ R` and second-moment Loewner bound
`∑ i, ∫ X i · X i ≤ σ² • 1`, the operator-norm tail probability satisfies

  `P(‖∑ i, X i (ω i)‖ ≥ t) ≤ 2 · matrix_bernstein_bound (card d) t σ² R`
  `                        = 4 · (card d) · exp(-t² / 2 / (σ² + R t / 3))`.

The factor of `2` in front is the standard union-bound overhead from
combining the upper-tail bounds on `λ_max(∑ X_i)` and
`λ_max(-∑ X_i) = -λ_min(∑ X_i)` via
`Matrix.IsHermitian.norm_le_max_lambdaMax_neg`. -/
theorem bernstein_op_norm_full
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
    (σ2 : ℝ) (hσ2 : 0 < σ2)
    (hvar : ∑ i, ∫ x, X i x * X i x ∂μ i ≤ σ2 • (1 : Matrix d d ℂ))
    (t : ℝ) (ht : 0 < t)
    (hSum : ∀ ω : ∀ i, Ω i, (∑ i, X i (ω i)).IsHermitian)
    (hLamMeasPos : AEMeasurable
      (fun ω => Finset.sup' Finset.univ Finset.univ_nonempty (hSum ω).eigenvalues)
      (MeasureTheory.Measure.pi μ))
    (hLamMeasNeg : AEMeasurable
      (fun ω => Finset.sup' Finset.univ Finset.univ_nonempty (hSum ω).neg.eigenvalues)
      (MeasureTheory.Measure.pi μ))
    (htrIntPos : MeasureTheory.Integrable
      (fun ω => (Matrix.trace (NormedSpace.exp
        (LTFP.matrix_bernstein_theta t σ2 R • (∑ i, X i (ω i))))).re)
      (MeasureTheory.Measure.pi μ))
    (htrIntNeg : MeasureTheory.Integrable
      (fun ω => (Matrix.trace (NormedSpace.exp
        (LTFP.matrix_bernstein_theta t σ2 R • (∑ i, -(X i (ω i)))))).re)
      (MeasureTheory.Measure.pi μ)) :
    (MeasureTheory.Measure.pi μ).real
      {ω | t ≤ ‖∑ i, X i (ω i)‖}
    ≤ 2 * LTFP.matrix_bernstein_bound (Fintype.card d) t σ2 R := by
  classical
  -- Abbreviate the carrier bound.
  set B : ℝ := LTFP.matrix_bernstein_bound (Fintype.card d) t σ2 R with hB_def
  -- ─── Positive-tail piece: apply `Matrix.bernstein_full` directly. ─────────
  have hPos : (MeasureTheory.Measure.pi μ).real
      {ω | t ≤ Finset.sup' Finset.univ Finset.univ_nonempty (hSum ω).eigenvalues}
      ≤ B :=
    Matrix.bernstein_full μ X hX hmeas R hR hbound hcenter σ2 hσ2 hvar t ht
      hSum hLamMeasPos htrIntPos
  -- ─── Negative-tail piece: apply `Matrix.bernstein_full` to `Y i := -X i`. ─
  let Y : ∀ i, Ω i → Matrix d d ℂ := fun i ω => -(X i ω)
  have hY_herm : ∀ i ω, (Y i ω).IsHermitian := fun i ω => (hX i ω).neg
  have hY_meas : ∀ i, MeasureTheory.AEStronglyMeasurable (Y i) (μ i) := fun i =>
    (hmeas i).neg
  have hY_bound : ∀ i ω, ‖Y i ω‖ ≤ R := fun i ω => by
    show ‖-(X i ω)‖ ≤ R
    rw [norm_neg]; exact hbound i ω
  have hY_center : ∀ i, ∫ x, Y i x ∂μ i = 0 := fun i => by
    show ∫ x, -(X i x) ∂μ i = 0
    rw [MeasureTheory.integral_neg, hcenter i, neg_zero]
  have hY_var : ∑ i, ∫ x, Y i x * Y i x ∂μ i ≤ σ2 • (1 : Matrix d d ℂ) := by
    have heq : ∀ i, ∫ x, Y i x * Y i x ∂μ i = ∫ x, X i x * X i x ∂μ i := by
      intro i
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      show -(X i x) * -(X i x) = X i x * X i x
      rw [neg_mul_neg]
    simp_rw [heq]; exact hvar
  -- Pointwise: `∑ i, Y i (ω i) = - ∑ i, X i (ω i)`.
  have h_sum_neg : ∀ ω : ∀ i, Ω i, ∑ i, Y i (ω i) = -(∑ i, X i (ω i)) := fun ω => by
    show (∑ i, -(X i (ω i))) = -(∑ i, X i (ω i))
    rw [Finset.sum_neg_distrib]
  -- Helper: for two `IsHermitian` proofs of equal matrices, the sup' of
  -- eigenvalues agree.  This is the eigenvalue-of-rewrite congruence lemma.
  have hSup_congr :
      ∀ (A B : Matrix d d ℂ) (hAB : A = B) (hA : A.IsHermitian) (hB : B.IsHermitian),
        Finset.sup' Finset.univ Finset.univ_nonempty hA.eigenvalues
          = Finset.sup' Finset.univ Finset.univ_nonempty hB.eigenvalues := by
    intro A B hAB hA hB
    subst hAB
    -- Now both `hA` and `hB` are proofs of `A.IsHermitian`; proof irrelevance.
    rw [Subsingleton.elim hA hB]
  -- Hermitian sum for the Y family: build via `▸` along `(h_sum_neg ω).symm`.
  have hSumY : ∀ ω : ∀ i, Ω i, (∑ i, Y i (ω i)).IsHermitian := fun ω =>
    (h_sum_neg ω).symm ▸ (hSum ω).neg
  -- `(hSumY ω).eigenvalues` sup equals `(hSum ω).neg.eigenvalues` sup,
  -- via the congruence lemma applied with the matrix equation
  -- `∑ Y i (ω i) = -(∑ X i (ω i))`.
  have h_eig : ∀ ω : ∀ i, Ω i,
      Finset.sup' Finset.univ Finset.univ_nonempty (hSumY ω).eigenvalues
        = Finset.sup' Finset.univ Finset.univ_nonempty (hSum ω).neg.eigenvalues := fun ω =>
    hSup_congr _ _ (h_sum_neg ω) (hSumY ω) (hSum ω).neg
  -- Measurability of the negated-side sup'.
  have hLamMeasY : AEMeasurable
      (fun ω => Finset.sup' Finset.univ Finset.univ_nonempty (hSumY ω).eigenvalues)
      (MeasureTheory.Measure.pi μ) := by
    have hcongr : (fun ω => Finset.sup' Finset.univ Finset.univ_nonempty (hSumY ω).eigenvalues)
        = (fun ω => Finset.sup' Finset.univ Finset.univ_nonempty (hSum ω).neg.eigenvalues) :=
      funext h_eig
    rw [hcongr]; exact hLamMeasNeg
  -- Integrability of the trace exponential for the Y family.
  have htrIntY : MeasureTheory.Integrable
      (fun ω => (Matrix.trace (NormedSpace.exp
        (LTFP.matrix_bernstein_theta t σ2 R • (∑ i, Y i (ω i))))).re)
      (MeasureTheory.Measure.pi μ) := by
    -- The integrand matches `htrIntNeg` definitionally: `Y i ω := -(X i ω)`.
    convert htrIntNeg using 1
  -- Now apply `Matrix.bernstein_full` to the Y family.
  have hNegRaw : (MeasureTheory.Measure.pi μ).real
      {ω | t ≤ Finset.sup' Finset.univ Finset.univ_nonempty (hSumY ω).eigenvalues}
      ≤ B :=
    Matrix.bernstein_full μ Y hY_herm hY_meas R hR hY_bound hY_center σ2 hσ2 hY_var t ht
      hSumY hLamMeasY htrIntY
  -- Rewrite the event using `h_eig` to match the `neg.eigenvalues` form.
  have hNeg : (MeasureTheory.Measure.pi μ).real
      {ω | t ≤ Finset.sup' Finset.univ Finset.univ_nonempty (hSum ω).neg.eigenvalues}
      ≤ B := by
    have hset : {ω | t ≤ Finset.sup' Finset.univ Finset.univ_nonempty (hSumY ω).eigenvalues}
        = {ω | t ≤ Finset.sup' Finset.univ Finset.univ_nonempty (hSum ω).neg.eigenvalues} := by
      ext ω; rw [Set.mem_setOf_eq, Set.mem_setOf_eq, h_eig ω]
    rw [hset] at hNegRaw; exact hNegRaw
  -- ─── Union bound. ─────────────────────────────────────────────────────────
  set Epos : Set (∀ i, Ω i) :=
    {ω | t ≤ Finset.sup' Finset.univ Finset.univ_nonempty (hSum ω).eigenvalues} with hEpos_def
  set Eneg : Set (∀ i, Ω i) :=
    {ω | t ≤ Finset.sup' Finset.univ Finset.univ_nonempty (hSum ω).neg.eigenvalues} with hEneg_def
  -- Event-inclusion: `{t ≤ ‖S‖} ⊆ Epos ∪ Eneg`.
  have hsubset : {ω : ∀ i, Ω i | t ≤ ‖∑ i, X i (ω i)‖} ⊆ Epos ∪ Eneg := by
    intro ω hω
    have ht_norm : t ≤ ‖∑ i, X i (ω i)‖ := hω
    have hor := (hSum ω).norm_le_max_lambdaMax_neg ht_norm
    rcases hor with h1 | h2
    · exact Or.inl h1
    · exact Or.inr h2
  -- Calc combining union bound and the two carrier bounds.
  calc (MeasureTheory.Measure.pi μ).real {ω | t ≤ ‖∑ i, X i (ω i)‖}
      ≤ (MeasureTheory.Measure.pi μ).real (Epos ∪ Eneg) :=
        MeasureTheory.measureReal_mono hsubset (MeasureTheory.measure_ne_top _ _)
    _ ≤ (MeasureTheory.Measure.pi μ).real Epos + (MeasureTheory.Measure.pi μ).real Eneg :=
        MeasureTheory.measureReal_union_le _ _
    _ ≤ B + B := add_le_add hPos hNeg
    _ = 2 * B := by ring

end Matrix
