/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Matrix MGF subadditivity for finitely many independent bounded summands

This module extends `Matrix.lieb_tropp_jensen_bochner_bounded` (Part 7b)
from a single bounded Hermitian summand to a finite sum of independent
bounded Hermitian summands by iterating Bochner Jensen over the
product probability measure.

For independent bounded Hermitian random matrices `X i : Ω i → Matrix d d ℂ`
with `‖X i ω‖ ≤ R`,

  `∫ Re tr exp (H + ∑ i, X i (ω i)) dπ μ ≤
    Re tr exp (H + ∑ i, log (∫ exp (X i x) dμ i))`

where `π μ := Measure.pi μ` is the product probability measure on
`Π i, Ω i`.

## Proof outline

Induction on `n : ℕ` over `Fin n`:

* Base case `n = 0`: empty sum, both sides equal `Re tr exp H`.
* Inductive step `n → n + 1`: use `measurePreserving_piFinSuccAbove`
  to identify `Measure.pi μ` with `(μ 0).prod (Measure.pi (μ ∘ Fin.succ))`.
  Then `Fubini` (`integral_prod_symm`) integrates over `Ω 0` first.
  Apply Part 7b on the `Ω 0`-integral with the (deterministic given the
  tail coordinate `ω'`) Hermitian shift `H + ∑ i : Fin n, X i.succ (ω' i)`.
  Then apply the IH to the resulting integrand over `Measure.pi (μ ∘ Fin.succ)`
  with the new Hermitian shift `H + log ∫ exp (X 0)`.

The generic `Fintype m` version follows by transporting via `equivFin`
and `measurePreserving_piCongrLeft`.

## Main result

* `Matrix.matrix_mgf_sum_pi_bounded` — Matrix MGF subadditivity for
  the product probability measure with bounded summands.

## Reference

* J. A. Tropp, *User-friendly tail bounds for sums of random matrices*,
  Found. Comput. Math. (2012), Lemma 3.4.
-/
import LTFP.MathlibExt.MatrixAnalysis.LiebTroppJensenBochner
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

namespace Matrix

open scoped MatrixOrder Matrix.Norms.L2Operator CFC.Matrix.Norms.L2Operator ComplexOrder

/-! ### Helper: AESM of `Re tr exp` -/

/-- Continuity of `A ↦ Re tr exp A` (re-export). -/
theorem continuous_re_trace_exp_aux
    {d : Type*} [Fintype d] [DecidableEq d] :
    Continuous (fun A : Matrix d d ℂ => (Matrix.trace (NormedSpace.exp A)).re) :=
  Matrix.continuous_re_trace_exp

/-! ### Inductive workhorse over `Fin n` -/

set_option maxHeartbeats 4000000 in
/-- **Matrix MGF subadditivity over a product probability measure
indexed by `Fin n`, with bounded Hermitian summands.**

This is the inductive workhorse: the general `Fintype m` case follows
by transferring along `equivFin`. -/
theorem matrix_mgf_sum_pi_fin_bounded :
    ∀ {n : ℕ} {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    {Ω : Fin n → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, MeasureTheory.Measure (Ω i))
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
    (H : Matrix d d ℂ) (_hH : H.IsHermitian)
    (X : ∀ i, Ω i → Matrix d d ℂ)
    (_hX : ∀ i ω, (X i ω).IsHermitian)
    (R : ℝ) (_hR : 0 ≤ R)
    (_hbound : ∀ i ω, ‖X i ω‖ ≤ R)
    (_hmeas : ∀ i, MeasureTheory.AEStronglyMeasurable (X i) (μ i)),
    (∫ ω, (Matrix.trace
      (NormedSpace.exp (H + ∑ i, X i (ω i)))).re ∂MeasureTheory.Measure.pi μ) ≤
      (Matrix.trace (NormedSpace.exp
        (H + ∑ i, CFC.log (∫ x, NormedSpace.exp (X i x) ∂μ i)))).re := by
  intro n
  induction n with
  | zero =>
      intro d _ _ _ Ω _ μ _ H _hH X _hX R _hR _hbound _hmeas
      -- Empty index set: both integrals reduce to `Re tr exp H`.
      simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero]
      rw [MeasureTheory.integral_const]
      have hμtot : (MeasureTheory.Measure.pi μ : MeasureTheory.Measure
          ((i : Fin 0) → Ω i)).real Set.univ = 1 := by
        rw [MeasureTheory.measureReal_def, MeasureTheory.measure_univ]
        simp
      rw [hμtot, one_smul]
  | succ n ih =>
      intro d _inst1 _inst2 _inst3 Ω _instMS μ _instProb H hH X hX R hR hbound hmeas
      classical
      -- ─── Setup: peel coord 0 via piFinSuccAbove ──────────────────────────
      set μ' : ∀ i : Fin n, MeasureTheory.Measure (Ω i.succ) := fun i => μ i.succ
      set X' : ∀ i : Fin n, Ω i.succ → Matrix d d ℂ := fun i => X i.succ
      have hX' : ∀ i ω, (X' i ω).IsHermitian := fun i ω => hX i.succ ω
      have hbound' : ∀ i ω, ‖X' i ω‖ ≤ R := fun i ω => hbound i.succ ω
      have hmeas' : ∀ i, MeasureTheory.AEStronglyMeasurable (X' i) (μ' i) :=
        fun i => hmeas i.succ
      set M₀ : Matrix d d ℂ := ∫ x, NormedSpace.exp (X 0 x) ∂μ 0 with hM₀_def
      -- The new shift `H + CFC.log M₀` is Hermitian.
      have h_logM₀_herm : (CFC.log M₀).IsHermitian := by
        rw [isHermitian_iff_isSelfAdjoint]
        unfold CFC.log
        exact cfc_predicate _ M₀
      have hH'_herm : (H + CFC.log M₀).IsHermitian := hH.add h_logM₀_herm
      -- ─── Apply IH to tail with new H' and tail summands ──────────────────
      have h_ih := ih μ' (H + CFC.log M₀) hH'_herm X' hX' R hR hbound' hmeas'
      -- ─── Norm bounds ────────────────────────────────────────────────────
      have h_norm_Y : ∀ ω' : ∀ i : Fin n, Ω i.succ,
          ‖H + ∑ i : Fin n, X' i (ω' i)‖ ≤ ‖H‖ + n * R := by
        intro ω'
        calc ‖H + ∑ i : Fin n, X' i (ω' i)‖
            ≤ ‖H‖ + ‖∑ i : Fin n, X' i (ω' i)‖ := norm_add_le _ _
          _ ≤ ‖H‖ + ∑ i : Fin n, ‖X' i (ω' i)‖ := by
              gcongr; exact norm_sum_le _ _
          _ ≤ ‖H‖ + ∑ i : Fin n, R := by
              gcongr with i
              exact hbound' i (ω' i)
          _ = ‖H‖ + n * R := by
              simp [mul_comm]
      -- ─── Compact-bound for the integrand ────────────────────────────────
      set Rad : ℝ := ‖H‖ + (n + 1) * R with hRad_def
      have hRad_nn : 0 ≤ Rad := by
        show 0 ≤ ‖H‖ + (n + 1) * R
        have hnorm := norm_nonneg H
        have hn1R : 0 ≤ ((n : ℝ) + 1) * R := by
          apply mul_nonneg _ hR
          have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
          linarith
        linarith
      have hProper : ProperSpace (Matrix d d ℂ) :=
        FiniteDimensional.proper_real (Matrix d d ℂ)
      have h_compact_ball : IsCompact (Metric.closedBall (0 : Matrix d d ℂ) Rad) :=
        isCompact_closedBall _ _
      have h_cont : Continuous (fun A : Matrix d d ℂ =>
          (Matrix.trace (NormedSpace.exp A)).re) := Matrix.continuous_re_trace_exp
      obtain ⟨Cg, hCg⟩ : ∃ C, ∀ A ∈ Metric.closedBall (0 : Matrix d d ℂ) Rad,
          ‖(Matrix.trace (NormedSpace.exp A)).re‖ ≤ C :=
        h_compact_ball.exists_bound_of_continuousOn h_cont.continuousOn
      -- ─── Change of variables: pi μ ↔ (μ 0).prod (pi μ') ─────────────────
      set e : (∀ i : Fin (n + 1), Ω i) ≃ᵐ Ω 0 × (∀ i : Fin n, Ω i.succ) :=
        MeasurableEquiv.piFinSuccAbove Ω 0 with he_def
      have hMP : MeasureTheory.MeasurePreserving e (MeasureTheory.Measure.pi μ)
          ((μ 0).prod (MeasureTheory.Measure.pi μ')) := by
        have hMP0 := MeasureTheory.measurePreserving_piFinSuccAbove μ (0 : Fin (n + 1))
        have hμ_eq : (fun j : Fin n => μ ((0 : Fin (n + 1)).succAbove j)) =
            (fun j : Fin n => μ j.succ) := by
          funext j; simp
        rw [hμ_eq] at hMP0
        exact hMP0
      have he_eval : ∀ ω : ∀ i : Fin (n + 1), Ω i,
          e ω = (ω 0, fun i : Fin n => ω i.succ) := fun _ => rfl
      -- The integrand decomposed in (x, ω') coordinates.
      set g : Ω 0 → (∀ i : Fin n, Ω i.succ) → ℝ := fun x ω' =>
        (Matrix.trace
          (NormedSpace.exp ((H + ∑ i : Fin n, X' i (ω' i)) + X 0 x))).re with hg_def
      -- Sum decomposition.
      have h_sum_decomp : ∀ ω : ∀ i : Fin (n + 1), Ω i,
          (NormedSpace.exp (H + ∑ i, X i (ω i)) : Matrix d d ℂ) =
            NormedSpace.exp ((H + ∑ i : Fin n, X i.succ (ω i.succ)) + X 0 (ω 0)) := by
        intro ω
        congr 1
        rw [Fin.sum_univ_succ]
        abel
      -- LHS rewrite.
      have h_lhs_eq :
          (∫ ω, (Matrix.trace
            (NormedSpace.exp (H + ∑ i, X i (ω i)))).re ∂MeasureTheory.Measure.pi μ) =
          ∫ p : Ω 0 × (∀ i : Fin n, Ω i.succ),
            g p.1 p.2 ∂((μ 0).prod (MeasureTheory.Measure.pi μ')) := by
        rw [← hMP.integral_comp']
        refine MeasureTheory.integral_congr_ae ?_
        refine MeasureTheory.ae_of_all _ ?_
        intro ω
        show (Matrix.trace (NormedSpace.exp (H + ∑ i, X i (ω i)))).re =
            g (e ω).1 (e ω).2
        rw [he_eval, h_sum_decomp]
      rw [h_lhs_eq]
      -- ─── AESM of the integrand ──────────────────────────────────────────
      -- Build AESM(X 0 ∘ fst) and AESM(X' i ∘ (eval i ∘ snd)) on the product.
      have h_aem_X0_fst : MeasureTheory.AEStronglyMeasurable
          (fun p : Ω 0 × (∀ i : Fin n, Ω i.succ) => X 0 p.1)
          ((μ 0).prod (MeasureTheory.Measure.pi μ')) :=
        (hmeas 0).comp_fst
      have h_aem_X'_eval : ∀ i : Fin n, MeasureTheory.AEStronglyMeasurable
          (fun ω' : ∀ j : Fin n, Ω j.succ => X' i (ω' i))
          (MeasureTheory.Measure.pi μ') := by
        intro i
        -- X' i is AESM on μ' i; eval i : pi μ' → μ' i is measure-preserving.
        have hMP_eval : MeasureTheory.MeasurePreserving
            (Function.eval i : (∀ j : Fin n, Ω j.succ) → Ω i.succ)
            (MeasureTheory.Measure.pi μ') (μ' i) :=
          MeasureTheory.measurePreserving_eval _ _
        exact (hmeas' i).comp_quasiMeasurePreserving hMP_eval.quasiMeasurePreserving
      have h_aem_X'_snd : ∀ i : Fin n, MeasureTheory.AEStronglyMeasurable
          (fun p : Ω 0 × (∀ j : Fin n, Ω j.succ) => X' i (p.2 i))
          ((μ 0).prod (MeasureTheory.Measure.pi μ')) :=
        fun i => (h_aem_X'_eval i).comp_snd
      have h_aem_sum : MeasureTheory.AEStronglyMeasurable
          (fun p : Ω 0 × (∀ j : Fin n, Ω j.succ) =>
            ∑ i : Fin n, X' i (p.2 i)) ((μ 0).prod (MeasureTheory.Measure.pi μ')) :=
        Finset.aestronglyMeasurable_fun_sum Finset.univ
          (fun i _ => h_aem_X'_snd i)
      have h_aem_arg : MeasureTheory.AEStronglyMeasurable
          (fun p : Ω 0 × (∀ j : Fin n, Ω j.succ) =>
            (H + ∑ i : Fin n, X' i (p.2 i)) + X 0 p.1)
          ((μ 0).prod (MeasureTheory.Measure.pi μ')) :=
        (h_aem_sum.const_add _).add h_aem_X0_fst
      have h_aem_g : MeasureTheory.AEStronglyMeasurable
          (fun p : Ω 0 × (∀ j : Fin n, Ω j.succ) => g p.1 p.2)
          ((μ 0).prod (MeasureTheory.Measure.pi μ')) :=
        h_cont.comp_aestronglyMeasurable h_aem_arg
      -- ─── Boundedness: |g p.1 p.2| ≤ Cg via compact-bound ────────────────
      have h_norm_arg : ∀ p : Ω 0 × (∀ i : Fin n, Ω i.succ),
          ‖(H + ∑ i : Fin n, X' i (p.2 i)) + X 0 p.1‖ ≤ Rad := by
        intro ⟨x, ω'⟩
        calc ‖(H + ∑ i : Fin n, X' i (ω' i)) + X 0 x‖
            ≤ ‖H + ∑ i : Fin n, X' i (ω' i)‖ + ‖X 0 x‖ := norm_add_le _ _
          _ ≤ (‖H‖ + n * R) + R := by
              gcongr
              · exact h_norm_Y ω'
              · exact hbound 0 x
          _ = Rad := by show _ = ‖H‖ + (n + 1) * R; ring
      have h_pointwise_norm_bound : ∀ p : Ω 0 × (∀ i : Fin n, Ω i.succ),
          ‖g p.1 p.2‖ ≤ Cg := by
        intro p
        have h_mem : (H + ∑ i : Fin n, X' i (p.2 i)) + X 0 p.1 ∈
            Metric.closedBall (0 : Matrix d d ℂ) Rad := by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact h_norm_arg p
        exact hCg _ h_mem
      have h_int_g : MeasureTheory.Integrable
          (fun p : Ω 0 × (∀ i : Fin n, Ω i.succ) => g p.1 p.2)
          ((μ 0).prod (MeasureTheory.Measure.pi μ')) := by
        refine (MeasureTheory.integrable_const Cg).mono h_aem_g ?_
        refine MeasureTheory.ae_of_all _ ?_
        intro p
        have h1 := h_pointwise_norm_bound p
        have h2 : Cg ≤ ‖Cg‖ := by
          rw [Real.norm_eq_abs]; exact le_abs_self _
        exact h1.trans h2
      -- ─── Pointwise Part 7b on the inner integral over Ω 0 ─────────────
      have h_inner_bound : ∀ ω' : ∀ i : Fin n, Ω i.succ,
          (∫ x, g x ω' ∂μ 0) ≤
            (Matrix.trace (NormedSpace.exp
              ((H + ∑ i : Fin n, X' i (ω' i)) + CFC.log M₀))).re := by
        intro ω'
        set Y : Matrix d d ℂ := H + ∑ i : Fin n, X' i (ω' i) with hY_def
        have hY_herm : Y.IsHermitian := by
          refine hH.add ?_
          rw [isHermitian_iff_isSelfAdjoint]
          exact isSelfAdjoint_sum Finset.univ
            (fun i _ => (hX' i (ω' i)).isSelfAdjoint)
        have h_cont_exp : Continuous fun A : Matrix d d ℂ =>
            (NormedSpace.exp A : Matrix d d ℂ) := by
          let +nondep : NormedAlgebra ℚ (Matrix d d ℂ) :=
            NormedAlgebra.restrictScalars ℚ ℂ (Matrix d d ℂ)
          exact NormedSpace.exp_continuous
        have h_aem_exp : MeasureTheory.AEStronglyMeasurable
            (fun x => (NormedSpace.exp (X 0 x) : Matrix d d ℂ)) (μ 0) :=
          h_cont_exp.comp_aestronglyMeasurable (hmeas 0)
        have h_cont_shifted : Continuous fun A : Matrix d d ℂ => Y + A :=
          continuous_const.add continuous_id
        have h_aem_tr : MeasureTheory.AEStronglyMeasurable
            (fun x => (Matrix.trace (NormedSpace.exp (Y + X 0 x))).re) (μ 0) :=
          (h_cont.comp h_cont_shifted).comp_aestronglyMeasurable (hmeas 0)
        have h7b := Matrix.lieb_tropp_jensen_bochner_bounded
          (μ := μ 0) Y hY_herm (X 0) (fun ω => hX 0 ω) R hR
          (fun ω => hbound 0 ω) h_aem_exp h_aem_tr
        show ∫ x, (Matrix.trace
            (NormedSpace.exp (Y + X 0 x))).re ∂μ 0 ≤
          (Matrix.trace (NormedSpace.exp (Y + CFC.log M₀))).re
        exact h7b
      -- ─── Fubini ────────────────────────────────────────────────────────
      have h_fubini : ∫ p : Ω 0 × (∀ i : Fin n, Ω i.succ),
            g p.1 p.2 ∂((μ 0).prod (MeasureTheory.Measure.pi μ')) =
          ∫ ω' : ∀ i : Fin n, Ω i.succ, ∫ x, g x ω' ∂μ 0 ∂MeasureTheory.Measure.pi μ' :=
        MeasureTheory.integral_prod_symm _ h_int_g
      rw [h_fubini]
      -- ─── Inner-integral integrability ──────────────────────────────────
      have h_int_inner : MeasureTheory.Integrable
          (fun ω' : ∀ i : Fin n, Ω i.succ => ∫ x, g x ω' ∂μ 0)
          (MeasureTheory.Measure.pi μ') :=
        h_int_g.integral_prod_right
      -- Bound function b on pi μ'.
      set b : (∀ i : Fin n, Ω i.succ) → ℝ := fun ω' =>
        (Matrix.trace (NormedSpace.exp
          ((H + ∑ i : Fin n, X' i (ω' i)) + CFC.log M₀))).re with hb_def
      -- AESM of b: ω' ↦ b ω' = Re tr exp (Y + log M₀).
      have h_aem_sum_pi : MeasureTheory.AEStronglyMeasurable
          (fun ω' : ∀ j : Fin n, Ω j.succ => ∑ i : Fin n, X' i (ω' i))
          (MeasureTheory.Measure.pi μ') :=
        Finset.aestronglyMeasurable_fun_sum Finset.univ
          (fun i _ => h_aem_X'_eval i)
      have h_aem_b_arg : MeasureTheory.AEStronglyMeasurable
          (fun ω' : ∀ j : Fin n, Ω j.succ =>
            (H + ∑ i : Fin n, X' i (ω' i)) + CFC.log M₀)
          (MeasureTheory.Measure.pi μ') :=
        (h_aem_sum_pi.const_add _).add_const _
      have h_aem_b : MeasureTheory.AEStronglyMeasurable b
          (MeasureTheory.Measure.pi μ') :=
        h_cont.comp_aestronglyMeasurable h_aem_b_arg
      -- Bound on b.
      set RadB : ℝ := ‖H‖ + n * R + ‖CFC.log M₀‖ with hRadB_def
      have h_compact_ballB : IsCompact (Metric.closedBall (0 : Matrix d d ℂ) RadB) :=
        isCompact_closedBall _ _
      obtain ⟨Cb, hCb⟩ : ∃ C, ∀ A ∈ Metric.closedBall (0 : Matrix d d ℂ) RadB,
          ‖(Matrix.trace (NormedSpace.exp A)).re‖ ≤ C :=
        h_compact_ballB.exists_bound_of_continuousOn h_cont.continuousOn
      have h_norm_b_arg_pt : ∀ ω' : ∀ i : Fin n, Ω i.succ,
          ‖(H + ∑ i : Fin n, X' i (ω' i)) + CFC.log M₀‖ ≤ RadB := by
        intro ω'
        calc ‖(H + ∑ i : Fin n, X' i (ω' i)) + CFC.log M₀‖
            ≤ ‖H + ∑ i : Fin n, X' i (ω' i)‖ + ‖CFC.log M₀‖ := norm_add_le _ _
          _ ≤ (‖H‖ + n * R) + ‖CFC.log M₀‖ := by
              gcongr
              exact h_norm_Y ω'
      have h_b_norm_bound : ∀ ω' : ∀ i : Fin n, Ω i.succ, ‖b ω'‖ ≤ Cb := by
        intro ω'
        have h_mem : (H + ∑ i : Fin n, X' i (ω' i)) + CFC.log M₀ ∈
            Metric.closedBall (0 : Matrix d d ℂ) RadB := by
          rw [Metric.mem_closedBall, dist_zero_right]
          exact h_norm_b_arg_pt ω'
        exact hCb _ h_mem
      have h_int_b : MeasureTheory.Integrable b (MeasureTheory.Measure.pi μ') := by
        refine (MeasureTheory.integrable_const Cb).mono h_aem_b ?_
        refine MeasureTheory.ae_of_all _ ?_
        intro ω'
        have h1 := h_b_norm_bound ω'
        have h2 : Cb ≤ ‖Cb‖ := by
          rw [Real.norm_eq_abs]; exact le_abs_self _
        exact h1.trans h2
      -- Monotone integral inequality.
      have h_monotone : ∫ ω', (∫ x, g x ω' ∂μ 0) ∂MeasureTheory.Measure.pi μ' ≤
          ∫ ω', b ω' ∂MeasureTheory.Measure.pi μ' :=
        MeasureTheory.integral_mono_ae h_int_inner h_int_b
          (MeasureTheory.ae_of_all _ h_inner_bound)
      -- IH rewrite.
      have h_b_eq_ih_integrand : ∀ ω' : ∀ i : Fin n, Ω i.succ,
          b ω' = (Matrix.trace (NormedSpace.exp
            ((H + CFC.log M₀) + ∑ i : Fin n, X' i (ω' i)))).re := by
        intro ω'
        show (Matrix.trace (NormedSpace.exp
            ((H + ∑ i : Fin n, X' i (ω' i)) + CFC.log M₀))).re = _
        congr 2; abel
      have h_ih_rw : (∫ ω', b ω' ∂MeasureTheory.Measure.pi μ') =
          ∫ ω', (Matrix.trace (NormedSpace.exp
            ((H + CFC.log M₀) + ∑ i : Fin n, X' i (ω' i)))).re ∂MeasureTheory.Measure.pi μ' :=
        MeasureTheory.integral_congr_ae
          (MeasureTheory.ae_of_all _ h_b_eq_ih_integrand)
      -- Chain everything.
      calc (∫ ω', (∫ x, g x ω' ∂μ 0) ∂MeasureTheory.Measure.pi μ')
          ≤ ∫ ω', b ω' ∂MeasureTheory.Measure.pi μ' := h_monotone
        _ = ∫ ω', (Matrix.trace (NormedSpace.exp
              ((H + CFC.log M₀) + ∑ i : Fin n, X' i (ω' i)))).re
              ∂MeasureTheory.Measure.pi μ' := h_ih_rw
        _ ≤ (Matrix.trace (NormedSpace.exp
              ((H + CFC.log M₀) + ∑ i : Fin n,
                CFC.log (∫ x, NormedSpace.exp (X' i x) ∂μ' i)))).re := h_ih
        _ = (Matrix.trace (NormedSpace.exp
              (H + ∑ i : Fin (n + 1),
                CFC.log (∫ x, NormedSpace.exp (X i x) ∂μ i)))).re := by
            -- Substitute M₀ definition, X' = X ∘ Fin.succ, μ' = μ ∘ Fin.succ.
            -- LHS: (H + log (∫ exp X 0 dμ 0)) + ∑_{Fin n} log (∫ exp X i.succ dμ i.succ)
            -- RHS: H + ∑_{Fin (n+1)} log (∫ exp X i dμ i)
            -- RHS sum decomposes via Fin.sum_univ_succ as:
            --   log (∫ exp X 0 dμ 0) + ∑_{Fin n} log (∫ exp X i.succ dμ i.succ)
            -- Then group: H + (a + ∑) = (H + a) + ∑.
            have hgoal :
                (H + CFC.log M₀) + ∑ i : Fin n, CFC.log
                  (∫ x, NormedSpace.exp (X' i x) ∂μ' i) =
                H + ∑ i : Fin (n + 1), CFC.log
                  (∫ x, NormedSpace.exp (X i x) ∂μ i) := by
              show (H + CFC.log (∫ x, NormedSpace.exp (X 0 x) ∂μ 0)) +
                  ∑ i : Fin n, CFC.log
                    (∫ x, NormedSpace.exp (X i.succ x) ∂μ i.succ) =
                H + ∑ i : Fin (n + 1), CFC.log
                  (∫ x, NormedSpace.exp (X i x) ∂μ i)
              rw [Fin.sum_univ_succ]
              abel
            rw [hgoal]

/-! ### General `Fintype m` version via `equivFin` -/

set_option maxHeartbeats 800000 in
/-- **Matrix MGF subadditivity for independent bounded Hermitian
summands indexed by a finite type `m`.**

For a Hermitian `H`, independent random Hermitian matrices `X i` on
probability spaces `Ω i` with `‖X i ω‖ ≤ R`,

  `∫ Re tr exp (H + ∑ i, X i (ω i)) dπ μ ≤
    Re tr exp (H + ∑ i, log ∫ exp (X i x) dμ i)`.

This iterates `Matrix.lieb_tropp_jensen_bochner_bounded` (Part 7b) over
the product probability measure on `Π i, Ω i`. -/
theorem matrix_mgf_sum_pi_bounded
    {d m : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
    [Fintype m] [DecidableEq m]
    {Ω : m → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, MeasureTheory.Measure (Ω i))
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
    (H : Matrix d d ℂ) (hH : H.IsHermitian)
    (X : ∀ i, Ω i → Matrix d d ℂ)
    (hX : ∀ i ω, (X i ω).IsHermitian)
    (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ i ω, ‖X i ω‖ ≤ R)
    (hmeas : ∀ i, MeasureTheory.AEStronglyMeasurable (X i) (μ i)) :
    (∫ ω, (Matrix.trace
      (NormedSpace.exp (H + ∑ i, X i (ω i)))).re ∂MeasureTheory.Measure.pi μ) ≤
      (Matrix.trace (NormedSpace.exp
        (H + ∑ i, CFC.log (∫ x, NormedSpace.exp (X i x) ∂μ i)))).re := by
  classical
  -- Transport via `equivFin`.
  set e : Fin (Fintype.card m) ≃ m := (Fintype.equivFin m).symm with he_def
  set Ω' : Fin (Fintype.card m) → Type _ := fun i => Ω (e i)
  set μ' : ∀ i, MeasureTheory.Measure (Ω' i) := fun i => μ (e i)
  haveI : ∀ i, MeasureTheory.IsProbabilityMeasure (μ' i) := fun i => inferInstance
  set X' : ∀ i, Ω' i → Matrix d d ℂ := fun i ω => X (e i) ω
  have hX' : ∀ i ω, (X' i ω).IsHermitian := fun i ω => hX (e i) ω
  have hbound' : ∀ i ω, ‖X' i ω‖ ≤ R := fun i ω => hbound (e i) ω
  have hmeas' : ∀ i, MeasureTheory.AEStronglyMeasurable (X' i) (μ' i) :=
    fun i => hmeas (e i)
  have h_fin := matrix_mgf_sum_pi_fin_bounded μ' H hH X' hX' R hR hbound' hmeas'
  have hMP : MeasureTheory.MeasurePreserving
      (MeasurableEquiv.piCongrLeft Ω e)
      (MeasureTheory.Measure.pi μ')
      (MeasureTheory.Measure.pi μ) :=
    MeasureTheory.measurePreserving_piCongrLeft μ e
  -- Sum re-indexing via the equiv e.
  have h_sum_X : ∀ ω' : ∀ i : Fin (Fintype.card m), Ω' i,
      ∑ i : m, X i ((MeasurableEquiv.piCongrLeft Ω e) ω' i) =
      ∑ j : Fin (Fintype.card m), X' j (ω' j) := by
    intro ω'
    rw [← Equiv.sum_comp e (fun i : m =>
      X i ((MeasurableEquiv.piCongrLeft Ω e) ω' i))]
    refine Finset.sum_congr rfl ?_
    intro j _
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply, X']
  have h_sum_log :
      ∑ i : m, CFC.log (∫ x, NormedSpace.exp (X i x) ∂μ i) =
      ∑ j : Fin (Fintype.card m),
        CFC.log (∫ x, NormedSpace.exp (X' j x) ∂μ' j) := by
    rw [← Equiv.sum_comp e (fun i : m =>
      CFC.log (∫ x, NormedSpace.exp (X i x) ∂μ i))]
  have h_LHS_eq :
      (∫ ω, (Matrix.trace (NormedSpace.exp (H + ∑ i, X i (ω i)))).re
        ∂MeasureTheory.Measure.pi μ) =
      (∫ ω', (Matrix.trace (NormedSpace.exp (H + ∑ i, X' i (ω' i)))).re
        ∂MeasureTheory.Measure.pi μ') := by
    rw [← hMP.integral_comp']
    refine MeasureTheory.integral_congr_ae ?_
    refine MeasureTheory.ae_of_all _ ?_
    intro ω'
    show (Matrix.trace (NormedSpace.exp
        (H + ∑ i : m, X i ((MeasurableEquiv.piCongrLeft Ω e) ω' i)))).re =
      (Matrix.trace (NormedSpace.exp (H + ∑ j, X' j (ω' j)))).re
    rw [h_sum_X ω']
  rw [h_LHS_eq, h_sum_log]
  exact h_fin

end Matrix
