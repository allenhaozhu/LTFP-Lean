/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Data.Fintype.Option
import LTFP.MathlibExt.Probability.RnDerivProd

/-!
# Radon–Nikodym derivative on finite product measures

This module proves the finite-product Radon–Nikodym derivative identity:
if `μ i ≪ ν i` for every index `i : ι` (where `ι` is a finite type),
with each `ν i` σ-finite and each `μ i` s-finite, then the RN derivative
of the product measure `Measure.pi μ` with respect to `Measure.pi ν`
factors as the coordinatewise product:

```
(Measure.pi μ).rnDeriv (Measure.pi ν)
  =ᵐ[Measure.pi ν] (fun x ↦ ∏ i, (μ i).rnDeriv (ν i) (x i))
```

The proof proceeds by induction on the finite index type via
`Fintype.induction_empty_option`:

* **Base case (`ι = PEmpty`)**: the product measures collapse to a
  Dirac on the unique element, so both sides equal `1` a.e.
* **Inductive step (`ι = Option β`)**: use `pi_map_piOptionEquivProd`
  to split `Measure.pi μ` as the pushforward of
  `(Measure.pi (μ ∘ some)).prod (μ none)`, apply
  `Measure.rnDeriv_prod` (the binary case from `RnDerivProd.lean`),
  the inductive hypothesis on `β`, and `MeasurableEmbedding.rnDeriv_map`
  to transport through the measurable equivalence.
* **Transport step (`α ≃ β`)**: a measurable equivalence between index
  types transports the identity via `MeasurableEquiv.piCongrLeft`.

A companion absolute-continuity lemma `Measure.absolutelyContinuous_pi`
is proved by the same induction and is used internally by `rnDeriv_pi`
to feed the binary `rnDeriv_prod` lemma at the inductive step.

## Main results

* `MeasureTheory.Measure.absolutelyContinuous_pi`: coordinatewise
  absolute continuity implies absolute continuity of the product.
* `MeasureTheory.Measure.rnDeriv_pi`: the headline identity.

-/

noncomputable section

open MeasureTheory BigOperators

namespace MeasureTheory

namespace Measure

/-- **Absolute continuity of finite product measures.** If `μ i ≪ ν i`
for every index `i : ι` with each `ν i` σ-finite and each `μ i`
s-finite, then `Measure.pi μ ≪ Measure.pi ν`. -/
theorem absolutelyContinuous_pi :
    ∀ {ι : Type*} [Fintype ι] {α : ι → Type*}
      [∀ i, MeasurableSpace (α i)]
      (μ ν : ∀ i, Measure (α i))
      [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
      (_hμν : ∀ i, μ i ≪ ν i),
      Measure.pi μ ≪ Measure.pi ν := by
  apply Fintype.induction_empty_option
  · -- Transport across a Fintype equivalence `ι₁ ≃ ι₂`.
    intro ι₁ ι₂ _ eqv ih α _ μ ν _ _ hμν
    letI : Fintype ι₁ := Fintype.ofEquiv _ eqv.symm
    let α' : ι₁ → Type _ := fun a => α (eqv a)
    let μ' : ∀ a, Measure (α' a) := fun a => μ (eqv a)
    let ν' : ∀ a, Measure (α' a) := fun a => ν (eqv a)
    haveI : ∀ a, SigmaFinite (μ' a) := fun a => inferInstanceAs (SigmaFinite (μ (eqv a)))
    haveI : ∀ a, SigmaFinite (ν' a) := fun a => inferInstanceAs (SigmaFinite (ν (eqv a)))
    have hμν' : ∀ a, μ' a ≪ ν' a := fun a => hμν (eqv a)
    have h_ih := ih μ' ν' hμν'
    -- Push the AC across the piCongrLeft equiv.
    let e : (∀ a, α' a) ≃ᵐ (∀ b, α b) := MeasurableEquiv.piCongrLeft α eqv
    have h_pi_μ : (Measure.pi μ').map e = Measure.pi μ :=
      (MeasureTheory.measurePreserving_piCongrLeft μ eqv).map_eq
    have h_pi_ν : (Measure.pi ν').map e = Measure.pi ν :=
      (MeasureTheory.measurePreserving_piCongrLeft ν eqv).map_eq
    rw [← h_pi_μ, ← h_pi_ν]
    exact (e.measurableEmbedding).absolutelyContinuous_map h_ih
  · -- Base case: `ι = PEmpty`. Both pi μ and pi ν are dirac at the same point.
    intro α _ μ ν _ _ _hμν
    have h_μ : Measure.pi μ = Measure.dirac (isEmptyElim) :=
      pi_of_empty (α := PEmpty) μ
    have h_ν : Measure.pi ν = Measure.dirac (isEmptyElim) :=
      pi_of_empty (α := PEmpty) ν
    rw [h_μ, h_ν]
  · -- Inductive step: `ι = Option β`.
    intro β _ ih α _ μ ν _ _ hμν
    let e : (∀ i : Option β, α i) ≃ᵐ ((∀ i : β, α (some i)) × α none) :=
      MeasurableEquiv.piOptionEquivProd α
    have h_pi_μ : (Measure.pi μ).map e
        = (Measure.pi (fun i : β => μ (some i))).prod (μ none) := by
      have h : ((Measure.pi (fun i : β => μ (some i))).prod (μ none)).map e.symm
          = Measure.pi μ := pi_map_piOptionEquivProd μ
      rw [← h]
      exact MeasurableEquiv.map_map_symm e
    have h_pi_ν : (Measure.pi ν).map e
        = (Measure.pi (fun i : β => ν (some i))).prod (ν none) := by
      have h : ((Measure.pi (fun i : β => ν (some i))).prod (ν none)).map e.symm
          = Measure.pi ν := pi_map_piOptionEquivProd ν
      rw [← h]
      exact MeasurableEquiv.map_map_symm e
    have hμν_some : ∀ i : β, μ (some i) ≪ ν (some i) := fun i => hμν (some i)
    have hμν_none : μ none ≪ ν none := hμν none
    have h_ih_some : Measure.pi (fun i : β => μ (some i))
        ≪ Measure.pi (fun i : β => ν (some i)) :=
      ih (fun i : β => μ (some i)) (fun i : β => ν (some i)) hμν_some
    -- Combine via AbsolutelyContinuous.prod.
    have h_prod_ac : (Measure.pi (fun i : β => μ (some i))).prod (μ none)
        ≪ (Measure.pi (fun i : β => ν (some i))).prod (ν none) :=
      h_ih_some.prod hμν_none
    -- Pull back across e.
    have h_map_ac : (Measure.pi μ).map e ≪ (Measure.pi ν).map e := by
      rw [h_pi_μ, h_pi_ν]; exact h_prod_ac
    -- Apply e.symm to recover AC on pi μ vs pi ν.
    have h_pulled : ((Measure.pi μ).map e).map e.symm
        ≪ ((Measure.pi ν).map e).map e.symm :=
      (e.symm.measurableEmbedding).absolutelyContinuous_map h_map_ac
    simpa [MeasurableEquiv.map_symm_map] using h_pulled

/-- **Radon–Nikodym derivative of a finite product measure.** For a
finite index `ι`, if `μ i ≪ ν i` for every `i` with each `ν i`
σ-finite and each `μ i` s-finite, then the Radon–Nikodym derivative
of the product measure `Measure.pi μ` with respect to `Measure.pi ν`
factors as the coordinatewise product of the per-coordinate
Radon–Nikodym derivatives. -/
theorem rnDeriv_pi : ∀ {ι : Type*} [Fintype ι] {α : ι → Type*}
    [∀ i, MeasurableSpace (α i)]
    (μ ν : ∀ i, Measure (α i))
    [∀ i, SigmaFinite (μ i)] [∀ i, SigmaFinite (ν i)]
    (_hμν : ∀ i, μ i ≪ ν i),
    (Measure.pi μ).rnDeriv (Measure.pi ν)
      =ᵐ[Measure.pi ν] (fun x : ∀ i, α i => ∏ i, (μ i).rnDeriv (ν i) (x i)) := by
  apply Fintype.induction_empty_option
  · -- Transport across a Fintype equivalence `ι₁ ≃ ι₂`.
    intro ι₁ ι₂ _ eqv ih α _ μ ν _ _ hμν
    letI : Fintype ι₁ := Fintype.ofEquiv _ eqv.symm
    let α' : ι₁ → Type _ := fun a => α (eqv a)
    let μ' : ∀ a, Measure (α' a) := fun a => μ (eqv a)
    let ν' : ∀ a, Measure (α' a) := fun a => ν (eqv a)
    haveI : ∀ a, SigmaFinite (μ' a) := fun a => inferInstanceAs (SigmaFinite (μ (eqv a)))
    haveI : ∀ a, SigmaFinite (ν' a) := fun a => inferInstanceAs (SigmaFinite (ν (eqv a)))
    have hμν' : ∀ a, μ' a ≪ ν' a := fun a => hμν (eqv a)
    have h_ih := ih μ' ν' hμν'
    let e : (∀ a, α' a) ≃ᵐ (∀ b, α b) := MeasurableEquiv.piCongrLeft α eqv
    have he_meas : MeasurableEmbedding e := e.measurableEmbedding
    have h_pi_μ : (Measure.pi μ').map e = Measure.pi μ :=
      (MeasureTheory.measurePreserving_piCongrLeft μ eqv).map_eq
    have h_pi_ν : (Measure.pi ν').map e = Measure.pi ν :=
      (MeasureTheory.measurePreserving_piCongrLeft ν eqv).map_eq
    have h_push : (fun y : ∀ a, α' a =>
        ((Measure.pi μ').map e).rnDeriv ((Measure.pi ν').map e) (e y))
          =ᵐ[Measure.pi ν'] (Measure.pi μ').rnDeriv (Measure.pi ν') :=
      he_meas.rnDeriv_map (Measure.pi μ') (Measure.pi ν')
    rw [h_pi_μ, h_pi_ν] at h_push
    -- Convert a.e. on `pi ν'` to a.e. on `pi ν` via the measure-preserving map e.
    have h_goal_lift : ∀ᵐ x ∂(Measure.pi ν),
        (Measure.pi μ).rnDeriv (Measure.pi ν) x
          = ∏ i, (μ i).rnDeriv (ν i) (x i) := by
      have h_meas_pred : MeasurableSet
          { x : ∀ b, α b | (Measure.pi μ).rnDeriv (Measure.pi ν) x
            = ∏ i, (μ i).rnDeriv (ν i) (x i) } := by
        refine measurableSet_eq_fun ?_ ?_
        · exact measurable_rnDeriv _ _
        · exact Finset.measurable_prod _ fun i _ =>
            (measurable_rnDeriv _ _).comp (measurable_pi_apply i)
      -- Prove the ae statement on the map-side first, then transport.
      have h_map : ∀ᵐ x ∂((Measure.pi ν').map e),
          (Measure.pi μ).rnDeriv (Measure.pi ν) x
            = ∏ i, (μ i).rnDeriv (ν i) (x i) := by
        rw [ae_map_iff e.measurable.aemeasurable h_meas_pred]
        filter_upwards [h_push.symm, h_ih] with y hy hih
        rw [← hy, hih]
        -- Goal: ∏ i : ι₁, (μ' i).rnDeriv (ν' i) (y i) = ∏ i : ι₂, (μ i).rnDeriv (ν i) (e y i)
        -- The LHS uses μ' i = μ (eqv i) and ν' i = ν (eqv i) by definition.
        -- Apply Equiv.prod_comp to convert the ι₂-product to an ι₁-product:
        -- ∏ i : ι₁, (μ (eqv i)).rnDeriv (ν (eqv i)) (e y (eqv i))
        --   = ∏ b : ι₂, (μ b).rnDeriv (ν b) ((e y) b)
        rw [← Equiv.prod_comp eqv (fun b => (μ b).rnDeriv (ν b) (e y b))]
        refine Finset.prod_congr rfl (fun a _ => ?_)
        -- Goal: (μ' a).rnDeriv (ν' a) (y a) = (μ (eqv a)).rnDeriv (ν (eqv a)) (e y (eqv a))
        -- μ' a = μ (eqv a), ν' a = ν (eqv a), so LHS reduces to RHS once y a = e y (eqv a).
        show (μ (eqv a)).rnDeriv (ν (eqv a)) (y a)
          = (μ (eqv a)).rnDeriv (ν (eqv a)) ((e y) (eqv a))
        congr 1
        exact (MeasurableEquiv.piCongrLeft_apply_apply eqv y a).symm
      -- Convert: h_map is on `map e (pi ν')`; we want on `pi ν`. These are equal.
      have h_eq : (Measure.pi ν').map e = Measure.pi ν := h_pi_ν
      rw [h_eq] at h_map
      exact h_map
    exact h_goal_lift
  · -- Base case: `ι = PEmpty`.
    intro α _ μ ν _ _ _hμν
    have h_μ : Measure.pi μ = Measure.dirac (isEmptyElim) :=
      pi_of_empty (α := PEmpty) μ
    have h_ν : Measure.pi ν = Measure.dirac (isEmptyElim) :=
      pi_of_empty (α := PEmpty) ν
    have h_self : (Measure.pi μ).rnDeriv (Measure.pi ν)
        =ᵐ[Measure.pi ν] (fun _ : ∀ i : PEmpty, α i => 1) := by
      have h_eq : Measure.pi μ = Measure.pi ν := by rw [h_μ, h_ν]
      rw [h_eq]
      exact rnDeriv_self (Measure.pi ν)
    refine h_self.mono fun x hx => ?_
    show (Measure.pi μ).rnDeriv (Measure.pi ν) x
        = ∏ i : PEmpty, (μ i).rnDeriv (ν i) (x i)
    rw [hx]
    simp
  · -- Inductive step: `ι = Option β`.
    intro β _ ih α _ μ ν _ _ hμν
    let e : (∀ i : Option β, α i) ≃ᵐ ((∀ i : β, α (some i)) × α none) :=
      MeasurableEquiv.piOptionEquivProd α
    have he_meas : MeasurableEmbedding e := e.measurableEmbedding
    have h_pi_μ : (Measure.pi μ).map e
        = (Measure.pi (fun i : β => μ (some i))).prod (μ none) := by
      have h : ((Measure.pi (fun i : β => μ (some i))).prod (μ none)).map e.symm
          = Measure.pi μ := pi_map_piOptionEquivProd μ
      rw [← h]
      exact MeasurableEquiv.map_map_symm e
    have h_pi_ν : (Measure.pi ν).map e
        = (Measure.pi (fun i : β => ν (some i))).prod (ν none) := by
      have h : ((Measure.pi (fun i : β => ν (some i))).prod (ν none)).map e.symm
          = Measure.pi ν := pi_map_piOptionEquivProd ν
      rw [← h]
      exact MeasurableEquiv.map_map_symm e
    have hμν_some : ∀ i : β, μ (some i) ≪ ν (some i) := fun i => hμν (some i)
    have hμν_none : μ none ≪ ν none := hμν none
    have h_ih_some := ih (fun i : β => μ (some i)) (fun i : β => ν (some i)) hμν_some
    -- Absolute continuity for the truncated pi (needed by rnDeriv_prod).
    have h_pi_some_ac : Measure.pi (fun i : β => μ (some i))
        ≪ Measure.pi (fun i : β => ν (some i)) :=
      absolutelyContinuous_pi (fun i : β => μ (some i))
        (fun i : β => ν (some i)) hμν_some
    -- Apply DS.1: rnDeriv of a binary product.
    have h_prod : (((Measure.pi (fun i : β => μ (some i))).prod (μ none)).rnDeriv
          ((Measure.pi (fun i : β => ν (some i))).prod (ν none)))
            =ᵐ[(Measure.pi (fun i : β => ν (some i))).prod (ν none)]
            (fun z : (∀ i : β, α (some i)) × α none =>
              (Measure.pi (fun i : β => μ (some i))).rnDeriv
                (Measure.pi (fun i : β => ν (some i))) z.1
                * (μ none).rnDeriv (ν none) z.2) :=
      rnDeriv_prod (Measure.pi (fun i : β => μ (some i)))
        (Measure.pi (fun i : β => ν (some i))) (μ none) (ν none)
        h_pi_some_ac hμν_none
    -- Pull rnDeriv through the measurable equiv e.
    have h_push : (fun x : ∀ i : Option β, α i =>
        ((Measure.pi μ).map e).rnDeriv ((Measure.pi ν).map e) (e x))
          =ᵐ[Measure.pi ν] (Measure.pi μ).rnDeriv (Measure.pi ν) :=
      he_meas.rnDeriv_map (Measure.pi μ) (Measure.pi ν)
    rw [h_pi_μ, h_pi_ν] at h_push
    -- Transport h_prod (a.e. on the prod side) back to a.e. on pi ν via e.
    have h_prod_ae : ∀ᵐ x ∂(Measure.pi ν),
        ((Measure.pi (fun i : β => μ (some i))).prod (μ none)).rnDeriv
            ((Measure.pi (fun i : β => ν (some i))).prod (ν none)) (e x)
          = (Measure.pi (fun i : β => μ (some i))).rnDeriv
              (Measure.pi (fun i : β => ν (some i))) (e x).1
              * (μ none).rnDeriv (ν none) (e x).2 := by
      have h_meas_pred : MeasurableSet
          { z : (∀ i : β, α (some i)) × α none |
            ((Measure.pi (fun i : β => μ (some i))).prod (μ none)).rnDeriv
              ((Measure.pi (fun i : β => ν (some i))).prod (ν none)) z
              = (Measure.pi (fun i : β => μ (some i))).rnDeriv
                  (Measure.pi (fun i : β => ν (some i))) z.1
                  * (μ none).rnDeriv (ν none) z.2 } := by
        refine measurableSet_eq_fun ?_ ?_
        · exact measurable_rnDeriv _ _
        · exact ((measurable_rnDeriv _ _).comp measurable_fst).mul
            ((measurable_rnDeriv _ _).comp measurable_snd)
      rw [← ae_map_iff e.measurable.aemeasurable h_meas_pred, h_pi_ν]
      exact h_prod
    -- Transport h_ih_some from a.e. on pi (ν ∘ some) to a.e. on pi ν via e then fst.
    have h_ih_ae : ∀ᵐ x ∂(Measure.pi ν),
        (Measure.pi (fun i : β => μ (some i))).rnDeriv
            (Measure.pi (fun i : β => ν (some i))) (e x).1
          = ∏ i : β, (μ (some i)).rnDeriv (ν (some i)) ((e x).1 i) := by
      -- Step A: lift h_ih_some from a.e. on pi (ν ∘ some) to a.e. on (pi (ν ∘ some)).prod (ν none)
      -- via the projection. Use the direct null-set lift: for any pi (ν ∘ some)-null set s,
      -- Prod.fst ⁻¹' s has measure (pi (ν ∘ some)) s · (ν none) univ = 0 · _ = 0 in the prod.
      have h_ih_prod : ∀ᵐ z ∂((Measure.pi (fun i : β => ν (some i))).prod (ν none)),
          (Measure.pi (fun i : β => μ (some i))).rnDeriv
            (Measure.pi (fun i : β => ν (some i))) z.1
            = ∏ i : β, (μ (some i)).rnDeriv (ν (some i)) (z.1 i) := by
        -- Use map_fst_prod : ((pi (ν ∘ some)).prod (ν none)).map Prod.fst = (ν none univ) • pi (ν ∘ some).
        -- A null set in (c • pi (ν ∘ some)) is the same as in pi (ν ∘ some) (whenever 0 < c or c = 0).
        -- Easier: use the direct computation on the predicate set.
        set P : (∀ i : β, α (some i)) → Prop := fun y =>
          (Measure.pi (fun i : β => μ (some i))).rnDeriv
              (Measure.pi (fun i : β => ν (some i))) y
            = ∏ i : β, (μ (some i)).rnDeriv (ν (some i)) (y i) with hP_def
        have h_meas_P : MeasurableSet { y | P y } := by
          refine measurableSet_eq_fun ?_ ?_
          · exact measurable_rnDeriv _ _
          · exact Finset.measurable_prod _ fun i _ =>
              (measurable_rnDeriv _ _).comp (measurable_pi_apply i)
        -- h_ih_some : ∀ᵐ y ∂pi (ν ∘ some), P y, i.e. (pi (ν ∘ some)) {y | ¬ P y} = 0.
        have h_null : (Measure.pi (fun i : β => ν (some i))) { y | ¬ P y } = 0 :=
          h_ih_some
        -- Want: ((pi (ν ∘ some)).prod (ν none)) {z | ¬ P z.1} = 0.
        have h_prod_null :
            ((Measure.pi (fun i : β => ν (some i))).prod (ν none)) { z | ¬ P z.1 } = 0 := by
          -- {z | ¬ P z.1} = Prod.fst ⁻¹' {y | ¬ P y}.
          have h_preimg : { z : (∀ i : β, α (some i)) × α none | ¬ P z.1 }
              = Prod.fst ⁻¹' { y | ¬ P y } := rfl
          rw [h_preimg]
          have h_meas_neg : MeasurableSet { y | ¬ P y } := h_meas_P.compl
          rw [← Measure.map_apply measurable_fst h_meas_neg]
          rw [map_fst_prod]
          simp [Measure.smul_apply, h_null]
        exact h_prod_null
      -- Step B: lift from prod side back to pi ν via e.
      -- Use that `∀ᵐ z ∂((pi ν).map e), Q z ↔ ∀ᵐ x ∂(pi ν), Q (e x)` and
      -- `(pi ν).map e = (pi (ν ∘ some)).prod (ν none)`.
      have h_ae_lift : ∀ᵐ x ∂(Measure.pi ν),
          (Measure.pi (fun i : β => μ (some i))).rnDeriv
            (Measure.pi (fun i : β => ν (some i))) (e x).1
            = ∏ i : β, (μ (some i)).rnDeriv (ν (some i)) ((e x).1 i) := by
        have h_meas_pred : MeasurableSet
            { z : (∀ i : β, α (some i)) × α none |
              (Measure.pi (fun i : β => μ (some i))).rnDeriv
                (Measure.pi (fun i : β => ν (some i))) z.1
                = ∏ i : β, (μ (some i)).rnDeriv (ν (some i)) (z.1 i) } := by
          refine measurableSet_eq_fun ?_ ?_
          · exact (measurable_rnDeriv _ _).comp measurable_fst
          · exact Finset.measurable_prod _ fun i _ =>
              (measurable_rnDeriv _ _).comp
                ((measurable_pi_apply i).comp measurable_fst)
        rw [← ae_map_iff e.measurable.aemeasurable h_meas_pred, h_pi_ν]
        exact h_ih_prod
      exact h_ae_lift
    -- Combine all three.
    filter_upwards [h_push.symm, h_prod_ae, h_ih_ae] with x hpush hprod hih
    rw [hpush, hprod, hih]
    -- Goal: (∏ i : β, (μ (some i)).rnDeriv (ν (some i)) ((e x).1 i))
    --         * (μ none).rnDeriv (ν none) ((e x).2)
    --     = ∏ i : Option β, (μ i).rnDeriv (ν i) (x i)
    rw [Fintype.prod_option]
    -- (e x).1 = (fun i => x (some i)) and (e x).2 = x none by piOptionEquivProd defn.
    show (∏ i : β, (μ (some i)).rnDeriv (ν (some i)) ((e x).1 i))
        * (μ none).rnDeriv (ν none) ((e x).2)
      = (μ none).rnDeriv (ν none) (x none)
        * ∏ i : β, (μ (some i)).rnDeriv (ν (some i)) (x (some i))
    have h_e1 : (e x).1 = fun i => x (some i) := rfl
    have h_e2 : (e x).2 = x none := rfl
    rw [h_e1, h_e2]
    ring

end Measure

end MeasureTheory
