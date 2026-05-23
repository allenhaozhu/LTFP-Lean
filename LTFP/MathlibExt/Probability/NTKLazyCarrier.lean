/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import LTFP.MathlibExt.Probability.NTKConcentration
import LTFP.MathlibExt.Analysis.LazyTrainingLinearization

/-!
# B8 N5 framework carrier: NTK concentration ⟹ lazy linearization tail

This file composes the two existing sub-carriers for B8 N5:

* `ntk_concentration_scalar_hoeffding`
  (`LTFP/MathlibExt/Probability/NTKConcentration.lean`) — the scalar-
  Hoeffding NTK operator-norm tail bound.
* `lazy_training_linearization_from_taylor`
  (`LTFP/MathlibExt/Analysis/LazyTrainingLinearization.lean`) — the
  deterministic Taylor sub-step turning a movement bound plus Taylor
  remainder into the quadratic lazy-linearization-error bound.

The composition is mediated by a single *parametric bridge hypothesis*
`hbridge`, which makes the deferred analytic/probabilistic work
explicit: on the NTK-good event one must derive both the parameter-
movement bound `‖θt − θ₀‖ ≤ A/√m` and the multivariate first-order
Taylor remainder `|f(θt;x) − f(θ₀;x) − ⟨∇f(θ₀;x), θt − θ₀⟩|
≤ (L/2) ‖θt − θ₀‖²`. Both pieces are still genuine multi-week upstream
work (parameter-movement bound from NTK + multivariate Hessian Taylor).

This framework theorem is the carrier shape: once `hbridge` is
discharged, one immediately gets the lazy-linearization tail bound
`μ.real { lazy-bad event } ≤ δ`.
-/

open scoped RealInnerProductSpace Matrix.Norms.L2Operator
open MeasureTheory

namespace ProbabilityTheory

/-- Framework carrier theorem for B8 N5: NTK concentration plus a bridge from the
NTK-good event to movement and Taylor remainder control implies the carrier-facing
lazy-linearization tail bound.

The bridge hypothesis is exactly the deferred analytic/probabilistic work: derive
parameter movement and the multivariate Taylor remainder on the NTK-good event. -/
theorem ntk_concentration_to_lazy_linearization_framework
    {σ : ℝ → ℝ} (hσ_meas : Measurable σ)
    {σ_inf : ℝ} (hσ_pos : 0 < σ_inf) (hσ_bdd : ∀ z, |σ z| ≤ σ_inf)
    {d n p : ℕ} (hn : 0 < n)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    {m : ℕ} (hm : 0 < m)
    {ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)} [IsProbabilityMeasure ν]
    {δ : ℝ} (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    {X : Type*}
    (f : EuclideanSpace ℝ (Fin p) → X → ℝ)
    (θ₀ θt : (Fin m → EuclideanSpace ℝ (Fin d) × ℝ) → EuclideanSpace ℝ (Fin p))
    (grad₀ : (Fin m → EuclideanSpace ℝ (Fin d) × ℝ) → X → EuclideanSpace ℝ (Fin p))
    (A L : ℝ) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hbridge : ∀ ω,
      ¬ ((n : ℝ) *
            (σ_inf ^ 2 * Real.sqrt (2 * Real.log (2 * (n : ℝ) ^ 2 / δ) / (m : ℝ)))
          < ‖empiricalNTK σ xs ω - populationNTK σ xs ν‖) →
        ‖θt ω - θ₀ ω‖ ≤ A / Real.sqrt (m : ℝ) ∧
        ∀ x : X,
          |f (θt ω) x - (f (θ₀ ω) x + inner ℝ (grad₀ ω x) (θt ω - θ₀ ω))|
            ≤ (L / 2) * ‖θt ω - θ₀ ω‖ ^ 2) :
    (Measure.pi (fun _ : Fin m => ν)).real
        {ω | ∃ x : X,
          (L / 2) * (A / Real.sqrt (m : ℝ)) ^ 2 <
            |f (θt ω) x - (f (θ₀ ω) x + inner ℝ (grad₀ ω x) (θt ω - θ₀ ω))|}
      ≤ δ := by
  let μ : Measure (Fin m → EuclideanSpace ℝ (Fin d) × ℝ) :=
    Measure.pi (fun _ : Fin m => ν)
  let rate : ℝ :=
    (n : ℝ) *
      (σ_inf ^ 2 * Real.sqrt (2 * Real.log (2 * (n : ℝ) ^ 2 / δ) / (m : ℝ)))
  let ntkBad : Set (Fin m → EuclideanSpace ℝ (Fin d) × ℝ) :=
    {ω | rate < ‖empiricalNTK σ xs ω - populationNTK σ xs ν‖}
  let lazyBad : Set (Fin m → EuclideanSpace ℝ (Fin d) × ℝ) :=
    {ω | ∃ x : X,
      (L / 2) * (A / Real.sqrt (m : ℝ)) ^ 2 <
        |f (θt ω) x - (f (θ₀ ω) x + inner ℝ (grad₀ ω x) (θt ω - θ₀ ω))|}
  have hlazy_of_good : ∀ ω, ω ∉ ntkBad →
      ∀ x : X,
        |f (θt ω) x - (f (θ₀ ω) x + inner ℝ (grad₀ ω x) (θt ω - θ₀ ω))|
          ≤ (L / 2) * (A / Real.sqrt (m : ℝ)) ^ 2 := by
    intro ω hgood
    have hgood' :
        ¬ ((n : ℝ) *
              (σ_inf ^ 2 * Real.sqrt (2 * Real.log (2 * (n : ℝ) ^ 2 / δ) / (m : ℝ)))
            < ‖empiricalNTK σ xs ω - populationNTK σ xs ν‖) := by
      simpa [ntkBad, rate] using hgood
    exact LTFP.MathlibExt.Analysis.lazy_training_linearization_from_taylor
      f (θ₀ ω) (θt ω) (grad₀ ω) m A L hm hA hL
      ((hbridge ω hgood').1) ((hbridge ω hgood').2)
  have hsubset : lazyBad ⊆ ntkBad := by
    intro ω hω
    by_contra hgood
    rcases hω with ⟨x, hx⟩
    exact (not_lt_of_ge (hlazy_of_good ω hgood x)) hx
  have hconc := ntk_concentration_scalar_hoeffding
    hσ_meas hσ_pos hσ_bdd hn xs hm (ν := ν) hδ_pos hδ_lt
  calc
    (Measure.pi (fun _ : Fin m => ν)).real
        {ω | ∃ x : X,
          (L / 2) * (A / Real.sqrt (m : ℝ)) ^ 2 <
            |f (θt ω) x - (f (θ₀ ω) x + inner ℝ (grad₀ ω x) (θt ω - θ₀ ω))|}
        = μ.real lazyBad := by rfl
    _ ≤ μ.real ntkBad := measureReal_mono hsubset (measure_ne_top μ _)
    _ ≤ δ := by
      simpa [μ, ntkBad, rate] using hconc

end ProbabilityTheory
