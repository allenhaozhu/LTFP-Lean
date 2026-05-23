/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import LTFP.MathlibExt.Probability.NTKConcentration
import LTFP.MathlibExt.Analysis.LazyTrainingLinearization
import LTFP.MathlibExt.Calculus.MultivariateHessianTaylor
import LTFP.MathlibExt.Calculus.FDerivInnerGradient

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

/-- B8 N5 carrier specialized to a uniform Hessian-norm bound.

This wrapper composes the §49 framework (`ntk_concentration_to_lazy_linearization_framework`)
with the §55 multivariate Hessian Taylor remainder
(`LTFP.MathlibExt.Calculus.hessian_taylor_remainder_along_segment`).

The parametric `hbridge` of the framework is auto-discharged from:
* `hgrad` — a Riesz-style identification of `grad₀ ω x` with the gradient of
  `θ ↦ f θ x` at `θ₀ ω` (the gradient bridge);
* `hmove` — the parameter-movement bound `‖θt − θ₀‖ ≤ A/√m` on the NTK-good
  event (tied to specific dynamics);
* `hcont` — a uniform `C²` regularity of `θ ↦ f θ x` (per sample `x`);
* `hHess` — a uniform operator-norm bound `L` on the Hessian along the
  segment `[θ₀ ω, θt ω]`, again per sample `x`, on the NTK-good event.

The resulting tail bound is exactly the framework's conclusion. -/
theorem ntk_concentration_to_lazy_linearization_via_hessian_bound
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
    (hgrad : ∀ ω x v, (fderiv ℝ (fun θ => f θ x) (θ₀ ω)) v
              = inner ℝ (grad₀ ω x) v)
    (hmove : ∀ ω,
      ¬ ((n : ℝ) *
            (σ_inf ^ 2 * Real.sqrt (2 * Real.log (2 * (n : ℝ) ^ 2 / δ) / (m : ℝ)))
          < ‖empiricalNTK σ xs ω - populationNTK σ xs ν‖) →
        ‖θt ω - θ₀ ω‖ ≤ A / Real.sqrt (m : ℝ))
    (hcont : ∀ x : X,
      ContDiff ℝ 2 (fun θ : EuclideanSpace ℝ (Fin p) => f θ x))
    (hHess : ∀ ω,
      ¬ ((n : ℝ) *
            (σ_inf ^ 2 * Real.sqrt (2 * Real.log (2 * (n : ℝ) ^ 2 / δ) / (m : ℝ)))
          < ‖empiricalNTK σ xs ω - populationNTK σ xs ν‖) →
      ∀ x : X, ∀ z ∈ segment ℝ (θ₀ ω) (θt ω),
        ‖iteratedFDeriv ℝ 2 (fun θ : EuclideanSpace ℝ (Fin p) => f θ x) z‖ ≤ L) :
    (Measure.pi (fun _ : Fin m => ν)).real
        {ω | ∃ x : X,
          (L / 2) * (A / Real.sqrt (m : ℝ)) ^ 2 <
            |f (θt ω) x - (f (θ₀ ω) x + inner ℝ (grad₀ ω x) (θt ω - θ₀ ω))|}
      ≤ δ := by
  -- Build the framework's `hbridge` from the per-sample Hessian Taylor lemma.
  have hbridge : ∀ ω,
      ¬ ((n : ℝ) *
            (σ_inf ^ 2 * Real.sqrt (2 * Real.log (2 * (n : ℝ) ^ 2 / δ) / (m : ℝ)))
          < ‖empiricalNTK σ xs ω - populationNTK σ xs ν‖) →
        ‖θt ω - θ₀ ω‖ ≤ A / Real.sqrt (m : ℝ) ∧
        ∀ x : X,
          |f (θt ω) x - (f (θ₀ ω) x + inner ℝ (grad₀ ω x) (θt ω - θ₀ ω))|
            ≤ (L / 2) * ‖θt ω - θ₀ ω‖ ^ 2 := by
    intro ω hgood
    refine ⟨hmove ω hgood, ?_⟩
    intro x
    -- Apply the multivariate Hessian Taylor remainder to `θ ↦ f θ x`.
    have htaylor :
        |f (θt ω) x - f (θ₀ ω) x
            - (fderiv ℝ (fun θ => f θ x) (θ₀ ω)) (θt ω - θ₀ ω)|
          ≤ (L / 2) * ‖θt ω - θ₀ ω‖ ^ 2 :=
      LTFP.MathlibExt.Calculus.hessian_taylor_remainder_along_segment
        (f := fun θ => f θ x) (x₀ := θ₀ ω) (x₁ := θt ω) (L := L)
        (hcont x) (hHess ω hgood x)
    -- Rewrite the linear part via the gradient bridge `hgrad`.
    have hrw :
        (fderiv ℝ (fun θ => f θ x) (θ₀ ω)) (θt ω - θ₀ ω)
          = inner ℝ (grad₀ ω x) (θt ω - θ₀ ω) := hgrad ω x (θt ω - θ₀ ω)
    rw [hrw] at htaylor
    -- Normalize `a - b - c` vs `a - (b + c)`.
    have hgroup :
        f (θt ω) x - f (θ₀ ω) x - inner ℝ (grad₀ ω x) (θt ω - θ₀ ω)
          = f (θt ω) x - (f (θ₀ ω) x + inner ℝ (grad₀ ω x) (θt ω - θ₀ ω)) := by
      ring
    rw [hgroup] at htaylor
    exact htaylor
  -- Apply the §49 framework theorem with the constructed `hbridge`.
  exact ntk_concentration_to_lazy_linearization_framework
    hσ_meas hσ_pos hσ_bdd hn xs hm (ν := ν) hδ_pos hδ_lt
    f θ₀ θt grad₀ A L hA hL hbridge

/-- §56 EuclideanSpace specialization: the `hgrad` Riesz hypothesis is
auto-discharged.

On the finite-dimensional Hilbert space `EuclideanSpace ℝ (Fin p)`, the
Riesz representation identifies `fderiv ℝ (fun θ => f θ x) (θ₀ ω) v`
with `inner ℝ (gradient (fun θ => f θ x) (θ₀ ω)) v` whenever the inner
function is differentiable at `θ₀ ω`. Under the `ContDiff ℝ 2`
hypothesis `hcont`, differentiability is automatic, so `hgrad` is
redundant — we instantiate `grad₀ ω x` as Mathlib's
`gradient (fun θ => f θ x) (θ₀ ω)` and discharge the Riesz bridge with
`LTFP.MathlibExt.Calculus.fderiv_eq_inner_gradient_of_contDiff`.

This wrapper packages the EuclideanSpace-specific shape that §56's
downstream clients actually consume. -/
theorem ntk_concentration_to_lazy_linearization_via_hessian_bound_euclidean
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
    (A L : ℝ) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hmove : ∀ ω,
      ¬ ((n : ℝ) *
            (σ_inf ^ 2 * Real.sqrt (2 * Real.log (2 * (n : ℝ) ^ 2 / δ) / (m : ℝ)))
          < ‖empiricalNTK σ xs ω - populationNTK σ xs ν‖) →
        ‖θt ω - θ₀ ω‖ ≤ A / Real.sqrt (m : ℝ))
    (hcont : ∀ x : X,
      ContDiff ℝ 2 (fun θ : EuclideanSpace ℝ (Fin p) => f θ x))
    (hHess : ∀ ω,
      ¬ ((n : ℝ) *
            (σ_inf ^ 2 * Real.sqrt (2 * Real.log (2 * (n : ℝ) ^ 2 / δ) / (m : ℝ)))
          < ‖empiricalNTK σ xs ω - populationNTK σ xs ν‖) →
      ∀ x : X, ∀ z ∈ segment ℝ (θ₀ ω) (θt ω),
        ‖iteratedFDeriv ℝ 2 (fun θ : EuclideanSpace ℝ (Fin p) => f θ x) z‖ ≤ L) :
    (Measure.pi (fun _ : Fin m => ν)).real
        {ω | ∃ x : X,
          (L / 2) * (A / Real.sqrt (m : ℝ)) ^ 2 <
            |f (θt ω) x - (f (θ₀ ω) x +
                inner ℝ (gradient (fun θ : EuclideanSpace ℝ (Fin p) => f θ x) (θ₀ ω))
                      (θt ω - θ₀ ω))|}
      ≤ δ := by
  -- Instantiate `grad₀ ω x := gradient (fun θ => f θ x) (θ₀ ω)` and discharge
  -- `hgrad` via the Riesz bridge `fderiv_eq_inner_gradient_of_contDiff`.
  refine ntk_concentration_to_lazy_linearization_via_hessian_bound
    hσ_meas hσ_pos hσ_bdd hn xs hm (ν := ν) hδ_pos hδ_lt
    f θ₀ θt
    (fun ω x => gradient (fun θ : EuclideanSpace ℝ (Fin p) => f θ x) (θ₀ ω))
    A L hA hL ?_ hmove hcont hHess
  intro ω x v
  exact LTFP.MathlibExt.Calculus.fderiv_eq_inner_gradient_of_contDiff (hcont x) (θ₀ ω) v

end ProbabilityTheory
