/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Real
import LTFP.MathlibExt.Probability.RandomFeatureDynamics

/-!
# Random-feature exact-linearization tail bound
(B8 N5 random-feature carrier)

For the output-layer-only random-feature model, the first-order
Taylor expansion of the prediction map at any base point is *exact*
— there is no nonlinear remainder in the output-layer parameter `a`.
This file packages that algebraic fact into a probabilistic tail
bound: the event that the linearization error is positive somewhere
is empty, hence has measure zero, and is therefore bounded by any
non-negative slack `δ`.

## What this file is — and what it is NOT

This file closes the **random-feature exact-linearization tail bound**
only. It is the cleanest possible "lazy training" statement in the
output-layer-only random-feature parametrization, where linearity in
`a` makes the bound trivial (the bad event is *empty*, not merely
small).

Per the honesty note attached to `RandomFeatureDynamics.lean`:

> This closes output-layer-only random-feature prediction. It does
> NOT establish hidden-weight lazy training, does NOT derive
> parameter movement from coercivity, and does NOT prove the full
> Bach (2024) lazy-NTK theorem. Those require the full lazy-NTK
> model in `LTFP/MathlibExt/Probability/NTKLazyCarrier.lean`.

## Main result

* `randomFeature_exact_lazy_linearization_tail` — for any product
  measure `Measure.pi (fun _ : Fin m => ν)` on the random-feature
  draw space, any pair of measurable parameter trajectories
  `a₀, aₜ` (the output-layer state at times `0` and `t`), and any
  slack `δ ≥ 0`,

      P{ ∃ x, |f(aₜ, x) − (f(a₀, x) + ⟨∇_a f(a₀, x), aₜ − a₀⟩)| > 0 } ≤ δ,

  because by `lazyNet_exact_linearization` the linearization error is
  identically zero for every realization, every input, and every pair
  of parameters — so the bad event is empty.

## Encoding choices

We rename the time-`t` parameter trajectory from `at` to `at_` because
`at` is a Lean keyword (used in tactic targeting). This is a purely
cosmetic rename; the mathematical statement is unchanged.
-/

namespace ProbabilityTheory

open MeasureTheory

/-- **Random-feature exact-linearization tail bound** (B8 N5 random-
feature carrier).

For the output-layer-only random-feature model, the linearization
error at any base point is identically zero (see
`lazyNet_exact_linearization`). Hence the event

  `{ω | ∃ x, 0 < |lazyNet σ ω (aₜ ω) x −
              (lazyNet σ ω (a₀ ω) x +
                ⟨∇_a (lazyNet σ ω · x) (a₀ ω), aₜ ω − a₀ ω⟩)| }`

is empty under *any* product measure on the random-feature draw
space, and is therefore bounded by any non-negative slack `δ`.

This is the cleanest possible lazy-training tail bound: it holds
deterministically (the integrand is zero pointwise), but is stated
in tail form so that downstream consumers can compose with other
probabilistic carriers without an extra wrapper.

The parameter trajectories `a₀` and `at_` may depend arbitrarily on
the random-feature draw `ω`; no measurability or integrability is
needed because the bad event is identically empty. -/
theorem randomFeature_exact_lazy_linearization_tail
    {σ : ℝ → ℝ} {d m : ℕ}
    {ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)}
    {δ : ℝ} (hδ : 0 ≤ δ)
    (a₀ at_ :
      (Fin m → EuclideanSpace ℝ (Fin d) × ℝ) →
        EuclideanSpace ℝ (Fin m)) :
    (Measure.pi (fun _ : Fin m => ν)).real
        {ω | ∃ x : EuclideanSpace ℝ (Fin d),
          0 <
            |lazyNet σ ω (at_ ω) x -
              (lazyNet σ ω (a₀ ω) x +
                inner ℝ
                  (gradient (fun a => lazyNet σ ω a x) (a₀ ω))
                  (at_ ω - a₀ ω))|}
      ≤ δ := by
  -- The bad event is empty: by `lazyNet_exact_linearization`, the
  -- linearization error is zero pointwise, so its absolute value is
  -- zero and cannot be strictly positive.
  have hempty :
      {ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ |
        ∃ x : EuclideanSpace ℝ (Fin d),
          0 <
            |lazyNet σ ω (at_ ω) x -
              (lazyNet σ ω (a₀ ω) x +
                inner ℝ
                  (gradient (fun a => lazyNet σ ω a x) (a₀ ω))
                  (at_ ω - a₀ ω))|}
        = ∅ := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false,
      not_exists]
    intro x
    -- Apply exact linearization at (a₀ ω, at_ ω, x): the difference is 0.
    have heq :
        lazyNet σ ω (at_ ω) x =
          lazyNet σ ω (a₀ ω) x +
            inner ℝ (gradient (fun a => lazyNet σ ω a x) (a₀ ω))
              (at_ ω - a₀ ω) :=
      lazyNet_exact_linearization σ ω (a₀ ω) (at_ ω) x
    -- Reduce `|0|` and conclude `¬ 0 < 0`.
    rw [heq, sub_self, abs_zero]
    exact lt_irrefl 0
  -- Rewriting the bad event to `∅` collapses the measure to `0 ≤ δ`.
  rw [hempty, measureReal_empty]
  exact hδ

end ProbabilityTheory
