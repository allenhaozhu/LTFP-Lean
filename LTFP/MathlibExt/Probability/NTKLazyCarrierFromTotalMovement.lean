/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.NTKLazyCarrierNonParametric

/-!
# Non-parametric NTK lazy-training carrier from a total-movement bound

**R4 NTK Part E3e.8 — total-movement discharge.**

The non-parametric carrier `ntk_lazy_training_carrier_nonparametric`
(Part E3e.7) consumes a *per-neuron* parameter movement bound
`∀ t ∀ j, dist ((θ t).1 j, (θ t).2 j) ((θ 0).1 j, (θ 0).2 j) ≤ Δ`. The
upstream `bootstrap_radius_uniform_movement` (Part E3e.6) produces a
*total* movement bound `‖θ t - θ 0‖ ≤ r₀`. The present module bridges
the two:

* `param_per_neuron_dist_le_norm_sub` — for any two parameters
  `θ θ₀ : Param d m`, the per-neuron distance is at most the product
  norm `‖θ - θ₀‖`.
* `ntk_lazy_training_carrier_from_total_movement` — non-parametric
  carrier where the user supplies a uniform *total* movement bound
  `‖θ t - θ 0‖ ≤ Δ` instead of a per-neuron bound. Discharges per-neuron
  via the projection lemma.

This is the atomic piece needed to compose `bootstrap_radius_uniform_movement`
(or any future global-trajectory bound on the gradient-flow ODE) with
the non-parametric carrier without re-doing the carrier proof.

## On the bootstrap continuity argument

Closing the *full* "from-small-initial-residual" loop — i.e., deriving
the uniform total-movement bound from a small-initial-residual
hypothesis alone — requires a connectedness/clopen bootstrap argument
on the gradient-flow trajectory: the set of times at which the movement
inequality is strict is open (by continuity of the trajectory) and
closed (by the carrier's exponential decay giving a strict residual
upper bound), hence equals `[0, ∞)`. This is the standard "open and
closed" argument in NTK lazy-training papers (Du et al., Allen-Zhu et
al.). In Mathlib it requires:

* `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt` — local
  existence (already in Mathlib).
* Global extension via the energy bound `gradient_flow_energy_deriv_nonpos`
  (already in LTFP `MathlibExt.Calculus.GradientFlow`).
* Strict-inequality persistence (open) + supremum closure (closed)
  — bespoke connectedness argument not yet in Mathlib.

The bespoke connectedness argument is parked as Part 1.C of the R4 NTK
discharge plan: see `PROGRESS.md §3 ntk-lazy-training`. The present
module closes Parts 1.A + 1.B + 1.D modulo that bootstrap.

## Main results

* `param_per_neuron_dist_le_norm_sub` — per-neuron distance bound (1.A).
* `ntk_lazy_training_carrier_from_total_movement` — from total movement
  bound (1.B + 1.D).

## References

* Bach (2024) *Learning Theory from First Principles*, §12.
* `LTFP.MathlibExt.Probability.NTKLazyCarrierNonParametric` — E3e.7
  per-neuron-movement carrier (the consumer of this wrapper).
* `LTFP.MathlibExt.Probability.NTKBootstrapRadius` — E3e.6
  total-movement bound (a natural producer of the new hypothesis).
-/

open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix

namespace LTFP

variable {d m : ℕ}

/-- **Part 1.A: per-neuron distance is bounded by the product norm.**

For two parameters `θ θ₀ : Param d m = (Fin m → ℝ) × (Fin m → EuclideanSpace ℝ (Fin d))`,
the per-neuron pair-distance `dist ((θ.1 j, θ.2 j), (θ₀.1 j, θ₀.2 j))`
(a `max` of two coordinate distances) is bounded by the product norm
`‖θ - θ₀‖` (a `max` of two pi-norms).

This is the projection lemma used to convert any uniform *total* movement
bound `‖θ - θ₀‖ ≤ Δ` into the per-neuron form
`∀ j, dist ((θ.1 j, θ.2 j), (θ₀.1 j, θ₀.2 j)) ≤ Δ` required by the
non-parametric carrier. -/
theorem param_per_neuron_dist_le_norm_sub
    (θ θ₀ : ProbabilityTheory.Param d m) (j : Fin m) :
    dist ((θ.1 j, θ.2 j)) ((θ₀.1 j, θ₀.2 j)) ≤ ‖θ - θ₀‖ := by
  -- `dist` on a product = max of coordinate distances.
  rw [Prod.dist_eq]
  -- Goal: `max (dist (θ.1 j) (θ₀.1 j)) (dist (θ.2 j) (θ₀.2 j)) ≤ ‖θ - θ₀‖`.
  -- `‖θ - θ₀‖` on a product = max of pi norms.
  rw [Prod.norm_def]
  -- Goal: `max (dist (θ.1 j) (θ₀.1 j)) (dist (θ.2 j) (θ₀.2 j)) ≤ max ‖(θ - θ₀).1‖ ‖(θ - θ₀).2‖`.
  refine max_le_max ?_ ?_
  · -- dist on the 1-component ≤ pi-norm of the 1-component of the diff.
    have h1 : dist (θ.1 j) (θ₀.1 j) = ‖θ.1 j - θ₀.1 j‖ := by
      rw [dist_eq_norm]
    rw [h1]
    have h2 : θ.1 j - θ₀.1 j = (θ - θ₀).1 j := by
      simp [Prod.fst_sub]
    rw [h2]
    -- For the pi-norm: each component norm ≤ the sup-norm of the function.
    exact norm_le_pi_norm ((θ - θ₀).1) j
  · -- dist on the 2-component ≤ pi-norm of the 2-component of the diff.
    have h1 : dist (θ.2 j) (θ₀.2 j) = ‖θ.2 j - θ₀.2 j‖ := by
      rw [dist_eq_norm]
    rw [h1]
    have h2 : θ.2 j - θ₀.2 j = (θ - θ₀).2 j := by
      simp [Prod.snd_sub]
    rw [h2]
    exact norm_le_pi_norm ((θ - θ₀).2) j

/-- **Part 1.B: trajectory per-neuron movement from a total-movement bound.**

If a parameter trajectory `θ : ℝ → Param d m` has uniform total-movement
`‖θ t - θ 0‖ ≤ Δ` for every `t`, then per-neuron pair-distance is also
bounded by `Δ`:

  `∀ t ∀ j, dist ((θ t).1 j, (θ t).2 j) ((θ 0).1 j, (θ 0).2 j) ≤ Δ`.

This is a pointwise composition of `param_per_neuron_dist_le_norm_sub`
with the trajectory total-movement bound. -/
theorem param_per_neuron_movement_from_total_movement
    (θ : ℝ → ProbabilityTheory.Param d m)
    {Δ : ℝ}
    (h_total : ∀ t : ℝ, ‖θ t - θ 0‖ ≤ Δ) :
    ∀ t : ℝ, ∀ j : Fin m,
      dist ((θ t).1 j, (θ t).2 j) ((θ 0).1 j, (θ 0).2 j) ≤ Δ := by
  intro t j
  exact le_trans (param_per_neuron_dist_le_norm_sub (θ t) (θ 0) j) (h_total t)

/-- **Part 1.D: non-parametric NTK lazy-training carrier from a total
movement bound.**

Variant of `ntk_lazy_training_carrier_nonparametric` (Part E3e.7) where
the user supplies a uniform *total* movement bound `‖θ t - θ 0‖ ≤ Δ`
instead of a per-neuron bound. The per-neuron bound is discharged
internally via `param_per_neuron_movement_from_total_movement` (Part 1.A
+ 1.B).

This is the interface intended to be consumed by
`bootstrap_radius_uniform_movement` (Part E3e.6) once the bootstrap
continuity argument (Part 1.C) lands: that bootstrap produces a uniform
total-movement bound from a small-initial-residual hypothesis, and the
present theorem then closes the chain to the exponential residual decay
without any per-neuron-movement hypothesis on the user side.

Hypotheses (same as the per-neuron carrier, with the per-neuron `hΔ`
replaced by the total-movement `h_total`):

* Lipschitz + boundedness data on `σ, σ'`;
* data bounds on `xs`;
* bounded output weights `|θ(t).1 j| ≤ Aa` along the trajectory;
* uniform *total* parameter movement bound `‖θ t - θ 0‖ ≤ Δ`;
* the small-movement inequality `n · C · Δ ≤ ρ/2`;
* initial coercivity `ρ • 1 ≤ K(θ(0))`;
* the residual ODE `r'(t) = -(K(θ(t)) · r(t))`;
* Hermitian dynamic kernel along the trajectory.

Conclusion: `‖r(T)‖² ≤ ‖r(0)‖² · exp(-(ρ · T))` for all `T ≥ 0`. -/
theorem ntk_lazy_training_carrier_from_total_movement
    {n : ℕ}
    [Nonempty (Fin n)]
    (σ σ' : ℝ → ℝ)
    {Lσ Lσ' : NNReal}
    (hσ_lip : LipschitzWith Lσ σ)
    (hσ'_lip : LipschitzWith Lσ' σ')
    {M M' : ℝ} (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (hσ_bdd : ∀ z, |σ z| ≤ M)
    (hσ'_bdd : ∀ z, |σ' z| ≤ M')
    (b : Fin m → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    {G X : ℝ} (hG_nn : 0 ≤ G) (hX_nn : 0 ≤ X)
    (hG : ∀ a b, |inner ℝ (xs a) (xs b)| ≤ G)
    (hX : ∀ a, ‖xs a‖ ≤ X)
    {Aa : ℝ} (hAa : 0 ≤ Aa)
    (θ : ℝ → ProbabilityTheory.Param d m)
    (ha_bound : ∀ t j, |(θ t).1 j| ≤ Aa)
    (Δ : ℝ) (hΔ_nn : 0 ≤ Δ)
    (h_total : ∀ t : ℝ, ‖θ t - θ 0‖ ≤ Δ)
    {ρ : ℝ} (hρ_pos : 0 < ρ)
    (hK_herm : ∀ t,
      (ProbabilityTheory.fullTrainingKernel σ σ' b (θ t) xs).IsHermitian)
    (hK_init_coercive :
      (ρ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤
        ProbabilityTheory.fullTrainingKernel σ σ' b (θ 0) xs)
    (h_small :
      (n : ℝ) *
        (2 * M * (Lσ : ℝ) * X + 2 * Aa * M' ^ 2 * G
          + 2 * Aa ^ 2 * M' * (Lσ' : ℝ) * X * G) * Δ ≤ ρ / 2)
    (r : ℝ → EuclideanSpace ℝ (Fin n))
    (hr_diff : Differentiable ℝ r)
    (hr_ODE : ∀ t,
      deriv r t = -(WithLp.toLp 2
        ((ProbabilityTheory.fullTrainingKernel σ σ' b (θ t) xs) *ᵥ
          WithLp.ofLp (r t))))
    (T : ℝ) (hT : 0 ≤ T) :
    ‖r T‖ ^ 2 ≤ ‖r 0‖ ^ 2 * Real.exp (-(ρ * T)) := by
  -- Step 1: convert the total-movement hypothesis to per-neuron.
  have hΔ : ∀ t : ℝ, ∀ j : Fin m,
      dist ((θ t).1 j, (θ t).2 j) ((θ 0).1 j, (θ 0).2 j) ≤ Δ :=
    param_per_neuron_movement_from_total_movement θ h_total
  -- Step 2: apply the per-neuron non-parametric carrier (E3e.7).
  exact ntk_lazy_training_carrier_nonparametric
    σ σ' hσ_lip hσ'_lip hM hM' hσ_bdd hσ'_bdd b xs hG_nn hX_nn hG hX hAa
    θ ha_bound Δ hΔ_nn hΔ hρ_pos hK_herm hK_init_coercive h_small
    r hr_diff hr_ODE T hT

end LTFP
