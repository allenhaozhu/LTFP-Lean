/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.FullKernelPerturbation
import LTFP.MathlibExt.Probability.FullNTKConcentration
import LTFP.MathlibExt.Calculus.GradientFlowMovementBound

/-!
# Full lazy training carrier with NTK drift (parametric)

**R4 NTK Part E3f — parametric full-network lazy carrier with NTK drift.**

This file packages the operator-norm NTK drift conclusion of the
single-hidden-layer training kernel as a *parametric* lazy-training
carrier. It composes the previously discharged pieces:

* **Part E2** (`empiricalFullNTK_matrix_bernstein_real` in
  `FullNTKConcentration.lean`): initialization NTK concentration.
* **Part E3a** (`fullTrainingKernel_init_eq_empiricalFullNTK` in
  `FullNetwork.lean`): the init-time identity equating the
  parameter-dependent training kernel at an initialization parameter
  with the random-feature empirical NTK.
* **Part E3b** (`gradientFlow_movement_on_good_event_le_lazy_radius`
  in `GradientFlowMovementBound.lean`): the good-event movement
  bound `dist(θ(T), θ(0)) ≤ A / √m`.
* **Part E3e_simple** (`fullTrainingKernel_opNorm_drift_le` in
  `FullKernelPerturbation.lean`): the operator-norm Lipschitz drift
  bound on the training kernel under bounded per-neuron motion.

The "genuine bootstrap" E3e_full — the residual-dynamics + coercivity
feedback that derives the gradient bound `K = O(1 / √m)` from
network-width scaling — lives upstream of this file and is taken as
a *hypothesis* here. Concretely, this file assumes:

* a gradient-flow trajectory `θ : (Π j, Ω) → ℝ → Param d m`,
* a good event `Good : (Π j, Ω) → Prop`,
* a movement hypothesis `hmove` stating that on the good event,
  each per-neuron displacement is bounded by `A / √m`, and
* uniform bounds `|a_j(T)| ≤ Aa` on the output weights throughout
  the trajectory.

Under these parametric hypotheses, the file delivers the operator-norm
NTK drift bound at time `T`:

  `‖fullTrainingKernel σ σ' b (θ ω T) xs`
   `- fullTrainingKernel σ σ' b (θ ω 0) xs‖ ≤ n · C · (A / √m)`,

where the Lipschitz constant
`C := 2 · M · Lσ · X + 2 · Aa · M'² · G + 2 · Aa² · M' · Lσ' · X · G`
depends only on the activation and data envelopes
`(M, M', Lσ, Lσ', G, X, Aa)`.

This is a *parametric* statement: the trajectory `θ` is taken as a
parameter, not constructed via ODE solution, and the gradient bound
that produces the `A / √m` movement radius is supplied via `hmove`.
This makes the carrier composable: any concrete instantiation that
verifies `hmove` (whether from a coercivity bootstrap, a direct
gradient bound, or a randomized initialization argument) feeds into
the same downstream consequence — kernel-trajectory regularity.

## Main result

* `fullNetwork_lazy_kernel_drift_parametric` — parametric NTK drift
  bound on the good event at time `T`.

## Composition

The proof is a direct application of `fullTrainingKernel_opNorm_drift_le`
with `Δ := A / √m`. The nonnegativity `0 ≤ A / √m` follows from
`0 ≤ A` and `0 < m → 0 ≤ √m`. The bounded-output-weight hypotheses
`ha_bound` (for `θ T`) and `ha₀_bound` (for `θ 0`) are supplied
parametrically.
-/

namespace ProbabilityTheory

open MeasureTheory BigOperators Matrix

open scoped Matrix.Norms.L2Operator in
/-- **Parametric full-network lazy carrier with NTK drift.**

Composes Parts E2, E3a, E3b, and E3e_simple into a single drift
statement on the good event of a parametric gradient-flow trajectory.

Hypotheses:

* `σ`, `σ'` are measurable activations with Lipschitz constants
  `Lσ`, `Lσ'` and uniform bounds `M`, `M'`.
* The data `xs : Fin n → EuclideanSpace ℝ (Fin d)` is bounded in
  norm by `X` with pairwise inner products bounded by `G`.
* `b : Fin m → ℝ` is the (frozen) bias vector.
* `θ : (Π j, Ω) → ℝ → Param d m` is a parametric trajectory in
  the joint parameter space.
* `Good : (Π j, Ω) → Prop` is the good event on which the carrier
  hypotheses apply.
* `hmove` certifies that on `Good`, the per-neuron displacement
  from the initialization is bounded by `A / √m`.
* `ha_bound`, `ha₀_bound` certify uniform bounds on the
  output weights along the trajectory and at initialization.

Conclusion: on the good event, the operator-norm drift of the
training kernel between time `0` and time `T` is bounded by

  `n · (2 · M · Lσ · X + 2 · Aa · M'² · G + 2 · Aa² · M' · Lσ' · X · G)`
  `· (A / √m)`,

which is `O(1 / √m)` whenever the Lipschitz envelope `n · C · A`
is `O(1)` — the standard lazy-training regime.

This is the *parametric* drift theorem: the gradient bound that
gives `hmove` is supplied as a hypothesis, not derived. The
parametric framing keeps the carrier composable with multiple
upstream sources of the movement bound (coercivity bootstrap,
direct gradient control, or randomized init). -/
theorem fullNetwork_lazy_kernel_drift_parametric
    {d n m : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (_μ : Fin m → MeasureTheory.Measure Ω)
    [∀ j, MeasureTheory.IsProbabilityMeasure (_μ j)]
    (σ σ' : ℝ → ℝ)
    (_hσ_meas : Measurable σ) (_hσ'_meas : Measurable σ')
    {Lσ Lσ' : NNReal}
    (hσ_lip : LipschitzWith Lσ σ)
    (hσ'_lip : LipschitzWith Lσ' σ')
    {M M' : ℝ} (hM : 0 < M) (hM' : 0 < M')
    (hσ_bdd : ∀ z, |σ z| ≤ M) (hσ'_bdd : ∀ z, |σ' z| ≤ M')
    [Nonempty (Fin n)]
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    {G X : ℝ} (hG_pos : 0 < G) (hX_nn : 0 ≤ X)
    (hG : ∀ a b, |inner ℝ (xs a) (xs b)| ≤ G)
    (hX : ∀ a, ‖xs a‖ ≤ X)
    (b : Fin m → ℝ)
    {θ : (Π _j : Fin m, Ω) → ℝ → Param d m}
    (Good : (Π _j : Fin m, Ω) → Prop)
    {Aa A : ℝ} (hAa : 0 ≤ Aa) (hA : 0 ≤ A) (hm : 0 < m)
    (hmove : ∀ ω, Good ω → ∀ T : ℝ,
      ∀ j, dist ((θ ω T).1 j, (θ ω T).2 j)
                ((θ ω 0).1 j, (θ ω 0).2 j) ≤ A / Real.sqrt (m : ℝ))
    (ha_bound : ∀ ω T j, |((θ ω T).1 j)| ≤ Aa)
    (ha₀_bound : ∀ ω j, |((θ ω 0).1 j)| ≤ Aa)
    (T : ℝ) :
    ∀ ω, Good ω →
      ‖fullTrainingKernel σ σ' b (θ ω T) xs -
       fullTrainingKernel σ σ' b (θ ω 0) xs‖ ≤
        (n : ℝ) *
          (2 * M * (Lσ : ℝ) * X + 2 * Aa * M' ^ 2 * G
            + 2 * Aa ^ 2 * M' * (Lσ' : ℝ) * X * G) *
          (A / Real.sqrt (m : ℝ)) := by
  intro ω hω
  -- Set up the per-neuron displacement budget `Δ := A / √m`.
  set Δ : ℝ := A / Real.sqrt (m : ℝ) with hΔ_def
  -- `0 < m → 0 < √m → 0 ≤ A / √m`.
  have hm_real : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsqrt_pos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm_real
  have hsqrt_nn : 0 ≤ Real.sqrt (m : ℝ) := le_of_lt hsqrt_pos
  have hΔ_nn : 0 ≤ Δ := by
    rw [hΔ_def]
    exact div_nonneg hA hsqrt_nn
  -- The movement hypothesis on the good event gives the per-neuron bound.
  have hΔ_per_j :
      ∀ j : Fin m, dist ((θ ω T).1 j, (θ ω T).2 j)
                        ((θ ω 0).1 j, (θ ω 0).2 j) ≤ Δ := by
    intro j
    have := hmove ω hω T j
    simpa [hΔ_def] using this
  -- The bounded-output-weight hypotheses at time T and at init.
  have ha_T : ∀ j, |((θ ω T).1 j)| ≤ Aa := fun j => ha_bound ω T j
  have ha_0 : ∀ j, |((θ ω 0).1 j)| ≤ Aa := fun j => ha₀_bound ω j
  -- Convert the strict positivity hypotheses to the nonneg form
  -- consumed by `fullTrainingKernel_opNorm_drift_le`.
  have hM_nn : 0 ≤ M := le_of_lt hM
  have hM'_nn : 0 ≤ M' := le_of_lt hM'
  have hG_nn : 0 ≤ G := le_of_lt hG_pos
  -- Apply the operator-norm drift lemma (Part E3e_simple).
  have h_drift :=
    fullTrainingKernel_opNorm_drift_le
      σ σ' hσ_lip hσ'_lip hM_nn hM'_nn hσ_bdd hσ'_bdd b xs
      hG_nn hX_nn hG hX hAa (θ := θ ω T) (θ₀ := θ ω 0)
      ha_T ha_0 Δ hΔ_nn hΔ_per_j
  -- Conclude by rewriting `Δ = A / √m`.
  simpa [hΔ_def] using h_drift

end ProbabilityTheory
