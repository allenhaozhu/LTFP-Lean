/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.NTKCoercivityPreservation
import LTFP.MathlibExt.Probability.NTKBootstrapRadius
import LTFP.MathlibExt.Probability.NTKLazyTrainingEndToEnd

/-!
# Non-parametric NTK lazy-training carrier

**R4 NTK Part E3e.7 — non-parametric closure of NTK lazy training.**

Composes Parts E3e.5–6 with the parametric end-to-end carrier
(`ntk_lazy_training_carrier_parametric`, E3e.7 historic) to deliver a
fully non-parametric statement: the only "K(θ(t)) is uniformly
coercive" hypothesis the parametric carrier required is now discharged
from the chain "initial NTK coercivity + small-enough parameter
movement". The user supplies the same ODE + initialization data as
before; the uniform drift hypothesis is no longer needed.

## Strategy

The parametric carrier `ntk_lazy_training_carrier_parametric` requires
* `K(θ(0)) ≽ ρ • 1` (initial coercivity), and
* `∀ t, ‖K(θ(t)) - K(θ(0))‖ ≤ ρ/2` (uniform kernel drift).

Part E3e.5 (`coercivity_preserved_under_param_drift`) shows the latter
is *equivalent to* a uniform per-neuron parameter movement bound
`∀ t, ∀ j, dist (θ(t).1 j, θ(t).2 j) (θ(0).1 j, θ(0).2 j) ≤ Δ`, modulo
the small-drift inequality `n · C · Δ ≤ ρ/2`. We turn this into the
hypothesis "uniform per-neuron movement is at most `Δ` for some `Δ`
with `n · C · Δ ≤ ρ/2`". The bootstrap argument
(`bootstrap_radius_uniform_movement`, E3e.6) shows that this is in
turn implied by a small-initial-residual hypothesis combined with the
gradient bound `‖∇L(θ(t))‖ ≤ √Kmax · ‖r(t)‖` and exponential residual
decay — but the residual decay is itself the *conclusion* of the
parametric carrier, so a continuity argument would be needed for a
fully bootstrapped statement.

The present non-parametric carrier exposes the chain by taking the
uniform per-neuron movement bound as a *hypothesis* on the trajectory.
This is the cleanest atomic statement that does NOT depend on a
multi-week continuity argument; it can be specialized to a fully
bootstrapped form once that argument is formalized upstream (e.g.,
when Mathlib's ODE library acquires a `continuity-of-trajectories +
bootstrap` lemma applicable to gradient flows on Banach spaces).

## Main result

* `ntk_lazy_training_carrier_nonparametric` — gradient-flow residual
  decay closed under the bootstrap chain E3e.5 + E3e.6 + parametric
  carrier.

## References

* Bach (2024) *Learning Theory from First Principles*, §12.
* `LTFP.MathlibExt.Probability.NTKLazyTrainingEndToEnd` — parametric
  carrier.
* `LTFP.MathlibExt.Probability.NTKCoercivityPreservation` — E3e.5.
* `LTFP.MathlibExt.Probability.NTKBootstrapRadius` — E3e.6.
-/

open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix

namespace LTFP

variable {d n m : ℕ}

/-- **Non-parametric NTK lazy-training carrier.**

Composes the per-neuron Lipschitz drift of the dynamic training kernel
(E3c.2/E3d), the coercivity-preservation lemma (E3e.5), and the
parametric residual-decay carrier (E3e.7 historic) to give a
non-parametric exponential residual-decay statement for NTK lazy
training.

The user supplies:

* Lipschitz + boundedness data on `σ, σ'`;
* data bounds on `xs`;
* bounded output weights `|θ(t).1 j| ≤ Aa` along the trajectory;
* a uniform per-neuron movement bound `Δ` (the bootstrap radius)
  along the trajectory:
  `∀ t ∀ j, dist (θ(t).1 j, θ(t).2 j) (θ(0).1 j, θ(0).2 j) ≤ Δ`;
* the small-movement inequality `n · C · Δ ≤ ρ/2` where `C` is the
  operator-norm drift constant;
* initial coercivity `ρ • 1 ≤ K(θ(0))`;
* the residual ODE `r'(t) = -(K(θ(t)) · r(t))`;
* Hermitian dynamic kernel along the trajectory.

The conclusion is the exponential residual decay

  `‖r(T)‖² ≤ ‖r(0)‖² · exp(-(ρ · T))` for all `T ≥ 0`,

with the kernel coercivity floor at every `t` provided *internally*
by E3e.5 — no `∀ t, ‖K(θ(t)) - K(θ(0))‖ ≤ ρ/2` hypothesis on the
user side. -/
theorem ntk_lazy_training_carrier_nonparametric
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
    (hΔ : ∀ t j, dist ((θ t).1 j, (θ t).2 j) ((θ 0).1 j, (θ 0).2 j) ≤ Δ)
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
  -- Step 1: discharge the uniform drift hypothesis required by the
  -- parametric carrier, via E3e.5 + the small-drift inequality.
  -- For each `t`, the operator-norm drift `‖K(θ t) - K(θ 0)‖ ≤ ρ/2`.
  have h_drift_uniform : ∀ t : ℝ,
      ‖ProbabilityTheory.fullTrainingKernel σ σ' b (θ t) xs -
        ProbabilityTheory.fullTrainingKernel σ σ' b (θ 0) xs‖ ≤ ρ / 2 := by
    intro t
    have h := ProbabilityTheory.fullTrainingKernel_opNorm_drift_le
      σ σ' hσ_lip hσ'_lip hM hM' hσ_bdd hσ'_bdd b xs hG_nn hX_nn hG hX
      hAa (ha_bound t) (ha_bound 0) Δ hΔ_nn (hΔ t)
    exact le_trans h h_small
  -- Step 2: apply the parametric carrier (E3e.7 historic).
  exact ntk_lazy_training_carrier_parametric σ σ' b xs θ hK_herm hρ_pos
    hK_init_coercive h_drift_uniform r hr_diff hr_ODE T hT

end LTFP
