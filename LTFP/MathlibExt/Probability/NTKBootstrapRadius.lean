/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.MovementFromResidualDecay

/-!
# Bootstrap radius for NTK lazy training

**R4 NTK Part E3e.6 — small-residual self-consistency.**

Once Part E3e.5 (`coercivity_preserved_under_param_drift`) tells us
that bounded parameter motion `‖θ(t) - θ(0)‖ ≤ r₀` preserves the NTK
spectral floor, the residual decay rate provided by Grönwall in turn
controls parameter motion via the gradient bound
`‖∇L(θ(t))‖ ≤ √Kmax · ‖r(t)‖`. Composing
`movement_from_residual_decay` with the trivial bound
`1 - exp(-x) ≤ 1` for `x ≥ 0` yields the *uniform* movement envelope

  `‖θ(t) - θ(0)‖ ≤ 2 √Kmax · ‖r(0)‖ / ρ`

valid for every `t ≥ 0`. If the initial residual is small enough that

  `2 √Kmax · ‖r(0)‖ / ρ ≤ r₀`,

then the bootstrap radius `r₀` is *self-consistent*: the parameter
trajectory never leaves the ball of radius `r₀` around initialization,
which is exactly the hypothesis required by Part E3e.5 to preserve
the NTK coercivity floor along the trajectory.

## Main result

* `bootstrap_radius_uniform_movement` — given the (parametric)
  exponential residual decay and gradient bound assumed by
  `movement_from_residual_decay`, the parameter movement is uniformly
  bounded by `2 √Kmax · ‖r(0)‖ / ρ` for every `t ≥ 0`. Combined with
  the small-residual hypothesis `2 √Kmax · ‖r(0)‖ / ρ ≤ r₀`, this
  delivers `‖θ(t) - θ(0)‖ ≤ r₀` uniformly in `t ≥ 0`.

This closes the self-consistency loop for the non-parametric NTK
lazy-training carrier (Part E3e.7), eliminating the need for
hypotheses of the form "the kernel is coercive at every `t`" — they
become consequences of small-residual initialization.

## References

* Bach (2024) *Learning Theory from First Principles*, §12 (NTK lazy
  training).
* `LTFP.MathlibExt.Probability.MovementFromResidualDecay` — parametric
  movement bound from residual exponential decay.
* `LTFP.MathlibExt.Probability.NTKCoercivityPreservation` — E3e.5,
  the consumer of the bootstrap radius hypothesis.
-/

namespace LTFP.MathlibExt.Probability

open Set

/-- **Bootstrap radius: uniform parameter movement bound under
exponential residual decay.**

Given:

* a parameter trajectory `θ : ℝ → E` that is differentiable and obeys
  the gradient-flow form `deriv θ t = -G t`;
* a gradient norm bound `‖G t‖ ≤ √Kmax · ‖r(0)‖ · exp(-ρ t / 2)`
  (the standard NTK-lazy-training form combining `‖∇L‖ ≤ √Kmax · ‖r‖`
  with residual exponential decay);
* a small-residual hypothesis: `2 √Kmax · ‖r(0)‖ / ρ ≤ r₀`;

then the parameter trajectory never leaves the ball of radius `r₀`
around `θ 0`:

  `‖θ(t) - θ(0)‖ ≤ r₀` for every `t ≥ 0`.

This is the deterministic core of the bootstrap argument: it shows
that the small-residual hypothesis is *self-consistent*, in the
sense that the predicted parameter motion stays inside the radius
required for Part E3e.5 to preserve the kernel coercivity floor. -/
theorem bootstrap_radius_uniform_movement
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (θ : ℝ → E)
    (hθ_diff : Differentiable ℝ θ)
    (G : ℝ → E)
    (hθ_ODE : ∀ t, deriv θ t = -G t)
    (Kmax : ℝ) (hKmax : 0 ≤ Kmax)
    (r0_norm : ℝ) (hr0_nn : 0 ≤ r0_norm)
    {ρ : ℝ} (hρ_pos : 0 < ρ)
    (hG_bound : ∀ t, ‖G t‖ ≤ Real.sqrt Kmax * (r0_norm * Real.exp (-(ρ * t / 2))))
    {r₀ : ℝ}
    (h_small : Real.sqrt Kmax * (2 * r0_norm / ρ) ≤ r₀)
    {t : ℝ} (ht : 0 ≤ t) :
    ‖θ t - θ 0‖ ≤ r₀ := by
  -- Step 1: invoke the parametric movement bound (E3e.5 historic name).
  have h_move : ‖θ t - θ 0‖ ≤
      Real.sqrt Kmax * (2 * r0_norm / ρ) * (1 - Real.exp (-(ρ * t / 2))) :=
    movement_from_residual_decay θ hθ_diff G hθ_ODE Kmax hKmax r0_norm hr0_nn
      hρ_pos hG_bound ht
  -- Step 2: `1 - exp(-(ρ t / 2)) ≤ 1` for `t ≥ 0`.
  have hexp_nn : 0 ≤ Real.exp (-(ρ * t / 2)) := (Real.exp_pos _).le
  have h_one_sub_le_one : 1 - Real.exp (-(ρ * t / 2)) ≤ 1 := by linarith
  -- Step 3: the prefactor `√Kmax · (2 r0 / ρ)` is nonneg.
  have h_sqrt_nn : 0 ≤ Real.sqrt Kmax := Real.sqrt_nonneg _
  have h_2r0 : 0 ≤ 2 * r0_norm := by positivity
  have h_2r0_div : 0 ≤ 2 * r0_norm / ρ := by positivity
  have h_pref_nn : 0 ≤ Real.sqrt Kmax * (2 * r0_norm / ρ) := by positivity
  -- Step 4: chain `h_move ≤ √Kmax · (2 r0 / ρ) · 1 = √Kmax · (2 r0 / ρ) ≤ r₀`.
  have h_envelope : Real.sqrt Kmax * (2 * r0_norm / ρ) * (1 - Real.exp (-(ρ * t / 2)))
      ≤ Real.sqrt Kmax * (2 * r0_norm / ρ) := by
    have := mul_le_mul_of_nonneg_left h_one_sub_le_one h_pref_nn
    simpa using this
  exact le_trans h_move (le_trans h_envelope h_small)

end LTFP.MathlibExt.Probability
