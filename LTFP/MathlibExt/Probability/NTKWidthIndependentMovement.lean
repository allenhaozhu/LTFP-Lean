/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.MovementFromResidualDecay
import LTFP.MathlibExt.Probability.NTKLazyTrainingEndToEnd

/-!
# Width-independent parameter-movement bound for NTK lazy training

**Phase 2b of the Chizat-Bach `O(1/√p)` verified pipeline.**

The Chizat & Bach (2019) `1/√p` mechanism for two-layer networks under
the canonical NTK `1/√m` output-weight scaling is often mis-stated as
*"the parameter movement shrinks with width"*. The correct statement is:

* **movement stays width-independent** — `‖θ(t) - θ₀‖ ≤ R` with `R`
  depending only on the initial residual, the NTK spectral gap `ρ`,
  and the gradient-flow kernel-norm constant `√Kmax`;
* **the Hessian scales as `L₀ / √m`** (Phase 2a's uniform-on-compact
  bound, refined in Phase 2c);
* the Taylor remainder
  `|f_θ - f^{lin}_θ| ≤ (L₀ / (2 √m)) · R² = O(1/√m)`
  is `O(1/√p)` because of the *Hessian factor*, not because movement
  shrinks.

This module builds the movement bound in the exact parametric-shell
form Codex prescribed. Concretely, the theorem consumes the residual
decay produced by `ntk_lazy_training_carrier_parametric`
(`‖r(T)‖² ≤ ‖r(0)‖² · exp(-ρT)`) and a kernel-operator control on the
gradient `‖G(t)‖ ≤ √Kmax · ‖r(t)‖`, and returns the uniform-in-`T`
movement bound

    `‖θ(T) - θ(0)‖ ≤ 2 √Kmax · ‖r(0)‖ / ρ`.

The right-hand side depends on `Kmax`, `‖r(0)‖`, and `ρ`, all of which
are width-independent in the standard NTK lazy-training analysis.

## Design (Codex parametric-shell)

We take the shortest composition route:

* **existing substrate.**
  `LTFP.MathlibExt.Probability.MovementFromResidualDecay` already
  proves the deterministic fencing bound
  `‖θ(T) - θ(0)‖ ≤ √Kmax · (2 ‖r₀‖ / ρ) · (1 - exp(-ρT/2))`
  from
  `‖deriv θ t‖ ≤ √Kmax · ‖r(0)‖ · exp(-ρt/2)`;
* **this module.**
  * Lift the `‖r(T)‖² ≤ ‖r(0)‖² · exp(-ρT)` decay produced by
    `ntk_lazy_training_carrier_parametric` to
    `‖r(t)‖ ≤ ‖r(0)‖ · exp(-ρt/2)` via a square-root step
    (`ntk_residual_norm_decay_from_sq_decay`).
  * Compose with `‖G t‖ ≤ √Kmax · ‖r(t)‖` and the fencing lemma to get
    the exponentially-shrinking-remainder movement bound
    (`ntk_movement_bound_from_carrier`).
  * Drop the `(1 - exp)` factor to obtain the clean uniform-in-`T`
    width-independent constant
    `R = 2 √Kmax · ‖r(0)‖ / ρ`
    (`gradient_flow_movement_bounded`).

## Main results

* `ntk_residual_norm_decay_from_sq_decay` — square-root normalization
  of the `‖r(T)‖² ≤ ‖r(0)‖² · exp(-ρT)` residual decay.
* `ntk_movement_bound_from_carrier` — parametric-shell movement bound
  with the exponentially-tightening remainder factor.
* `gradient_flow_movement_bounded` — the headline width-independent
  movement bound `‖θ(T) - θ(0)‖ ≤ 2 √Kmax · ‖r(0)‖ / ρ`, uniform in
  `T ≥ 0`.
* `gradient_flow_movement_bounded_width_independent` — witness form,
  packaging the bound `R = 2 √Kmax · ‖r(0)‖ / ρ` as an existential
  whose value is a formal expression in `Kmax`, `‖r(0)‖`, `ρ` only —
  no width variable appears.

## References

* Chizat & Bach (2019), *On lazy training in differentiable programming*.
* Bach (2024) *Learning Theory from First Principles* §12.
* `LTFP.MathlibExt.Probability.MovementFromResidualDecay` — the
  underlying fencing bound.
* `LTFP.MathlibExt.Probability.NTKLazyTrainingEndToEnd` — the residual
  decay carrier.
-/

namespace LTFP.MathlibExt.Probability

open Set

/-! ## Square-root normalization of the residual decay -/

/-- **Square-root normalization of `‖r‖²` residual decay.**

If `‖r(T)‖² ≤ ‖r(0)‖² · exp(-ρ T)` and `ρ > 0`, then
`‖r(T)‖ ≤ ‖r(0)‖ · exp(-ρ T / 2)`. This is the elementary
`Real.sqrt` step needed to feed the residual-decay carrier's
`‖r‖²`-shape output into the fencing lemma
`movement_from_residual_decay`, which expects `‖r‖`. -/
theorem ntk_residual_norm_decay_from_sq_decay
    {r0_norm : ℝ} (hr0_nn : 0 ≤ r0_norm)
    {ρ : ℝ} (_hρ_pos : 0 < ρ)
    {rT_norm : ℝ} (_hrT_nn : 0 ≤ rT_norm)
    (T : ℝ)
    (h_sq : rT_norm ^ 2 ≤ r0_norm ^ 2 * Real.exp (-(ρ * T))) :
    rT_norm ≤ r0_norm * Real.exp (-(ρ * T / 2)) := by
  -- Both sides are nonneg; compare squares.
  have h_rhs_nn : 0 ≤ r0_norm * Real.exp (-(ρ * T / 2)) :=
    mul_nonneg hr0_nn (Real.exp_pos _).le
  -- Show `(rT_norm)^2 ≤ (r0_norm * exp(-ρT/2))^2`.
  have h_sq_of_rhs :
      (r0_norm * Real.exp (-(ρ * T / 2))) ^ 2
        = r0_norm ^ 2 * Real.exp (-(ρ * T)) := by
    have h_exp : Real.exp (-(ρ * T / 2)) ^ 2 = Real.exp (-(ρ * T)) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [mul_pow, h_exp]
  have h_sq_le :
      rT_norm ^ 2 ≤ (r0_norm * Real.exp (-(ρ * T / 2))) ^ 2 := by
    rw [h_sq_of_rhs]; exact h_sq
  exact abs_le_of_sq_le_sq' h_sq_le h_rhs_nn |>.2

/-! ## Parametric-shell movement bound with tightening remainder -/

/-- **Parametric-shell movement bound: exponentially-tightening form.**

Given:

* a differentiable parameter trajectory `θ : ℝ → E`;
* its gradient field `G : ℝ → E` with the gradient-flow ODE
  `deriv θ t = -G t`;
* a residual norm process `r_norm : ℝ → ℝ` (a placeholder for the
  scalar `‖r(t)‖`) with `r_norm(0) = r0_norm ≥ 0`, exponential decay
  `r_norm(t) ≤ r0_norm · exp(-ρ t / 2)` (for every `t`), and a
  kernel-operator gradient bound
  `‖G t‖ ≤ √Kmax · r_norm(t)`;
* `Kmax ≥ 0` and `ρ > 0`;

we conclude the fencing-tight movement bound

    `‖θ(T) - θ(0)‖ ≤ √Kmax · (2 r0_norm / ρ) · (1 - exp(-ρT/2))`

for every `T ≥ 0`. This is the exponentially-shrinking-remainder
form; the width-independent uniform bound
`‖θ(T) - θ(0)‖ ≤ 2 √Kmax · r0_norm / ρ` follows as a corollary
(`gradient_flow_movement_bounded`). -/
theorem ntk_movement_bound_from_carrier
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (θ : ℝ → E)
    (hθ_diff : Differentiable ℝ θ)
    (G : ℝ → E)
    (hθ_ODE : ∀ t, deriv θ t = -G t)
    (Kmax : ℝ) (hKmax : 0 ≤ Kmax)
    (r_norm : ℝ → ℝ)
    (r0_norm : ℝ) (hr0_nn : 0 ≤ r0_norm)
    {ρ : ℝ} (hρ_pos : 0 < ρ)
    (hr_decay : ∀ t, r_norm t ≤ r0_norm * Real.exp (-(ρ * t / 2)))
    (hG_bound : ∀ t, ‖G t‖ ≤ Real.sqrt Kmax * r_norm t)
    {T : ℝ} (hT : 0 ≤ T) :
    ‖θ T - θ 0‖ ≤
      Real.sqrt Kmax * (2 * r0_norm / ρ) * (1 - Real.exp (-(ρ * T / 2))) := by
  -- Deduce the shape required by `movement_from_residual_decay`.
  have h_sqrtKmax_nn : 0 ≤ Real.sqrt Kmax := Real.sqrt_nonneg _
  have hG_bound' : ∀ t,
      ‖G t‖ ≤ Real.sqrt Kmax * (r0_norm * Real.exp (-(ρ * t / 2))) := by
    intro t
    calc ‖G t‖
        ≤ Real.sqrt Kmax * r_norm t := hG_bound t
      _ ≤ Real.sqrt Kmax * (r0_norm * Real.exp (-(ρ * t / 2))) :=
          mul_le_mul_of_nonneg_left (hr_decay t) h_sqrtKmax_nn
  exact movement_from_residual_decay θ hθ_diff G hθ_ODE Kmax hKmax
    r0_norm hr0_nn hρ_pos hG_bound' hT

/-! ## Width-independent movement bound (headline) -/

/-- **Width-independent movement bound (uniform-in-`T` form).**

Same hypotheses as `ntk_movement_bound_from_carrier`. The conclusion
drops the exponentially-shrinking remainder factor
`(1 - exp(-ρT/2)) ≤ 1` to obtain the clean uniform bound

    `‖θ(T) - θ(0)‖ ≤ 2 √Kmax · r0_norm / ρ`.

**Key feature.** The right-hand side depends only on `Kmax`,
`r0_norm := ‖r(0)‖`, and `ρ` — all width-independent in the standard
NTK lazy-training analysis. In particular it does not depend on the
network width `m` (which is embedded in the underlying `Param d m`
type but does not appear in the movement bound).

This is the substrate carrier of the Chizat-Bach `1/√p` theorem: the
movement stays bounded uniformly in `p`; the Hessian shrinks as
`O(1/√p)`; multiplying gives the `O(R² / √p) = O(1/√p)` Taylor
remainder. -/
theorem gradient_flow_movement_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (θ : ℝ → E)
    (hθ_diff : Differentiable ℝ θ)
    (G : ℝ → E)
    (hθ_ODE : ∀ t, deriv θ t = -G t)
    (Kmax : ℝ) (hKmax : 0 ≤ Kmax)
    (r_norm : ℝ → ℝ)
    (r0_norm : ℝ) (hr0_nn : 0 ≤ r0_norm)
    {ρ : ℝ} (hρ_pos : 0 < ρ)
    (hr_decay : ∀ t, r_norm t ≤ r0_norm * Real.exp (-(ρ * t / 2)))
    (hG_bound : ∀ t, ‖G t‖ ≤ Real.sqrt Kmax * r_norm t)
    {T : ℝ} (hT : 0 ≤ T) :
    ‖θ T - θ 0‖ ≤ 2 * Real.sqrt Kmax * r0_norm / ρ := by
  have h_tight := ntk_movement_bound_from_carrier
    θ hθ_diff G hθ_ODE Kmax hKmax r_norm r0_norm hr0_nn
    hρ_pos hr_decay hG_bound hT
  -- Bound the fencing RHS by dropping `(1 - exp(-ρT/2)) ≤ 1`.
  have h_exp_le : Real.exp (-(ρ * T / 2)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    -- Need `-(ρ * T / 2) ≤ 0`, i.e. `0 ≤ ρ * T / 2`.
    have : 0 ≤ ρ * T := mul_nonneg hρ_pos.le hT
    linarith
  have h_exp_pos : 0 < Real.exp (-(ρ * T / 2)) := Real.exp_pos _
  have h_one_sub_le : 1 - Real.exp (-(ρ * T / 2)) ≤ 1 := by linarith
  have h_one_sub_nn : 0 ≤ 1 - Real.exp (-(ρ * T / 2)) := by
    -- exp ≤ 1 so 1 - exp ≥ 0.
    linarith
  have h_pref_nn : 0 ≤ Real.sqrt Kmax * (2 * r0_norm / ρ) := by
    apply mul_nonneg (Real.sqrt_nonneg _)
    exact div_nonneg (by linarith) hρ_pos.le
  have h_drop :
      Real.sqrt Kmax * (2 * r0_norm / ρ) * (1 - Real.exp (-(ρ * T / 2)))
        ≤ Real.sqrt Kmax * (2 * r0_norm / ρ) := by
    calc Real.sqrt Kmax * (2 * r0_norm / ρ) * (1 - Real.exp (-(ρ * T / 2)))
        ≤ Real.sqrt Kmax * (2 * r0_norm / ρ) * 1 :=
          mul_le_mul_of_nonneg_left h_one_sub_le h_pref_nn
      _ = Real.sqrt Kmax * (2 * r0_norm / ρ) := by ring
  have h_final_eq :
      Real.sqrt Kmax * (2 * r0_norm / ρ)
        = 2 * Real.sqrt Kmax * r0_norm / ρ := by
    ring
  calc ‖θ T - θ 0‖
      ≤ Real.sqrt Kmax * (2 * r0_norm / ρ) *
          (1 - Real.exp (-(ρ * T / 2))) := h_tight
    _ ≤ Real.sqrt Kmax * (2 * r0_norm / ρ) := h_drop
    _ = 2 * Real.sqrt Kmax * r0_norm / ρ := h_final_eq

/-- **Width-independent movement bound (witness form).**

Package the movement bound as an explicit existential in the
width-independent radius

    `R := 2 √Kmax · ‖r(0)‖ / ρ`.

The right-hand side depends only on `Kmax`, `r0_norm`, and `ρ` — no
width variable appears in the expression. Under the standard NTK
lazy-training analysis all three of `Kmax`, `‖r(0)‖`, `ρ` are
width-independent, so `R` is a width-independent constant that
uniformly bounds `‖θ(T) - θ(0)‖` for every `T ≥ 0`.

This is the shape consumed downstream by the Chizat-Bach `1/√p`
Taylor-remainder argument (Phase 2c): multiplied by the `L₀ / √m`
Hessian bound from Phase 2a, it yields the `O(1/√m)` linearization
error. -/
theorem gradient_flow_movement_bounded_width_independent
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (θ : ℝ → E)
    (hθ_diff : Differentiable ℝ θ)
    (G : ℝ → E)
    (hθ_ODE : ∀ t, deriv θ t = -G t)
    (Kmax : ℝ) (hKmax : 0 ≤ Kmax)
    (r_norm : ℝ → ℝ)
    (r0_norm : ℝ) (hr0_nn : 0 ≤ r0_norm)
    {ρ : ℝ} (hρ_pos : 0 < ρ)
    (hr_decay : ∀ t, r_norm t ≤ r0_norm * Real.exp (-(ρ * t / 2)))
    (hG_bound : ∀ t, ‖G t‖ ≤ Real.sqrt Kmax * r_norm t) :
    ∃ R : ℝ,
      R = 2 * Real.sqrt Kmax * r0_norm / ρ ∧
      0 ≤ R ∧
      ∀ T : ℝ, 0 ≤ T → ‖θ T - θ 0‖ ≤ R := by
  refine ⟨2 * Real.sqrt Kmax * r0_norm / ρ, rfl, ?_, ?_⟩
  · -- 0 ≤ R.
    have h1 : 0 ≤ 2 * Real.sqrt Kmax * r0_norm := by
      have := Real.sqrt_nonneg Kmax
      positivity
    exact div_nonneg h1 hρ_pos.le
  · intro T hT
    exact gradient_flow_movement_bounded θ hθ_diff G hθ_ODE Kmax hKmax
      r_norm r0_norm hr0_nn hρ_pos hr_decay hG_bound hT

/-! ## End-to-end composition with the residual decay carrier

The next two results glue `gradient_flow_movement_bounded` to
`LTFP.ntk_lazy_training_carrier_parametric` via the square-root step
`ntk_residual_norm_decay_from_sq_decay`. The user supplies the ODE
relation and the coercivity/drift hypotheses; the movement bound
follows deterministically. -/

/-- **Movement bound from `‖r‖²` residual decay hypothesis.**

Same conclusion as `gradient_flow_movement_bounded` but the residual
decay is supplied in the `‖r(t)‖² ≤ ‖r(0)‖² · exp(-ρt)` form directly
produced by `ntk_lazy_training_carrier_parametric`. The theorem
converts this to the `‖r(t)‖ ≤ ‖r(0)‖ · exp(-ρt/2)` form internally
via `ntk_residual_norm_decay_from_sq_decay`. -/
theorem gradient_flow_movement_bounded_from_sq_decay
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (θ : ℝ → E)
    (hθ_diff : Differentiable ℝ θ)
    (G : ℝ → E)
    (hθ_ODE : ∀ t, deriv θ t = -G t)
    (Kmax : ℝ) (hKmax : 0 ≤ Kmax)
    (r_norm : ℝ → ℝ) (hr_nn : ∀ t, 0 ≤ r_norm t)
    (r0_norm : ℝ) (hr0_nn : 0 ≤ r0_norm)
    {ρ : ℝ} (hρ_pos : 0 < ρ)
    (hr_sq_decay : ∀ t, r_norm t ^ 2 ≤ r0_norm ^ 2 * Real.exp (-(ρ * t)))
    (hG_bound : ∀ t, ‖G t‖ ≤ Real.sqrt Kmax * r_norm t)
    {T : ℝ} (hT : 0 ≤ T) :
    ‖θ T - θ 0‖ ≤ 2 * Real.sqrt Kmax * r0_norm / ρ := by
  -- Convert the `‖r‖²`-shape decay to the `‖r‖`-shape decay pointwise.
  have hr_decay : ∀ t, r_norm t ≤ r0_norm * Real.exp (-(ρ * t / 2)) := by
    intro t
    exact ntk_residual_norm_decay_from_sq_decay hr0_nn hρ_pos (hr_nn t) t
      (hr_sq_decay t)
  exact gradient_flow_movement_bounded θ hθ_diff G hθ_ODE Kmax hKmax
    r_norm r0_norm hr0_nn hρ_pos hr_decay hG_bound hT

end LTFP.MathlibExt.Probability
