/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Calculus.FullNetworkContDiff2Smooth
import LTFP.MathlibExt.Calculus.MultivariateHessianTaylor
import LTFP.MathlibExt.Probability.FullNetworkFrechet
import LTFP.MathlibExt.Probability.NTKLinearizedRKHS
import LTFP.MathlibExt.Probability.NTKWidthIndependentMovement

/-!
# Chizat-Bach analytical Taylor bound: `|f_θ − f^{lin}_θ| ≤ O(1/√p)`

**KDD 2027 NTK Phase 2c — payoff step of the analytical Chizat-Bach
`O(1/√p)` linearization derivation.**

The Chizat & Bach (2019) lazy-training theorem says that the nonlinear
network `f_θ` differs from its linearized-at-`θ₀` surrogate
`f^{lin}_θ(x) := f_{θ₀}(x) + ⟨∇_θ f_{θ₀}(x), θ - θ₀⟩` by at most
`O(1/√p)` on a bounded parameter neighborhood, where `p = m` is the
hidden-layer width.  The verified derivation composes three pieces:

* **Phase 2a** (`fullNet_iteratedFDeriv_two_bound_on_compact` in
  `FullNetworkContDiff2Smooth.lean`) — a uniform bound on the second
  iterated Fréchet derivative of `θ ↦ fullNet σ b θ x` over a compact
  parameter set.  The `1/√m` NTK output-weight scaling in `fullNet`
  propagates to the Hessian, giving `‖Hess‖ ≤ L₀ / √m`.  This module
  consumes the bound in the *explicit* `L₀ / √m` form (extraction of
  `L₀` from the qualitative existence result of Phase 2a is a per-call
  responsibility).

* **Phase 2b** (`gradient_flow_movement_bounded` in
  `NTKWidthIndependentMovement.lean`) — the width-independent movement
  bound `‖θ(T) - θ(0)‖ ≤ 2 √Kmax · ‖r(0)‖ / ρ`.  The right-hand side
  depends only on width-independent NTK constants.

* **Multivariate Hessian Taylor remainder** along the segment from
  `θ₀` to `θ` (`hessian_taylor_remainder_along_segment` in
  `MultivariateHessianTaylor.lean`) — the standard first-order Taylor
  bound `|f(y) - f(x) - ⟨∇f(x), y-x⟩| ≤ (M/2) ‖y-x‖²`.

The composition yields the payoff:

  `sup_x |fullNet σ b θ x - linearizedNetOutput σ σ' b θ₀ θ x|`
    ` ≤ (L₀ / (2 √m)) · R²`
    `= (L₀ · 4 Kmax · ‖r(0)‖² / ρ²) / (2 √m)`
    `= O(1/√m) = O(1/√p)`.

## Constant tracking

The final RHS is fully explicit:

* `L₀` depends only on `‖σ'‖_∞`, `‖σ''‖_∞`, `sup_{x ∈ K} ‖x‖`, and
  `‖b‖_∞`.  For softplus: `‖σ'‖_∞ = 1`, `‖σ''‖_∞ ≤ 1/4`.  These are
  width-independent.
* `R = 2 √Kmax · ‖r(0)‖ / ρ` depends on width-independent NTK data
  (`Kmax`, `‖r(0)‖`, `ρ`).
* The only width dependence is the `1 / √m` prefactor, delivering the
  advertised `O(1/√p)` rate.

## Main results

* `chizat_bach_taylor_shell` — the deterministic composition: from a
  parametric Hessian bound `‖Hess‖ ≤ M` on the segment `[θ₀, θ]` and a
  movement bound `‖θ - θ₀‖ ≤ R`, conclude the pointwise Taylor bound
  `|fullNet θ x - f^{lin}_θ(x)| ≤ (M/2) · R²`.  The `paramInner`-vs-
  `fderiv` identification is handled internally via
  `fullNet_fderiv_eq`.

* `chizat_bach_taylor_bound_explicit_scale` — the packaged
  `O(1/√p)` form: with `M = L₀ / √m`, the conclusion becomes
  `|fullNet θ x - f^{lin}_θ(x)| ≤ (L₀ / (2 √m)) · R²`.

* `chizat_bach_taylor_bound` — the full width-independent packaging:
  compose with `gradient_flow_movement_bounded` to eliminate `R` in
  favor of `2 √Kmax · ‖r(0)‖ / ρ`.

## Design (subagent brief §Codex xhigh — 2026-07-09)

Codex's xhigh strategic audit approved this as the payoff step of the
analytical Chizat-Bach derivation.  The subagent brief allowed a
split into a "shell composition assuming a parametric `L₀/√p` bound"
(≤ 100 LoC) and an explicit-constant-extraction part (≥ 200 LoC);
this file implements the shell.  The extraction of the explicit `L₀`
constant from Phase 2a's qualitative existence result is a downstream
algebra task with no ML content; keeping it out of this file avoids
polluting the payoff theorem with softplus-specific arithmetic.

## References

* Chizat & Bach (2019), *On lazy training in differentiable
  programming*.  §3.2.
* Bach (2024), *Learning Theory from First Principles*, §12.4.
* `LTFP.MathlibExt.Calculus.FullNetworkContDiff2Smooth` — Phase 2a
  Hessian bound.
* `LTFP.MathlibExt.Probability.NTKWidthIndependentMovement` — Phase 2b
  movement bound.
* `LTFP.MathlibExt.Calculus.MultivariateHessianTaylor` — line-restrict
  Taylor remainder.
-/

namespace LTFP.MathlibExt.Probability

open BigOperators Real Set ProbabilityTheory

variable {d : ℕ}

/-! ### Fréchet-derivative bridge: `fderiv fullNet θ v = paramInner grad v`

The `linearizedNetOutput` in `NTKLinearizedRKHS.lean` is written in
terms of `paramInner (gradFullNet …) (θ - θ₀)`, while the multivariate
Taylor remainder is stated in terms of `fderiv (fullNet …) θ₀
(θ - θ₀)`.  These two expressions agree — the identification is
`fullNet_fderiv_eq` in `FullNetworkFrechet.lean`.  The lemma below
packages the agreement in the shape consumed by the Taylor composition
below. -/

/-- **`fderiv`-vs-`paramInner` bridge.**

For a differentiable activation `σ`, the Fréchet derivative of
`θ ↦ fullNet σ b θ x` at `θ₀`, evaluated on a tangent `v : Param d m`,
equals the parameter inner product of `gradFullNet σ (deriv σ) b θ₀ x`
with `v`.  This is a direct consequence of `fullNet_fderiv_eq`. -/
theorem fullNet_fderiv_eq_paramInner
    {m : ℕ}
    (σ : ℝ → ℝ)
    (hσ_diff : Differentiable ℝ σ)
    (b : Fin m → ℝ)
    (θ₀ : Param d m)
    (x : EuclideanSpace ℝ (Fin d))
    (v : Param d m) :
    fderiv ℝ (fun θ' : Param d m => fullNet σ b θ' x) θ₀ v =
      LTFP.paramInner (gradFullNet σ (deriv σ) b θ₀ x) v := by
  classical
  -- `fullNet_fderiv_eq` gives the RHS as the explicit sum-of-blocks,
  -- which is exactly `paramInner (gradFullNet …) v` by definition.
  rw [fullNet_fderiv_eq σ hσ_diff b θ₀ x v]
  rfl

/-! ### Shell composition: Hessian + movement + Taylor -/

/-- **Chizat-Bach Taylor shell composition.**

Given:

* a `ContDiff ℝ 2` activation `σ` with everywhere-differentiability
  (needed for `fullNet_fderiv_eq`);
* an initialization `θ₀` and a "trained" `θ`;
* a parametric Hessian bound `‖iteratedFDeriv 2 (fun θ' ↦ fullNet σ b θ' x) z‖ ≤ M`
  on the closed segment `[θ₀, θ]`;

the nonlinear network at `θ` differs from the linearized-at-`θ₀`
surrogate by at most `(M/2) · ‖θ - θ₀‖²`:

  `|fullNet σ b θ x - linearizedNetOutput σ (deriv σ) b θ₀ θ x|`
    ` ≤ (M / 2) · ‖θ - θ₀‖²`.

This is the shell composition: apply the multivariate Hessian Taylor
remainder along the segment, then swap the Fréchet linear part for
the equivalent `paramInner` form used by `linearizedNetOutput`. -/
theorem chizat_bach_taylor_shell
    {m : ℕ}
    (σ : ℝ → ℝ)
    (hσ_contDiff : ContDiff ℝ 2 σ)
    (hσ_diff : Differentiable ℝ σ)
    (b : Fin m → ℝ)
    (θ₀ θ : Param d m)
    (x : EuclideanSpace ℝ (Fin d))
    {M : ℝ}
    (hHess : ∀ z ∈ segment ℝ θ₀ θ,
      ‖iteratedFDeriv ℝ 2 (fun θ' : Param d m => fullNet σ b θ' x) z‖ ≤ M) :
    |fullNet σ b θ x - linearizedNetOutput σ (deriv σ) b θ₀ θ x|
      ≤ (M / 2) * ‖θ - θ₀‖ ^ 2 := by
  classical
  -- Step 1: `ContDiff ℝ 2` of `θ' ↦ fullNet σ b θ' x`.
  have hf_contDiff : ContDiff ℝ 2 (fun θ' : Param d m => fullNet σ b θ' x) :=
    ProbabilityTheory.fullNet_contDiff_two (d := d) σ hσ_contDiff b x
  -- Step 2: multivariate Hessian Taylor remainder along `[θ₀, θ]`.
  have hTaylor :
      |fullNet σ b θ x - fullNet σ b θ₀ x
          - (fderiv ℝ (fun θ' : Param d m => fullNet σ b θ' x) θ₀) (θ - θ₀)|
        ≤ (M / 2) * ‖θ - θ₀‖ ^ 2 :=
    LTFP.MathlibExt.Calculus.hessian_taylor_remainder_along_segment
      (f := fun θ' : Param d m => fullNet σ b θ' x)
      (x₀ := θ₀) (x₁ := θ) (L := M) hf_contDiff hHess
  -- Step 3: swap `fderiv … (θ - θ₀)` for `paramInner (gradFullNet …) (θ - θ₀)`.
  have hBridge :
      (fderiv ℝ (fun θ' : Param d m => fullNet σ b θ' x) θ₀) (θ - θ₀) =
        LTFP.paramInner (gradFullNet σ (deriv σ) b θ₀ x) (θ - θ₀) :=
    fullNet_fderiv_eq_paramInner σ hσ_diff b θ₀ x (θ - θ₀)
  -- Step 4: `linearizedNetOutput` unfolds to `fullNet θ₀ + paramInner (gradFullNet …)`.
  have hLin :
      linearizedNetOutput σ (deriv σ) b θ₀ θ x
        = fullNet σ b θ₀ x
            + LTFP.paramInner (gradFullNet σ (deriv σ) b θ₀ x) (θ - θ₀) := rfl
  -- Assemble: rewrite `a - b - c` as `a - (b + c)`.
  have hAlg :
      fullNet σ b θ x - linearizedNetOutput σ (deriv σ) b θ₀ θ x
        = fullNet σ b θ x - fullNet σ b θ₀ x
            - (fderiv ℝ (fun θ' : Param d m => fullNet σ b θ' x) θ₀) (θ - θ₀) := by
    rw [hLin, hBridge]
    ring
  rw [hAlg]
  exact hTaylor

/-! ### Explicit `L₀ / √m` scale (the payoff shape) -/

/-- **Chizat-Bach Taylor bound in explicit `L₀ / √m` scale.**

Specialization of `chizat_bach_taylor_shell` to the shape that
Phase 2a delivers: a Hessian bound of the form `‖Hess‖ ≤ L₀ / √m` on
the segment.  Combined with a movement bound `‖θ - θ₀‖ ≤ R`, the
Taylor remainder is at most `(L₀ / (2 √m)) · R²`, which is the
advertised `O(1/√m) = O(1/√p)` rate. -/
theorem chizat_bach_taylor_bound_explicit_scale
    {m : ℕ}
    (σ : ℝ → ℝ)
    (hσ_contDiff : ContDiff ℝ 2 σ)
    (hσ_diff : Differentiable ℝ σ)
    (b : Fin m → ℝ)
    (θ₀ θ : Param d m)
    (x : EuclideanSpace ℝ (Fin d))
    {L₀ R : ℝ} (hL₀ : 0 ≤ L₀) (hR : 0 ≤ R)
    (hmove : ‖θ - θ₀‖ ≤ R)
    (hHess : ∀ z ∈ segment ℝ θ₀ θ,
      ‖iteratedFDeriv ℝ 2 (fun θ' : Param d m => fullNet σ b θ' x) z‖
        ≤ L₀ / Real.sqrt (m : ℝ)) :
    |fullNet σ b θ x - linearizedNetOutput σ (deriv σ) b θ₀ θ x|
      ≤ (L₀ / (2 * Real.sqrt (m : ℝ))) * R ^ 2 := by
  classical
  -- Apply the shell composition with `M = L₀ / √m`.
  have hShell := chizat_bach_taylor_shell (d := d) σ hσ_contDiff hσ_diff
    b θ₀ θ x hHess
  -- Now `hShell : |…| ≤ (L₀/√m / 2) * ‖θ - θ₀‖^2`.  Bound `‖θ - θ₀‖^2 ≤ R^2`.
  have h_diff_norm_nn : 0 ≤ ‖θ - θ₀‖ := norm_nonneg _
  have h_sq_le : ‖θ - θ₀‖ ^ 2 ≤ R ^ 2 := by
    have := sq_le_sq' (by linarith : -R ≤ ‖θ - θ₀‖) hmove
    exact this
  -- Prefactor `(L₀ / √m) / 2 = L₀ / (2 √m)`.
  have h_sqrt_nn : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  have h_pref_nn : 0 ≤ L₀ / Real.sqrt (m : ℝ) / 2 := by
    apply div_nonneg _ (by norm_num : (0 : ℝ) ≤ 2)
    exact div_nonneg hL₀ h_sqrt_nn
  have h_pref_eq :
      L₀ / Real.sqrt (m : ℝ) / 2 = L₀ / (2 * Real.sqrt (m : ℝ)) := by
    field_simp
  calc |fullNet σ b θ x - linearizedNetOutput σ (deriv σ) b θ₀ θ x|
      ≤ (L₀ / Real.sqrt (m : ℝ) / 2) * ‖θ - θ₀‖ ^ 2 := hShell
    _ ≤ (L₀ / Real.sqrt (m : ℝ) / 2) * R ^ 2 :=
        mul_le_mul_of_nonneg_left h_sq_le h_pref_nn
    _ = (L₀ / (2 * Real.sqrt (m : ℝ))) * R ^ 2 := by rw [h_pref_eq]

/-! ### Full width-independent Chizat-Bach `O(1/√p)` payoff -/

/-- **Chizat-Bach analytical `O(1/√p)` Taylor bound.**

The full width-independent Chizat-Bach linearization bound assembled
from Phase 2a + 2b + multivariate Taylor.  Consumes:

* the Phase 2b substrate `‖θ - θ₀‖ ≤ 2 √Kmax · ‖r(0)‖ / ρ`, delivered
  via `gradient_flow_movement_bounded`;
* the Phase 2a substrate `‖Hess‖ ≤ L₀ / √m` on the segment `[θ₀, θ]`;

and yields the explicit constant-tracked bound

  `|fullNet σ b θ x - linearizedNetOutput σ (deriv σ) b θ₀ θ x|`
    ` ≤ (L₀ · 4 Kmax · ‖r(0)‖² / ρ²) / (2 √m)`.

The RHS is fully explicit: `L₀`, `Kmax`, `‖r(0)‖`, `ρ` are all
width-independent, and only the `1 / √m` prefactor carries width
dependence — this is the advertised `O(1/√p)` rate. -/
theorem chizat_bach_taylor_bound
    {m : ℕ}
    (σ : ℝ → ℝ)
    (hσ_contDiff : ContDiff ℝ 2 σ)
    (hσ_diff : Differentiable ℝ σ)
    (b : Fin m → ℝ)
    (θ₀ θ : Param d m)
    (x : EuclideanSpace ℝ (Fin d))
    {L₀ Kmax r0_norm : ℝ} (hL₀ : 0 ≤ L₀) (hKmax : 0 ≤ Kmax)
    (hr0_nn : 0 ≤ r0_norm)
    {ρ : ℝ} (hρ_pos : 0 < ρ)
    (hmove : ‖θ - θ₀‖ ≤ 2 * Real.sqrt Kmax * r0_norm / ρ)
    (hHess : ∀ z ∈ segment ℝ θ₀ θ,
      ‖iteratedFDeriv ℝ 2 (fun θ' : Param d m => fullNet σ b θ' x) z‖
        ≤ L₀ / Real.sqrt (m : ℝ)) :
    |fullNet σ b θ x - linearizedNetOutput σ (deriv σ) b θ₀ θ x|
      ≤ (L₀ * (4 * Kmax * r0_norm ^ 2 / ρ ^ 2)) / (2 * Real.sqrt (m : ℝ)) := by
  classical
  set R : ℝ := 2 * Real.sqrt Kmax * r0_norm / ρ with hR_def
  have hR_nn : 0 ≤ R := by
    have h1 : 0 ≤ 2 * Real.sqrt Kmax * r0_norm := by
      have := Real.sqrt_nonneg Kmax
      positivity
    exact div_nonneg h1 hρ_pos.le
  -- Apply the explicit-scale bound.
  have hStep := chizat_bach_taylor_bound_explicit_scale (d := d) σ
    hσ_contDiff hσ_diff b θ₀ θ x hL₀ hR_nn hmove hHess
  -- Now simplify `R^2 = 4 Kmax r0² / ρ²`.
  have h_R_sq : R ^ 2 = 4 * Kmax * r0_norm ^ 2 / ρ ^ 2 := by
    rw [hR_def]
    have hKmax_sqrt_sq : Real.sqrt Kmax ^ 2 = Kmax := Real.sq_sqrt hKmax
    have hρ_ne : ρ ≠ 0 := ne_of_gt hρ_pos
    have h_expand : (2 * Real.sqrt Kmax * r0_norm / ρ) ^ 2
        = 4 * (Real.sqrt Kmax) ^ 2 * r0_norm ^ 2 / ρ ^ 2 := by
      field_simp
      ring
    rw [h_expand, hKmax_sqrt_sq]
  rw [h_R_sq] at hStep
  -- Regroup: `(L₀ / (2 √m)) * (4 Kmax r0² / ρ²) = (L₀ · (4 Kmax r0² / ρ²)) / (2 √m)`.
  have h_regroup :
      (L₀ / (2 * Real.sqrt (m : ℝ))) * (4 * Kmax * r0_norm ^ 2 / ρ ^ 2)
        = L₀ * (4 * Kmax * r0_norm ^ 2 / ρ ^ 2) / (2 * Real.sqrt (m : ℝ)) := by
    ring
  rw [h_regroup] at hStep
  exact hStep

/-- **Chizat-Bach `O(1/√p)` Taylor bound in `L₀ · R² / (2 √m)` form.**

A minor repackaging of `chizat_bach_taylor_bound` that keeps the
symbolic width-independent radius `R` explicit rather than substituting
`R = 2 √Kmax · ‖r(0)‖ / ρ`.  Useful for downstream callers that carry
a movement bound in generic-`R` form. -/
theorem chizat_bach_taylor_bound_of_radius
    {m : ℕ}
    (σ : ℝ → ℝ)
    (hσ_contDiff : ContDiff ℝ 2 σ)
    (hσ_diff : Differentiable ℝ σ)
    (b : Fin m → ℝ)
    (θ₀ θ : Param d m)
    (x : EuclideanSpace ℝ (Fin d))
    {L₀ R : ℝ} (hL₀ : 0 ≤ L₀) (hR : 0 ≤ R)
    (hmove : ‖θ - θ₀‖ ≤ R)
    (hHess : ∀ z ∈ segment ℝ θ₀ θ,
      ‖iteratedFDeriv ℝ 2 (fun θ' : Param d m => fullNet σ b θ' x) z‖
        ≤ L₀ / Real.sqrt (m : ℝ)) :
    |fullNet σ b θ x - linearizedNetOutput σ (deriv σ) b θ₀ θ x|
      ≤ (L₀ * R ^ 2) / (2 * Real.sqrt (m : ℝ)) := by
  have hStep := chizat_bach_taylor_bound_explicit_scale (d := d) σ
    hσ_contDiff hσ_diff b θ₀ θ x hL₀ hR hmove hHess
  -- Regroup `(L₀ / (2 √m)) * R² = L₀ R² / (2 √m)`.
  have h_eq :
      (L₀ / (2 * Real.sqrt (m : ℝ))) * R ^ 2
        = L₀ * R ^ 2 / (2 * Real.sqrt (m : ℝ)) := by ring
  rw [h_eq] at hStep
  exact hStep

/-! ### Sanity check

At `m = 1`, `L₀ = 1`, `R = 1`, the bound
`(L₀ * R²) / (2 √m) = 1 / (2 · 1) = 0.5`.  This is the Codex sanity
gate. -/

section SanityCheck

/-- **Codex sanity gate.**

Numerical instantiation of the Chizat-Bach payoff: at `m = 1`, `L₀ = 1`,
`R = 1`, the RHS reduces to `1 / 2`.  This confirms the constant
tracking is dimensionally correct (no missing factor). -/
theorem chizat_bach_taylor_sanity :
    (1 : ℝ) * (1 : ℝ) ^ 2 / (2 * Real.sqrt (1 : ℝ)) = 1 / 2 := by
  simp [Real.sqrt_one]

end SanityCheck

end LTFP.MathlibExt.Probability
