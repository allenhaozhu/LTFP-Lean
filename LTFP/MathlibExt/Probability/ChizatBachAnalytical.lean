/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.ChizatBachTaylorScale
import LTFP.MathlibExt.Probability.NTKChizatBachShell

/-!
# Analytical Chizat-Bach `O(1/√p)` NTK kernel-expansion theorem (T6c-nonlin)

**KDD 2027 NTK Phase 2d — payoff step of the analytical Chizat-Bach
composition into the T6c-nonlin parametric shell.**

The `NTKChizatBachShell` module ships a *parametric* T6c-nonlin theorem
`ntk_network_approx_kernel_expansion`: given a bare Chizat-Bach constant
`C ≥ 0` (packaged as `ChizatBachBound σ σ' b θ₀ θ C`) and the finite-span
hypothesis of T6c-lin, the nonlinear network is uniformly within `C` of
the empirical-NTK kernel-expansion predictor.

The `ChizatBachTaylorScale` module (Phase 2c payoff) delivers the
*analytical* Chizat-Bach constant `C = L₀ · R² / (2 √m) = O(1/√m)` for
smooth activations `σ ∈ C²`, with `R = 2 √Kmax · ‖r(0)‖ / ρ`
(width-independent, from Phase 2b) and `L₀` the segment Hessian scale
(from Phase 2a).

This module composes the two: it produces the fully-analytical
`O(1/√p)` NTK kernel-expansion approximation theorem for a smooth
nonlinear network in the lazy regime, closing the Option-C campaign.
Concretely, for a `ContDiff ℝ 2` activation `σ` and a parameter update
`θ - θ₀` in the finite-dim RKHS span, there exist expansion coefficients
`α : Fin n → ℝ` such that

  `sup_x |fullNet σ b θ x
            - (fullNet σ b θ₀ x + ∑ i, α i · K_NTK(x, x_i))|`
    ` ≤ (L₀ · 4 Kmax · ‖r(0)‖² / ρ²) / (2 √m)`
    `= O(1/√p)`.

## Contents

* `ChizatBachBound.ofAnalytical` — constructs a `ChizatBachBound`
  witness with the explicit analytical `O(1/√m)` constant, feeding the
  Phase 2c Taylor bound into the shell's parametric interface.

* `ntk_network_approx_kernel_expansion_analytical` — the payoff
  theorem: smooth-activation, span-membership, Hessian-scale, and
  movement-radius hypotheses combine into the fully-analytical
  `O(1/√p)` kernel-expansion approximation.

* `ntk_network_approx_kernel_expansion_analytical_of_radius` — a
  generic-radius repackaging that keeps the movement radius `R`
  symbolic rather than substituting `R = 2 √Kmax · ‖r(0)‖ / ρ`.  Useful
  for downstream callers carrying a movement bound in the `‖θ - θ₀‖ ≤ R`
  shape.

## Composition sketch

1. From `h_span : θ - θ₀ ∈ Submodule.span ℝ (range ∇_θ f_{θ₀}(x_·))`,
   T6c-lin (`ntk_linearized_model_in_finite_rkhs`) produces `α : Fin n → ℝ`
   with `linearizedNetOutput σ (deriv σ) b θ₀ θ x - fullNet σ b θ₀ x =
   ∑ i, α i · paramNTKKernel σ (deriv σ) b θ₀ x (xs i)`.

2. From `hHess` and `hmove`, Phase 2c
   (`chizat_bach_taylor_bound`) produces the analytical Chizat-Bach
   inequality
   `|fullNet σ b θ x - linearizedNetOutput σ (deriv σ) b θ₀ θ x|
     ≤ (L₀ · 4 Kmax · ‖r(0)‖² / ρ²) / (2 √m)`.

3. Substitute step 1's kernel-expansion identity into step 2's
   absolute-difference bound; the LHS becomes
   `|fullNet σ b θ x - (fullNet σ b θ₀ x
     + ∑ i, α i · paramNTKKernel σ (deriv σ) b θ₀ x (xs i))|`.

This composition never introduces a new `sorry` / `axiom`; all pieces
are verified in the substrate modules cited above.

## Sanity gate (Codex xhigh, 2026-07-09)

At `L₀ = Kmax = ‖r(0)‖ = ρ = m = 1`, the bound RHS reduces to
`1 · 4 · 1 · 1 / 1 / (2 · 1) = 2`.  A `#eval` of the closed-form
constant confirms the arithmetic.

## References

* Chizat & Bach (2019) *On lazy training in differentiable programming*,
  NeurIPS.
* Bach (2024) *Learning Theory from First Principles*, §12.4.
* `LTFP.MathlibExt.Probability.ChizatBachTaylorScale` — Phase 2c payoff.
* `LTFP.MathlibExt.Probability.NTKChizatBachShell` — T6c-nonlin
  parametric shell.
* `LTFP.MathlibExt.Probability.NTKLinearizedRKHS` — T6c-lin kernel
  expansion.
-/

namespace LTFP.MathlibExt.Probability

open BigOperators Real Set ProbabilityTheory
open LTFP

variable {d : ℕ}

/-! ### Analytical `ChizatBachBound` witness -/

/-- **Analytical Chizat-Bach witness with explicit `O(1/√m)` constant.**

Constructs an instance of the parametric `ChizatBachBound` structure
using the Phase 2c analytical Taylor bound.  The resulting constant is

  `C = L₀ · (4 · Kmax · ‖r(0)‖² / ρ²) / (2 · √m)`

which is the fully-explicit width-independent-times-`1/√m` form of
Chizat & Bach (2019).

This construction is the "closes the shell hypothesis" step: any
downstream caller of `ntk_network_approx_kernel_expansion` who has the
Phase 2a Hessian bound and the Phase 2b movement bound in hand can
feed the resulting `ChizatBachBound` witness into the shell without
having to reprove the analytical `O(1/√m)` scaling. -/
theorem chizatBachBound_ofAnalytical
    {m : ℕ}
    (σ : ℝ → ℝ)
    (hσ_contDiff : ContDiff ℝ 2 σ)
    (hσ_diff : Differentiable ℝ σ)
    (b : Fin m → ℝ)
    (θ₀ θ : Param d m)
    {L₀ Kmax r0_norm : ℝ} (hL₀ : 0 ≤ L₀) (hKmax : 0 ≤ Kmax)
    (hr0_nn : 0 ≤ r0_norm)
    {ρ : ℝ} (hρ_pos : 0 < ρ)
    (hmove : ‖θ - θ₀‖ ≤ 2 * Real.sqrt Kmax * r0_norm / ρ)
    (hHess : ∀ x : EuclideanSpace ℝ (Fin d),
      ∀ z ∈ segment ℝ θ₀ θ,
        ‖iteratedFDeriv ℝ 2 (fun θ' : Param d m => fullNet σ b θ' x) z‖
          ≤ L₀ / Real.sqrt (m : ℝ)) :
    ChizatBachBound σ (deriv σ) b θ₀ θ
      ((L₀ * (4 * Kmax * r0_norm ^ 2 / ρ ^ 2)) / (2 * Real.sqrt (m : ℝ))) :=
  ⟨fun x =>
    chizat_bach_taylor_bound (d := d) σ hσ_contDiff hσ_diff b θ₀ θ x
      hL₀ hKmax hr0_nn hρ_pos hmove (hHess x)⟩

/-- **Generic-radius analytical Chizat-Bach witness.**

Same shape as `chizatBachBound_ofAnalytical` but keeps the movement
radius `R` symbolic rather than substituting `R = 2 √Kmax · ‖r(0)‖ / ρ`.
Useful for downstream callers carrying a movement bound in generic-`R`
form (e.g., from an alternative width-independent movement lemma). -/
theorem chizatBachBound_ofAnalytical_of_radius
    {m : ℕ}
    (σ : ℝ → ℝ)
    (hσ_contDiff : ContDiff ℝ 2 σ)
    (hσ_diff : Differentiable ℝ σ)
    (b : Fin m → ℝ)
    (θ₀ θ : Param d m)
    {L₀ R : ℝ} (hL₀ : 0 ≤ L₀) (hR : 0 ≤ R)
    (hmove : ‖θ - θ₀‖ ≤ R)
    (hHess : ∀ x : EuclideanSpace ℝ (Fin d),
      ∀ z ∈ segment ℝ θ₀ θ,
        ‖iteratedFDeriv ℝ 2 (fun θ' : Param d m => fullNet σ b θ' x) z‖
          ≤ L₀ / Real.sqrt (m : ℝ)) :
    ChizatBachBound σ (deriv σ) b θ₀ θ
      ((L₀ * R ^ 2) / (2 * Real.sqrt (m : ℝ))) :=
  ⟨fun x =>
    chizat_bach_taylor_bound_of_radius (d := d) σ hσ_contDiff hσ_diff
      b θ₀ θ x hL₀ hR hmove (hHess x)⟩

/-! ### The analytical `O(1/√p)` T6c-nonlin theorem -/

/-- **Analytical Chizat-Bach `O(1/√p)` NTK kernel-expansion theorem.**

The fully-analytical T6c-nonlin theorem for smooth activations
`σ ∈ C²`: under the finite-span hypothesis of T6c-lin, a segment
Hessian bound `‖Hess‖ ≤ L₀ / √m` (from Phase 2a), and a
width-independent movement bound `‖θ - θ₀‖ ≤ 2 √Kmax · ‖r(0)‖ / ρ`
(from Phase 2b), there exist expansion coefficients `α : Fin n → ℝ`
such that

  `sup_x |fullNet σ b θ x
            - (fullNet σ b θ₀ x + ∑ i, α i · K_NTK(x, x_i))|`
    ` ≤ (L₀ · 4 Kmax · ‖r(0)‖² / ρ²) / (2 √m)`
    `= O(1/√p)`.

The RHS is fully explicit: all constants except the `1 / √m` prefactor
are width-independent.  This delivers the smooth-activation instance
of Bach (2024) §12.4's promise that the nonlinear network is a
kernel-regression predictor in the empirical-NTK RKHS, with a
width-independent-times-`1/√p` residual.

The residual bound is width-independent modulo the `1 / √m` prefactor,
matching Chizat & Bach (2019). -/
theorem ntk_network_approx_kernel_expansion_analytical
    {n m : ℕ}
    (σ : ℝ → ℝ)
    (hσ_contDiff : ContDiff ℝ 2 σ)
    (hσ_diff : Differentiable ℝ σ)
    (b : Fin m → ℝ)
    (θ₀ θ : Param d m)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    {L₀ Kmax r0_norm : ℝ} (hL₀ : 0 ≤ L₀) (hKmax : 0 ≤ Kmax)
    (hr0_nn : 0 ≤ r0_norm)
    {ρ : ℝ} (hρ_pos : 0 < ρ)
    (hmove : ‖θ - θ₀‖ ≤ 2 * Real.sqrt Kmax * r0_norm / ρ)
    (hHess : ∀ x : EuclideanSpace ℝ (Fin d),
      ∀ z ∈ segment ℝ θ₀ θ,
        ‖iteratedFDeriv ℝ 2 (fun θ' : Param d m => fullNet σ b θ' x) z‖
          ≤ L₀ / Real.sqrt (m : ℝ))
    (h_span : θ - θ₀ ∈
      Submodule.span ℝ
        (Set.range (fun i => gradFullNet σ (deriv σ) b θ₀ (xs i)))) :
    ∃ α : Fin n → ℝ,
      ∀ x : EuclideanSpace ℝ (Fin d),
        |fullNet σ b θ x -
            (fullNet σ b θ₀ x +
              ∑ i, α i * paramNTKKernel σ (deriv σ) b θ₀ x (xs i))|
          ≤ (L₀ * (4 * Kmax * r0_norm ^ 2 / ρ ^ 2)) /
              (2 * Real.sqrt (m : ℝ)) := by
  classical
  -- Step 1: build the analytical `ChizatBachBound` witness from Phase 2c.
  have hCB : ChizatBachBound σ (deriv σ) b θ₀ θ
      ((L₀ * (4 * Kmax * r0_norm ^ 2 / ρ ^ 2)) / (2 * Real.sqrt (m : ℝ))) :=
    chizatBachBound_ofAnalytical (d := d) σ hσ_contDiff hσ_diff b θ₀ θ
      hL₀ hKmax hr0_nn hρ_pos hmove hHess
  -- Step 2: feed into the parametric T6c-nonlin shell.
  exact ntk_network_approx_kernel_expansion σ (deriv σ) b θ₀ θ xs h_span hCB

/-- **Analytical Chizat-Bach `O(1/√p)` theorem in generic-radius form.**

A minor repackaging of `ntk_network_approx_kernel_expansion_analytical`
that keeps the width-independent movement radius `R` symbolic rather
than substituting `R = 2 √Kmax · ‖r(0)‖ / ρ`.  The conclusion is

  `sup_x |fullNet σ b θ x
            - (fullNet σ b θ₀ x + ∑ i, α i · K_NTK(x, x_i))|`
    ` ≤ L₀ · R² / (2 √m)`.

Useful when the caller carries a movement bound `‖θ - θ₀‖ ≤ R` in
generic form (e.g., from an alternative Phase 2b lemma). -/
theorem ntk_network_approx_kernel_expansion_analytical_of_radius
    {n m : ℕ}
    (σ : ℝ → ℝ)
    (hσ_contDiff : ContDiff ℝ 2 σ)
    (hσ_diff : Differentiable ℝ σ)
    (b : Fin m → ℝ)
    (θ₀ θ : Param d m)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    {L₀ R : ℝ} (hL₀ : 0 ≤ L₀) (hR : 0 ≤ R)
    (hmove : ‖θ - θ₀‖ ≤ R)
    (hHess : ∀ x : EuclideanSpace ℝ (Fin d),
      ∀ z ∈ segment ℝ θ₀ θ,
        ‖iteratedFDeriv ℝ 2 (fun θ' : Param d m => fullNet σ b θ' x) z‖
          ≤ L₀ / Real.sqrt (m : ℝ))
    (h_span : θ - θ₀ ∈
      Submodule.span ℝ
        (Set.range (fun i => gradFullNet σ (deriv σ) b θ₀ (xs i)))) :
    ∃ α : Fin n → ℝ,
      ∀ x : EuclideanSpace ℝ (Fin d),
        |fullNet σ b θ x -
            (fullNet σ b θ₀ x +
              ∑ i, α i * paramNTKKernel σ (deriv σ) b θ₀ x (xs i))|
          ≤ (L₀ * R ^ 2) / (2 * Real.sqrt (m : ℝ)) := by
  classical
  have hCB : ChizatBachBound σ (deriv σ) b θ₀ θ
      ((L₀ * R ^ 2) / (2 * Real.sqrt (m : ℝ))) :=
    chizatBachBound_ofAnalytical_of_radius (d := d) σ hσ_contDiff hσ_diff
      b θ₀ θ hL₀ hR hmove hHess
  exact ntk_network_approx_kernel_expansion σ (deriv σ) b θ₀ θ xs h_span hCB

/-! ### Codex xhigh sanity gate

At `L₀ = Kmax = ‖r(0)‖ = ρ = m = 1`, the bound RHS is
`1 · (4 · 1 · 1² / 1²) / (2 · √1) = 4 / 2 = 2`. -/

section SanityCheck

/-- **Codex xhigh sanity gate.**

Numerical instantiation of the Phase 2d analytical payoff constant.
At `L₀ = Kmax = ‖r(0)‖ = ρ = m = 1`, the RHS

  `L₀ · (4 · Kmax · ‖r(0)‖² / ρ²) / (2 · √m)`

reduces to `2`.  This confirms the constant tracking is arithmetically
correct (no missing factor of `1/2` or `2`). -/
theorem ntk_analytical_sanity :
    ((1 : ℝ) * (4 * (1 : ℝ) * (1 : ℝ) ^ 2 / (1 : ℝ) ^ 2))
        / (2 * Real.sqrt (1 : ℝ)) = 2 := by
  simp [Real.sqrt_one]
  norm_num

/-- `#eval`-able numerical form of the sanity gate.  Uses
`(1 : Float)` to sidestep `Real.sqrt` non-computability. -/
def ntk_analytical_sanity_value : Float :=
  (1.0 * (4.0 * 1.0 * 1.0 * 1.0 / (1.0 * 1.0))) / (2.0 * 1.0)

#eval ntk_analytical_sanity_value  -- expected: 2.0

end SanityCheck

end LTFP.MathlibExt.Probability

#print axioms LTFP.MathlibExt.Probability.ntk_network_approx_kernel_expansion_analytical
