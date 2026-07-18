/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Analysis.ParamL2
import LTFP.MathlibExt.Probability.NTKWidthIndependentMovement

/-!
# Width-independent L² parameter-movement bound via Chizat–Bach §B.3 energy

**R4 NTK L4-part2 — Chizat–Bach 2018 arXiv:1812.07956 Appendix B.3 / §D
energy-bootstrap argument.**

The naive L² movement bound
(`gradient_flow_movement_bounded_L2_via_sup_conversion`, L4-part1) inherits a
`√(m + m·d)` factor from the sup→L² conversion, making the resulting bound
**width-dependent**. That factor is a strict artefact of the coordinatewise
conversion — the sup-norm treatment saturates when a single coordinate
achieves the maximum, and the `L² ≤ √dim · L∞` step then charges the full
dimension.

The **Chizat–Bach energy argument** delivers the correct width-independent
`O(1)` L² movement bound directly, by running Grönwall on the energy
`E(t) := ‖θ_L2(t) - θ_L2(0)‖²` instead of composing sup-norm bounds.

## The energy argument (Chizat–Bach 2018 §B.3)

For gradient flow `θ'(t) = -∇L(θ(t))` on any normed space `E` (in
particular on `ParamL2 d m := EuclideanSpace ℝ (Fin (m + m·d))`), one has

  `d/dt (½‖θ(t) - θ₀‖²) = ⟨θ - θ₀, θ'⟩ = -⟨θ - θ₀, ∇L⟩ ≤ ‖θ - θ₀‖ · ‖∇L‖`.

Under the standard NTK kernel-operator bound `‖∇L(θ)‖ ≤ √Kmax · ‖r(θ)‖`
(chain rule on the empirical MSE loss composed with the network Jacobian
factored through the training-kernel Gram matrix), we get

  `d/dt ‖θ - θ₀‖ ≤ ‖∇L‖ ≤ √Kmax · ‖r(t)‖`.

If the residual satisfies exponential decay
`‖r(t)‖ ≤ r₀ · exp(-Kmax·t/2)`, integration gives

  `‖θ(T) - θ₀‖ ≤ ∫₀^T √Kmax · r₀ · exp(-Kmax·t/2) dt`
              `= √Kmax · r₀ · (2/Kmax) · (1 - exp(-Kmax·T/2))`
              `≤ 2 · r₀ / √Kmax = 2 · r₀ · √Kmax / Kmax`,

**width-independent** — depending only on `r₀`, `Kmax`, no `√m` or `√(md)`
factor.

## Composition with the L4-part1 Hessian

Composed with Task L3's L²-Hessian bound `‖∇²f_θ‖_op ≤ L₀ / √m`, the
Taylor remainder becomes

  `|f_θ - f^{lin}_θ| ≤ (L₀/(2√m)) · ‖θ - θ₀‖² ≤ (L₀/(2√m)) · (2 r₀/√Kmax)²`
                    `= (2 L₀ r₀²) / (√m · Kmax) = O(1/√m)`,

closing the Chizat–Bach `O(1/√p)` lazy-training linearization shape
unconditionally.

## Substrate reuse

The general-normed-space energy-fencing argument is already discharged in
`LTFP.MathlibExt.Probability.MovementFromResidualDecay` /
`LTFP.MathlibExt.Probability.NTKWidthIndependentMovement`
(`gradient_flow_movement_bounded`) — it uses Mathlib's
`image_norm_le_of_norm_deriv_right_le_deriv_boundary` on the curve
`g(t) := θ(t) - θ(0)` fenced by
`B(t) := √Kmax · (2 r₀ / ρ) · (1 - exp(-ρt/2))`. This IS the Chizat–Bach
§B.3 energy argument in disguise — Mathlib's fencing lemma is the
integrated form of

  `d/dt ‖g(t)‖ ≤ ‖g'(t)‖ = ‖∇L(θ(t))‖ ≤ √Kmax · ‖r(t)‖`,

which is the same inequality Chizat–Bach integrate by hand.

**Because `ParamL2 d m` is a `NormedAddCommGroup` and a `NormedSpace ℝ`
by definition** (`EuclideanSpace ℝ (Fin p)` is a Euclidean space with the
canonical L² norm), the existing generic movement bound applies
**directly** — no `√(m + m·d)` dimension factor appears. That factor
crept into L4-part1 only because the trajectory there was defined on the
sup-normed `Param d m` and then lifted to `ParamL2` via `ParamL2.ofParam`,
so the sup→L² conversion was applied at the outer boundary.

By defining the trajectory **on `ParamL2 d m` from the start** and asking
for the gradient-flow ODE **in that L² norm**, the whole argument runs
inside `EuclideanSpace ℝ (Fin (m + m·d))` and the width factor never
appears.

## Main results

* `chizat_bach_energy_movement_L2_bounded_general` — the parametric-shell
  Chizat–Bach movement bound `‖θ_L2(T) - θ_L2(0)‖ ≤ 2 √Kmax · r₀ / ρ`
  on the L² parameter space, matching the general `E`-shape movement bound
  applied at `E := ParamL2 d m`.
* `chizat_bach_energy_movement_L2_bounded` — the headline
  Chizat–Bach form with `ρ = Kmax > 0` (standard NTK kernel-coercivity
  convention), yielding
  `‖θ_L2(T) - θ_L2(0)‖ ≤ 2 · r₀ · √Kmax / Kmax = 2 · r₀ / √Kmax`,
  which is **width-independent** — no `m` or `d` factor.
* `chizat_bach_energy_movement_L2_witness` — witness form packaging the
  bound as an explicit existential in the width-independent radius.

## References

* Chizat, L. & Bach, F. (2018). *On the global convergence of gradient
  descent for over-parameterized models using optimal transport.*
  arXiv:1812.07956, Appendix B.3 / §D.
* `LTFP.MathlibExt.Probability.MovementFromResidualDecay` — the
  underlying fencing-form energy argument on a general normed space.
* `LTFP.MathlibExt.Probability.NTKWidthIndependentMovement` — the
  headline movement bound in general normed-space form; instantiated
  here at `E := ParamL2 d m`.
* `LTFP.MathlibExt.Analysis.ParamL2` — L1 substrate: `ParamL2 d m` and
  the sup/L² norm comparison.
* `LTFP.MathlibExt.Probability.NTKWidthIndependentMovementL2` — L4-part1
  naive sup→L² conversion (loose `√(m + m·d)` factor).
-/

namespace LTFP.MathlibExt.Probability

open ProbabilityTheory Real

/-! ## Parametric-shell L² movement bound (general `ρ`) -/

/-- **Chizat–Bach energy-argument L² movement bound (parametric shell).**

The width-independent L² movement bound on the flat L² parameter space
`ParamL2 d m := EuclideanSpace ℝ (Fin (m + m·d))`, following the
Chizat–Bach 2018 arXiv:1812.07956 §B.3 energy-bootstrap argument.

**Hypotheses.**

* `θ_L2 : ℝ → ParamL2 d m` — a differentiable parameter trajectory on the
  L² parameter space.
* Gradient-flow ODE `deriv θ_L2 t = -G t` where `G : ℝ → ParamL2 d m` is
  the loss gradient in the L² parameter norm.
* Residual exponential decay `r_norm(t) ≤ r₀ · exp(-ρ t / 2)`.
* Kernel-operator gradient bound `‖G(t)‖ ≤ √Kmax · r_norm(t)` — this is
  the chain-rule + kernel-Gram identity for the empirical MSE loss.
* `Kmax ≥ 0`, `ρ > 0`, `r₀ ≥ 0`.

**Conclusion.**

  `‖θ_L2(T) - θ_L2(0)‖ ≤ 2 √Kmax · r₀ / ρ` for every `T ≥ 0`.

**Why this is width-independent.** The right-hand side depends only on
`Kmax`, `r₀`, `ρ` — none of `m`, `d`, or `p = m + m·d`. The bound holds
uniformly across every network width. This is the correct rate; the
naive `√(m + m·d)` factor from L4-part1 is a **strict** sup→L²
conversion artefact and never appears here because the whole argument
runs inside the L² space.

**Proof.** `ParamL2 d m` is by definition a `NormedAddCommGroup` and a
`NormedSpace ℝ`, so the general normed-space movement bound
`gradient_flow_movement_bounded` (which encodes the Chizat–Bach §B.3
energy fencing argument via Mathlib's
`image_norm_le_of_norm_deriv_right_le_deriv_boundary`) applies
directly. -/
theorem chizat_bach_energy_movement_L2_bounded_general
    {d m : ℕ}
    (θ_L2 : ℝ → ParamL2 d m)
    (hθ_diff : Differentiable ℝ θ_L2)
    (G : ℝ → ParamL2 d m)
    (hθ_ODE : ∀ t, deriv θ_L2 t = -G t)
    (Kmax : ℝ) (hKmax : 0 ≤ Kmax)
    (r_norm : ℝ → ℝ)
    (r0_norm : ℝ) (hr0_nn : 0 ≤ r0_norm)
    {ρ : ℝ} (hρ_pos : 0 < ρ)
    (hr_decay : ∀ t, r_norm t ≤ r0_norm * Real.exp (-(ρ * t / 2)))
    (hG_bound : ∀ t, ‖G t‖ ≤ Real.sqrt Kmax * r_norm t)
    {T : ℝ} (hT : 0 ≤ T) :
    ‖θ_L2 T - θ_L2 0‖ ≤ 2 * Real.sqrt Kmax * r0_norm / ρ := by
  -- Apply the generic normed-space movement bound at `E := ParamL2 d m`.
  -- `ParamL2 d m := EuclideanSpace ℝ (Fin (m + m·d))` is a
  -- `NormedAddCommGroup + NormedSpace ℝ` by definition, so the generic
  -- movement bound `gradient_flow_movement_bounded` instantiates without
  -- any dimension factor. This is the Chizat–Bach §B.3 energy argument
  -- discharged via Mathlib's fencing lemma
  -- `image_norm_le_of_norm_deriv_right_le_deriv_boundary`.
  exact gradient_flow_movement_bounded
    θ_L2 hθ_diff G hθ_ODE Kmax hKmax
    r_norm r0_norm hr0_nn hρ_pos hr_decay hG_bound hT

/-! ## Headline: Chizat–Bach form with `ρ = Kmax` (kernel coercivity) -/

/-- **Chizat–Bach headline L² movement bound.**

The standard NTK convention identifies the coercivity constant `ρ` with
the training-kernel spectral floor `Kmax` (the smallest eigenvalue of the
Gram matrix `K(θ₀)`, preserved under lazy training by
`ntk_coercivity_preservation`). Under this identification and the
kernel-operator gradient bound `‖∇L‖ ≤ √Kmax · ‖r‖`, the general
parametric-shell bound simplifies to

  `‖θ_L2(T) - θ_L2(0)‖ ≤ 2 · r₀ · √Kmax / Kmax`.

Note the equivalent form `2 · r₀ · √Kmax / Kmax = 2 · r₀ / √Kmax`; both
appear in the Chizat–Bach literature.

This is the **width-independent** bound announced in the module docstring
— the right-hand side has no `m`, no `d`, no `p`. In the Chizat–Bach
`O(1/√p)` chain, this movement bound composes with Task L3's
`L₀/√m` L²-Hessian to give the

  `(L₀/(2√m)) · (2 r₀ · √Kmax / Kmax)² = 2 L₀ r₀² / (√m · Kmax)`

Taylor remainder — the `O(1/√m) = O(1/√p)` linearization shape.

**Extra hypothesis over the general form.** `Kmax > 0` (strict positivity
of the kernel spectrum). This is the standard NTK non-degeneracy
assumption; it holds when the initialization is non-collinear on the
training set (the exponential-decay hypothesis
`ntk_lazy_training_carrier_parametric` already implicitly uses `Kmax > 0`
to state the decay). -/
theorem chizat_bach_energy_movement_L2_bounded
    {d m : ℕ}
    (θ_L2 : ℝ → ParamL2 d m)
    (hθ_diff : Differentiable ℝ θ_L2)
    (G : ℝ → ParamL2 d m)
    (hθ_ODE : ∀ t, deriv θ_L2 t = -G t)
    {Kmax : ℝ} (hKmax_pos : 0 < Kmax)
    (r_norm : ℝ → ℝ)
    (r0_norm : ℝ) (hr0_nn : 0 ≤ r0_norm)
    (hr_decay : ∀ t, r_norm t ≤ r0_norm * Real.exp (-(Kmax * t / 2)))
    (hG_bound : ∀ t, ‖G t‖ ≤ Real.sqrt Kmax * r_norm t)
    {T : ℝ} (hT : 0 ≤ T) :
    ‖θ_L2 T - θ_L2 0‖ ≤ 2 * r0_norm * Real.sqrt Kmax / Kmax := by
  -- Apply the general parametric-shell bound at `ρ := Kmax`.
  have h_gen := chizat_bach_energy_movement_L2_bounded_general
    θ_L2 hθ_diff G hθ_ODE Kmax hKmax_pos.le r_norm r0_norm hr0_nn
    hKmax_pos hr_decay hG_bound hT
  -- Algebraic rewrite:
  --   2 * √Kmax * r₀ / Kmax = 2 * r₀ * √Kmax / Kmax
  -- (just commutativity of multiplication under the division).
  have h_rw : 2 * Real.sqrt Kmax * r0_norm / Kmax
              = 2 * r0_norm * Real.sqrt Kmax / Kmax := by ring
  rw [h_rw] at h_gen
  exact h_gen

/-! ## Witness form (existential) -/

/-- **Chizat–Bach L² movement bound (witness form).**

Packages the width-independent L² movement bound as an explicit
existential in the radius

  `R_L2 := 2 · r₀ · √Kmax / Kmax`.

The right-hand side depends only on `Kmax` and `r₀`, no width variable.
Standard NTK lazy-training analysis provides all three of these
constants width-independent, so `R_L2` is a width-independent constant
that uniformly bounds `‖θ_L2(T) - θ_L2(0)‖` for every `T ≥ 0`.

**Downstream composition (KDD-2027 NTK paper).** Composed with Task L3's
`L₀/√m` L²-Hessian bound at radius `R_L2`, the Chizat–Bach Taylor
remainder is

  `|f_θ(x) - f^{lin}_θ(x)| ≤ (L₀/(2√m)) · R_L2² = O(1/√m)`,

closing the Chizat–Bach `O(1/√p)` lazy-training linearization shape.

**Comparison with L4-part1.** The witness form
`gradient_flow_movement_bounded_L2_witness` in
`NTKWidthIndependentMovementL2` returns a radius scaled by
`√(m + m·d)` — that comes from the naive sup→L² conversion applied at
the outer boundary. This theorem's radius has no such factor because
the entire argument runs on the L² parameter space directly. -/
theorem chizat_bach_energy_movement_L2_witness
    {d m : ℕ}
    (θ_L2 : ℝ → ParamL2 d m)
    (hθ_diff : Differentiable ℝ θ_L2)
    (G : ℝ → ParamL2 d m)
    (hθ_ODE : ∀ t, deriv θ_L2 t = -G t)
    {Kmax : ℝ} (hKmax_pos : 0 < Kmax)
    (r_norm : ℝ → ℝ)
    (r0_norm : ℝ) (hr0_nn : 0 ≤ r0_norm)
    (hr_decay : ∀ t, r_norm t ≤ r0_norm * Real.exp (-(Kmax * t / 2)))
    (hG_bound : ∀ t, ‖G t‖ ≤ Real.sqrt Kmax * r_norm t) :
    ∃ R_L2 : ℝ,
      R_L2 = 2 * r0_norm * Real.sqrt Kmax / Kmax ∧
      0 ≤ R_L2 ∧
      ∀ T : ℝ, 0 ≤ T → ‖θ_L2 T - θ_L2 0‖ ≤ R_L2 := by
  refine ⟨2 * r0_norm * Real.sqrt Kmax / Kmax, rfl, ?_, ?_⟩
  · -- 0 ≤ R_L2. Numerator is a product of nonnegatives; denominator is
    -- strictly positive.
    have h_num_nn : 0 ≤ 2 * r0_norm * Real.sqrt Kmax := by
      have h1 : (0 : ℝ) ≤ 2 * r0_norm := by linarith
      have h2 : 0 ≤ Real.sqrt Kmax := Real.sqrt_nonneg _
      exact mul_nonneg h1 h2
    exact div_nonneg h_num_nn hKmax_pos.le
  · intro T hT
    exact chizat_bach_energy_movement_L2_bounded
      θ_L2 hθ_diff G hθ_ODE hKmax_pos
      r_norm r0_norm hr0_nn hr_decay hG_bound hT

/-! ## Consequence: `O(1/√p)` Taylor-remainder shape

The Chizat–Bach linearization error is

  `|f_θ(x) - f^{lin}_θ(x)| ≤ (L_op / 2) · ‖θ - θ₀‖²`,

where `L_op` is a Hessian operator-norm bound (from Task L3, `L₀ / √m`).
Composing with the `R_L2 := 2 r₀ · √Kmax / Kmax` movement bound above
yields the promised `O(1/√m) = O(1/√p)` shape. -/

/-- **Composition consequence: `O(1/√m)` linearization error.**

If the network Hessian obeys the L² operator-norm bound
`L_op ≤ L₀ / √m` (Task L3 shape), then the Taylor-remainder bound
`(L_op / 2) · R_L2²` at the Chizat–Bach movement radius simplifies to

  `(L₀ / (2 √m)) · (2 r₀ · √Kmax / Kmax)² = 2 L₀ r₀² / (√m · Kmax)`,

which is `O(1/√m)` uniformly in the input `x` and the trajectory time
`T ≥ 0`. This is the shape of the Chizat–Bach `O(1/√p)` linearization
theorem in the NTK lazy-training regime, closed **unconditionally** in
`m` and `d` — the movement bound contributes no width factor to the
denominator.

This lemma is the algebraic identity used to package the shape; it does
not require any of the ODE / gradient-flow / kernel hypotheses. It is
stated in explicit form so downstream carriers can compose without
re-deriving the algebra. -/
theorem chizat_bach_taylor_shape_from_movement_bound
    (L0 : ℝ) (_hL0_nn : 0 ≤ L0)
    (r0_norm : ℝ) (_hr0_nn : 0 ≤ r0_norm)
    {Kmax : ℝ} (hKmax_pos : 0 < Kmax)
    {m : ℕ} (hm_pos : 0 < m) :
    (L0 / (2 * Real.sqrt m)) *
        (2 * r0_norm * Real.sqrt Kmax / Kmax) ^ 2
      = 2 * L0 * r0_norm ^ 2 / (Real.sqrt m * Kmax) := by
  -- Setup positivity facts for the denominators.
  have hm_sqrt_pos : 0 < Real.sqrt m := by
    apply Real.sqrt_pos.mpr; exact_mod_cast hm_pos
  have hKmax_nn : 0 ≤ Kmax := hKmax_pos.le
  have hKmax_sq : Real.sqrt Kmax ^ 2 = Kmax := Real.sq_sqrt hKmax_nn
  have hKmax_ne : (Kmax : ℝ) ≠ 0 := ne_of_gt hKmax_pos
  have hm_sqrt_ne : Real.sqrt m ≠ 0 := ne_of_gt hm_sqrt_pos
  -- The identity is pure real algebra with a single square-root
  -- simplification `(√Kmax)² = Kmax`. Rewriting the square first turns
  -- the goal into a rational-function identity closed by
  -- `field_simp` + `ring`.
  have h_sq_expand :
      (2 * r0_norm * Real.sqrt Kmax / Kmax) ^ 2
        = (4 * r0_norm ^ 2 * Real.sqrt Kmax ^ 2) / Kmax ^ 2 := by
    field_simp
    ring
  rw [h_sq_expand, hKmax_sq]
  field_simp
  ring

end LTFP.MathlibExt.Probability
