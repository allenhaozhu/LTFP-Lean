/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Analysis.ParamL2
import LTFP.MathlibExt.Probability.NTKWidthIndependentMovement

/-!
# L² parameter-movement bound (naive sup→L² conversion)

**R4 NTK L4 — L² movement bound via sup-norm bridge.**

Phase 2b (`gradient_flow_movement_bounded`) delivers a
width-independent movement bound on the sup-normed `Param d m`
parameter space:

    ‖θ_sup(T) - θ_sup(0)‖_∞ ≤ 2 √Kmax · ‖r(0)‖ / ρ.

The L² parameter norm on `ParamL2 d m` (from L1) is related to the
sup norm via the flat-coordinate embedding, and satisfies (from
`paramL2_le_scale_param_sup`)

    ‖ϑ‖_2 ≤ √(m + m·d) · ‖ParamL2.toParam ϑ‖_∞.

Composing these two facts yields the **naive L² movement bound**

    ‖θ_L2(T) - θ_L2(0)‖_2 ≤ √(m + m·d) · (2 √Kmax · ‖r(0)‖ / ρ),

which is the deliverable of this module.

## Important honesty caveat: this bound is LOOSE

The `√(m + m·d)` factor makes this L² bound **width-dependent**
(growing as `√m`). For a two-layer network with `1/√m` output
normalization under lazy training (Chizat–Bach 2018, Prop 2.3),
the *true* L² parameter movement is **O(1) uniformly in width**:
each of the `m` neurons moves by `O(1/√m)` in Euclidean norm, and
the sum of squares of `m` such neurons is `m · (1/m) = O(1)`.

The naive sup→L² conversion cannot see this tighter bound because
it treats every sup-norm coordinate as if it independently achieved
the maximum. Getting the tight `O(1)` L² movement bound requires a
**direct energy inequality on the L² parameter norm**, not a
sup-norm-then-convert argument.

**Composition consequence for Phase 2c (L5).** If Phase 2c pairs
L3's `L₀/√m` L²-Hessian bound with L4's naive `√(m+m·d)·R` L²
movement bound, the Taylor remainder scales as

    (L₀/√m) · (√(m+m·d) · R)² ≈ L₀ · √m · d · R²,

which is `O(√m·d)` — **worse** than the desired `O(1/√m)` shape.
This does **NOT** invalidate Phase 2c; it means the O(1/√p) shape
cannot be obtained by naive composition of L3 with L4-naive. Two
strategy revisions are possible:

* **L4-part2 (banked).** Prove the tight `O(1)` L² movement bound
  via the lazy-training energy inequality (Chizat–Bach 2018 §D).
  Composing L3 (`L₀/√m`) with L4-part2 (`O(1)`) gives Taylor
  remainder `O(1/√m)` as expected.
* **Alternative composition.** Keep Phase 2b's sup-norm movement
  and derive a Hessian bound in the *matching sup-norm*, avoiding
  L² entirely for the composition step. This bypasses L4 but loses
  the Cauchy–Schwarz `1/√m` mechanism L3 exploits.

**This file delivers the naive bound only.** The tightening is
flagged as `L4-part2` and banked for later.

## Main results

* `paramL2_movement_le_sqrt_dim_sup_movement` — algebraic conversion
  lemma: `‖ParamL2.ofParam v‖ ≤ √(m + m·d) · ‖v‖` for any `v : Param d m`.
* `gradient_flow_movement_bounded_L2_via_sup_conversion` — the L² norm
  movement bound composed from Phase 2b's sup-norm bound.
* `gradient_flow_movement_bounded_L2_witness` — witness / existential
  form packaging the L² radius.

## References

* Chizat & Bach (2018), *On the global convergence of gradient descent
  for over-parameterized models using optimal transport*, Prop 2.3
  (lazy-training `O(1)` L² parameter movement).
* `LTFP.MathlibExt.Analysis.ParamL2` — L1 substrate: L² wrapper +
  sup/L² norm comparison.
* `LTFP.MathlibExt.Probability.NTKWidthIndependentMovement` — Phase 2b
  sup-norm movement bound.
-/

namespace LTFP.MathlibExt.Probability

open Real ProbabilityTheory

/-! ## Algebraic conversion: L² movement ≤ √(m+m·d) · sup movement -/

/-- **Conversion lemma.** The L² norm of `ParamL2.ofParam v` is
bounded by `√(m + m·d)` times the sup-norm `‖v‖ = ‖v‖_∞` of the
original `Param d m` vector.

This is a direct corollary of `paramL2_le_scale_param_sup` combined
with the round-trip `ParamL2.toParam (ParamL2.ofParam v) = v`
(from L1). It captures the naive `L² ≤ √dim · L∞` inequality on
the flat coordinate embedding.

**Caveat.** This bound is tight only when a single coordinate
saturates the sup-norm; for the lazy-training gradient-flow
trajectory, each coordinate is `O(1/√m)` and the true L² norm is
`O(1)`, not `√m · O(1/√m) = O(1)` (which coincidentally matches
but is not what this inequality asserts — it asserts a `√m`-worse
uniform bound applicable to any coordinate distribution). -/
theorem paramL2_movement_le_sqrt_dim_sup_movement
    {d m : ℕ} (v : Param d m) :
    ‖ParamL2.ofParam v‖
      ≤ Real.sqrt ((m + m * d : ℕ) : ℝ) * ‖v‖ := by
  -- Apply the L² ≤ √dim · sup inequality to `θ := ParamL2.ofParam v`,
  -- then rewrite `ParamL2.toParam (ParamL2.ofParam v) = v`.
  have h_bridge :
      ‖ParamL2.ofParam v‖
        ≤ Real.sqrt ((m + m * d : ℕ) : ℝ)
            * ‖ParamL2.toParam (ParamL2.ofParam v)‖ :=
    ProbabilityTheory.paramL2_le_scale_param_sup (ParamL2.ofParam v)
  have h_round : ParamL2.toParam (ParamL2.ofParam v) = v :=
    ProbabilityTheory.ParamL2.toParam_ofParam v
  rw [h_round] at h_bridge
  exact h_bridge

/-! ## L² movement bound (naive sup→L² conversion) -/

/-- **L² movement bound via naive sup→L² conversion.**

Given a gradient-flow trajectory `θ_sup : ℝ → Param d m` satisfying
the hypotheses of `gradient_flow_movement_bounded` (Phase 2b), the
lifted L² trajectory `t ↦ ParamL2.ofParam (θ_sup t)` satisfies

    ‖ParamL2.ofParam (θ_sup T) - ParamL2.ofParam (θ_sup 0)‖_2
      ≤ √(m + m·d) · (2 √Kmax · ‖r(0)‖ / ρ)

for every `T ≥ 0`. The proof combines Phase 2b's sup-norm bound
with `paramL2_movement_le_sqrt_dim_sup_movement`, using the fact
that `ParamL2.ofParam` is linear (via `paramL2Equiv.symm`) so
subtraction commutes with the L² lift.

**Loose / width-dependent.** The `√(m + m·d)` scaling factor is a
consequence of the naive `L² ≤ √dim · L∞` conversion. It grows as
`√m` and does **not** capture the tight `O(1)` L² movement that
holds under lazy training (Chizat–Bach 2018 Prop 2.3). See the
file docstring for the composition consequence and the banked
L4-part2 follow-up. -/
theorem gradient_flow_movement_bounded_L2_via_sup_conversion
    {d m : ℕ}
    (θ_sup : ℝ → Param d m)
    (hθ_diff : Differentiable ℝ θ_sup)
    (G : ℝ → Param d m)
    (hθ_ODE : ∀ t, deriv θ_sup t = -G t)
    (Kmax : ℝ) (hKmax : 0 ≤ Kmax)
    (r_norm : ℝ → ℝ)
    (r0_norm : ℝ) (hr0_nn : 0 ≤ r0_norm)
    {ρ : ℝ} (hρ_pos : 0 < ρ)
    (hr_decay : ∀ t, r_norm t ≤ r0_norm * Real.exp (-(ρ * t / 2)))
    (hG_bound : ∀ t, ‖G t‖ ≤ Real.sqrt Kmax * r_norm t)
    {T : ℝ} (hT : 0 ≤ T) :
    ‖ProbabilityTheory.ParamL2.ofParam (θ_sup T)
        - ProbabilityTheory.ParamL2.ofParam (θ_sup 0)‖
      ≤ Real.sqrt ((m + m * d : ℕ) : ℝ)
          * (2 * Real.sqrt Kmax * r0_norm / ρ) := by
  -- Step 1: Phase 2b sup-norm bound.
  have h_sup :
      ‖θ_sup T - θ_sup 0‖ ≤ 2 * Real.sqrt Kmax * r0_norm / ρ :=
    gradient_flow_movement_bounded
      θ_sup hθ_diff G hθ_ODE Kmax hKmax
      r_norm r0_norm hr0_nn hρ_pos hr_decay hG_bound hT
  -- Step 2: `ParamL2.ofParam` is linear (as `(paramL2Equiv).symm`),
  -- so subtraction commutes with the L² lift.
  have h_sub :
      ProbabilityTheory.ParamL2.ofParam (θ_sup T)
          - ProbabilityTheory.ParamL2.ofParam (θ_sup 0)
        = ProbabilityTheory.ParamL2.ofParam (θ_sup T - θ_sup 0) := by
    -- `ParamL2.ofParam = (paramL2Equiv d m).symm`, which is a linear
    -- equivalence, hence commutes with `Sub.sub` (i.e. `map_sub`).
    show (ProbabilityTheory.paramL2Equiv d m).symm (θ_sup T)
        - (ProbabilityTheory.paramL2Equiv d m).symm (θ_sup 0)
      = (ProbabilityTheory.paramL2Equiv d m).symm (θ_sup T - θ_sup 0)
    rw [map_sub]
  -- Step 3: naive `L² ≤ √dim · L∞` on the difference.
  have h_conv :
      ‖ProbabilityTheory.ParamL2.ofParam (θ_sup T - θ_sup 0)‖
        ≤ Real.sqrt ((m + m * d : ℕ) : ℝ) * ‖θ_sup T - θ_sup 0‖ :=
    paramL2_movement_le_sqrt_dim_sup_movement (θ_sup T - θ_sup 0)
  -- Step 4: combine.
  have h_sqrt_nn : 0 ≤ Real.sqrt ((m + m * d : ℕ) : ℝ) := Real.sqrt_nonneg _
  calc ‖ProbabilityTheory.ParamL2.ofParam (θ_sup T)
              - ProbabilityTheory.ParamL2.ofParam (θ_sup 0)‖
      = ‖ProbabilityTheory.ParamL2.ofParam (θ_sup T - θ_sup 0)‖ := by rw [h_sub]
    _ ≤ Real.sqrt ((m + m * d : ℕ) : ℝ) * ‖θ_sup T - θ_sup 0‖ := h_conv
    _ ≤ Real.sqrt ((m + m * d : ℕ) : ℝ) * (2 * Real.sqrt Kmax * r0_norm / ρ) :=
          mul_le_mul_of_nonneg_left h_sup h_sqrt_nn

/-! ## Witness / existential form -/

/-- **L² movement bound (witness form).**

Packages the naive-conversion L² movement bound as an explicit
existential in the radius

    R_L2 := √(m + m·d) · (2 √Kmax · ‖r(0)‖ / ρ).

The right-hand side depends on `m`, `d`, `Kmax`, `‖r(0)‖`, `ρ` —
in particular it **is width-dependent** (via the `√(m + m·d)` factor).
This is the honest naive bound; the tight `O(1)` bound is banked
as L4-part2. -/
theorem gradient_flow_movement_bounded_L2_witness
    {d m : ℕ}
    (θ_sup : ℝ → Param d m)
    (hθ_diff : Differentiable ℝ θ_sup)
    (G : ℝ → Param d m)
    (hθ_ODE : ∀ t, deriv θ_sup t = -G t)
    (Kmax : ℝ) (hKmax : 0 ≤ Kmax)
    (r_norm : ℝ → ℝ)
    (r0_norm : ℝ) (hr0_nn : 0 ≤ r0_norm)
    {ρ : ℝ} (hρ_pos : 0 < ρ)
    (hr_decay : ∀ t, r_norm t ≤ r0_norm * Real.exp (-(ρ * t / 2)))
    (hG_bound : ∀ t, ‖G t‖ ≤ Real.sqrt Kmax * r_norm t) :
    ∃ R_L2 : ℝ,
      R_L2 = Real.sqrt ((m + m * d : ℕ) : ℝ)
              * (2 * Real.sqrt Kmax * r0_norm / ρ) ∧
      0 ≤ R_L2 ∧
      ∀ T : ℝ, 0 ≤ T →
        ‖ProbabilityTheory.ParamL2.ofParam (θ_sup T)
            - ProbabilityTheory.ParamL2.ofParam (θ_sup 0)‖
          ≤ R_L2 := by
  refine
    ⟨Real.sqrt ((m + m * d : ℕ) : ℝ)
        * (2 * Real.sqrt Kmax * r0_norm / ρ),
      rfl, ?_, ?_⟩
  · -- 0 ≤ R_L2.
    have h1 : 0 ≤ 2 * Real.sqrt Kmax * r0_norm := by
      have := Real.sqrt_nonneg Kmax
      positivity
    have h2 : 0 ≤ 2 * Real.sqrt Kmax * r0_norm / ρ :=
      div_nonneg h1 hρ_pos.le
    exact mul_nonneg (Real.sqrt_nonneg _) h2
  · intro T hT
    exact gradient_flow_movement_bounded_L2_via_sup_conversion
      θ_sup hθ_diff G hθ_ODE Kmax hKmax
      r_norm r0_norm hr0_nn hρ_pos hr_decay hG_bound hT

end LTFP.MathlibExt.Probability
