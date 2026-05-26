/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Parametric movement bound from residual exponential decay

In NTK lazy-training analysis, once the residual `r(t)` is known to
decay exponentially `‖r(t)‖ ≤ ‖r(0)‖ · exp(-ρ t / 2)` and the gradient
`G(t) = ∇L(θ(t))` is controlled by the residual via the kernel-operator
bound `‖G(t)‖ ≤ √Kmax · ‖r(t)‖`, the parameter trajectory `θ(t)` can
move only a bounded amount from its initialization:

  `‖θ(T) - θ(0)‖ ≤ √Kmax · (2 ‖r(0)‖ / ρ) · (1 - exp(-ρT/2))`.

In particular, the right-hand side is uniformly bounded by
`2 √Kmax · ‖r(0)‖ / ρ`, independent of `T`. This is the "Strategy 2"
deterministic core of the bootstrap argument: residual decay (Strategy 1)
yields the movement bound here, which in turn closes the lazy-training
boundary condition.

## Strategy

Apply Mathlib's fencing theorem
`image_norm_le_of_norm_deriv_right_le_deriv_boundary` to the curve
`g(t) := θ(t) - θ(0)` with boundary
`B(t) := √Kmax · (2 ‖r(0)‖ / ρ) · (1 - exp(-ρ t / 2))`.

* `‖g(0)‖ = 0 ≤ B(0) = 0`.
* `deriv g(t) = deriv θ(t) = -G(t)`, so
  `‖deriv g(t)‖ = ‖G(t)‖ ≤ √Kmax · ‖r(0)‖ · exp(-ρ t / 2)`.
* `deriv B(t) = √Kmax · ‖r(0)‖ · exp(-ρ t / 2)` (constant times
  `-(- ρ/2)` times the exponential).

The fencing theorem then concludes `‖g(t)‖ ≤ B(t)` on `[0, T]`. Evaluating
at `T` gives the bound.

## Main result

* `movement_from_residual_decay` — the parametric movement bound.

## References

* Jacot, Gabriel, Hongler (2018), *Neural Tangent Kernel: Convergence
  and Generalization in Neural Networks*.
* Bach (2024), *Learning Theory from First Principles* §12.
-/

namespace LTFP.MathlibExt.Probability

open Set

/-- **Parametric movement bound from residual exponential decay.**

Given:

* a parameter trajectory `θ : ℝ → E` that is differentiable with
  derivative `deriv θ t = -G t`,
* a gradient norm bound `‖G t‖ ≤ √Kmax · ‖r(0)‖ · exp(-ρ t / 2)`
  (which arises in NTK analyses from
  `‖∇L(θ)‖ ≤ √‖K(θ)‖_op · ‖r(t)‖` combined with residual exponential
  decay `‖r(t)‖ ≤ ‖r(0)‖ · exp(-ρ t / 2)`),
* `Kmax ≥ 0`, `‖r(0)‖ ≥ 0`, and `ρ > 0`,

we have

  `‖θ(T) - θ(0)‖ ≤ √Kmax · (2 ‖r(0)‖ / ρ) · (1 - exp(-ρT/2))`

for every `T ≥ 0`. In particular,
`‖θ(T) - θ(0)‖ ≤ 2 √Kmax · ‖r(0)‖ / ρ` uniformly in `T`. This is the
deterministic core of NTK lazy-training movement bounds. -/
theorem movement_from_residual_decay
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (θ : ℝ → E)
    (hθ_diff : Differentiable ℝ θ)
    (G : ℝ → E)
    (hθ_ODE : ∀ t, deriv θ t = -G t)
    (Kmax : ℝ) (_hKmax : 0 ≤ Kmax)
    (r0_norm : ℝ) (_hr0_nn : 0 ≤ r0_norm)
    {ρ : ℝ} (hρ_pos : 0 < ρ)
    (hG_bound : ∀ t, ‖G t‖ ≤ Real.sqrt Kmax * (r0_norm * Real.exp (-(ρ * t / 2))))
    {T : ℝ} (hT : 0 ≤ T) :
    ‖θ T - θ 0‖ ≤
      Real.sqrt Kmax * (2 * r0_norm / ρ) * (1 - Real.exp (-(ρ * T / 2))) := by
  -- Curve `g(t) := θ(t) - θ(0)`.
  set g : ℝ → E := fun t => θ t - θ 0 with hg_def
  -- Boundary `B(t) := √Kmax · (2 r0 / ρ) · (1 - exp(-ρ t / 2))`.
  set B : ℝ → ℝ := fun t =>
    Real.sqrt Kmax * (2 * r0_norm / ρ) * (1 - Real.exp (-(ρ * t / 2))) with hB_def
  -- Boundary derivative `B'(t) := √Kmax · r0 · exp(-ρ t / 2)`.
  set B' : ℝ → ℝ := fun t => Real.sqrt Kmax * (r0_norm * Real.exp (-(ρ * t / 2))) with hB'_def
  -- Curve derivative `g'(t) = -G(t)`.
  set g' : ℝ → E := fun t => -G t with hg'_def
  -- Step 1: `g` is continuous on `[0, T]`.
  have hg_diff : Differentiable ℝ g := hθ_diff.sub_const _
  have hg_cont : ContinuousOn g (Icc 0 T) := hg_diff.continuous.continuousOn
  -- Step 2: For `x ∈ Ico 0 T`, `g` has right derivative `g' x = -G x`.
  have hg_hasDeriv : ∀ x ∈ Ico (0 : ℝ) T, HasDerivWithinAt g (g' x) (Ici x) x := by
    intro x _
    have h₁ : HasDerivAt θ (deriv θ x) x := (hθ_diff x).hasDerivAt
    have h₂ : HasDerivAt g (deriv θ x) x := by
      have := h₁.sub_const (θ 0)
      simpa [g] using this
    have h₃ : deriv θ x = g' x := by
      simp [g', hθ_ODE x]
    have h₄ : HasDerivAt g (g' x) x := h₃ ▸ h₂
    exact h₄.hasDerivWithinAt
  -- Step 3: `‖g 0‖ = 0 ≤ B 0`.
  have hg_zero : g 0 = 0 := by simp [g]
  have hB_zero : B 0 = 0 := by
    simp [B, Real.exp_zero]
  have ha : ‖g 0‖ ≤ B 0 := by
    rw [hg_zero, hB_zero, norm_zero]
  -- Step 4: `B` has derivative `B' x` everywhere on ℝ.
  -- Compute `deriv (Real.exp ∘ fun x => -(ρ * x / 2)) = -ρ/2 · exp(-(ρ x / 2))`.
  have h_inner_hasDeriv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => -(ρ * x / 2)) (-(ρ / 2)) x := by
    intro x
    have h1 : HasDerivAt (fun x : ℝ => ρ * x / 2) (ρ / 2) x := by
      have := ((hasDerivAt_id x).const_mul ρ).div_const 2
      simpa [mul_comm, mul_div_assoc] using this
    simpa using h1.neg
  have h_exp_hasDeriv : ∀ x : ℝ,
      HasDerivAt (fun x : ℝ => Real.exp (-(ρ * x / 2)))
        (Real.exp (-(ρ * x / 2)) * (-(ρ / 2))) x := by
    intro x
    exact (Real.hasDerivAt_exp _).comp x (h_inner_hasDeriv x)
  have h_one_sub_hasDeriv : ∀ x : ℝ,
      HasDerivAt (fun x : ℝ => 1 - Real.exp (-(ρ * x / 2)))
        (-(Real.exp (-(ρ * x / 2)) * (-(ρ / 2)))) x := by
    intro x
    have := ((hasDerivAt_const x (1 : ℝ))).sub (h_exp_hasDeriv x)
    simpa using this
  have hB_hasDeriv : ∀ x : ℝ, HasDerivAt B (B' x) x := by
    intro x
    have h := (h_one_sub_hasDeriv x).const_mul (Real.sqrt Kmax * (2 * r0_norm / ρ))
    -- h : HasDerivAt (fun x => √Kmax · (2 r0 / ρ) · (1 - exp(-ρ x / 2)))
    --       (√Kmax · (2 r0 / ρ) · -(exp(-ρx/2) · -(ρ/2))) x
    have h_target_eq :
        Real.sqrt Kmax * (2 * r0_norm / ρ) *
          (-(Real.exp (-(ρ * x / 2)) * (-(ρ / 2)))) = B' x := by
      have hρ_ne : ρ ≠ 0 := ne_of_gt hρ_pos
      have : Real.sqrt Kmax * (2 * r0_norm / ρ) *
            (-(Real.exp (-(ρ * x / 2)) * (-(ρ / 2)))) =
          Real.sqrt Kmax * (r0_norm * Real.exp (-(ρ * x / 2))) := by
        field_simp
      simpa [B'] using this
    exact h_target_eq ▸ h
  -- Step 5: For `x ∈ Ico 0 T`, `‖g' x‖ ≤ B' x`.
  have hbound : ∀ x ∈ Ico (0 : ℝ) T, ‖g' x‖ ≤ B' x := by
    intro x _
    have h : ‖g' x‖ = ‖G x‖ := by
      simp [g']
    rw [h]
    have := hG_bound x
    simpa [B'] using this
  -- Step 6: Apply the fencing theorem.
  have hbig := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    hg_cont hg_hasDeriv ha hB_hasDeriv hbound
  -- Step 7: Evaluate at `T`.
  have hT_mem : T ∈ Icc (0 : ℝ) T := ⟨hT, le_refl T⟩
  have := hbig hT_mem
  -- `this : ‖g T‖ ≤ B T`
  have hg_T : g T = θ T - θ 0 := rfl
  rw [hg_T] at this
  exact this

end LTFP.MathlibExt.Probability
