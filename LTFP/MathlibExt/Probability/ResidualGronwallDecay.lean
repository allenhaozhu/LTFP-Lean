/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import LTFP.MathlibExt.MatrixAnalysis.LoewnerPerturbation

/-!
# Grönwall exponential residual decay for the linearized NTK gradient flow

Given a residual `r : ℝ → EuclideanSpace ℝ (Fin n)` evolving by the
linear ODE `r'(t) = -(K(t) · r(t))` with `K(t) : Matrix (Fin n) (Fin n) ℝ`
coercive in the sense `λ_min(K(t)) ≥ ρ / 2`, the residual decays
exponentially:

  `‖r(T)‖² ≤ ‖r(0)‖² · exp(-ρ · T)`.

This is the **deterministic core** of NTK lazy-training convergence —
all the random / Lyapunov / bootstrap machinery feeds into this clean
parametric Grönwall statement.

## Strategy (hand-rolled exponential Grönwall)

Set the Lyapunov function `V(t) := ‖r(t)‖²`. Then

  `V'(t) = 2 ⟨r(t), r'(t)⟩ = -2 ⟨r(t), K(t) · r(t)⟩`.

Loewner coercivity `K(t) ≽ (ρ/2) • 1` gives `⟨r, K · r⟩ ≥ (ρ/2) ‖r‖²`,
so `V'(t) ≤ -ρ · V(t)`.

Define `g(t) := V(t) · exp(ρ · t)`. Then

  `g'(t) = (V'(t) + ρ · V(t)) · exp(ρ · t) ≤ 0`.

Hence `g` is antitone, so `g(T) ≤ g(0) = ‖r(0)‖²`. Rearranging gives
`V(T) ≤ ‖r(0)‖² · exp(-ρ · T)`.

This bypasses Mathlib's `Gronwall` API (which is shaped for ODE
trajectory comparison) in favour of a direct monotonicity argument.

## Main result

* `ntk_residual_gronwall_decay` — the exponential decay bound.

## References

* This is the standard textbook Grönwall lemma for linear ODEs with
  coercive symmetric drift. See, e.g., Bach (2024) *Learning Theory
  from First Principles* §12 (NTK lazy training).
-/

open scoped InnerProductSpace MatrixOrder
open Matrix

namespace LTFP

variable {n : ℕ}

/-! ### Quadratic-form bound from Loewner coercivity (real case) -/

/-- **Quadratic-form coercivity from Loewner coercivity (real case).**

If `(ρ/2) • 1 ≤ K` in the Loewner order on `Matrix (Fin n) (Fin n) ℝ`,
then for every `x : Fin n → ℝ` we have
`(ρ/2) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (K *ᵥ x)`.

This is the algebraic content of "PSD difference" in real inner-product
form: `K - (ρ/2) • 1` being PSD means
`0 ≤ x ⬝ᵥ ((K - (ρ/2) • 1) *ᵥ x) = x ⬝ᵥ (K *ᵥ x) - (ρ/2) * (x ⬝ᵥ x)`.
-/
lemma quadForm_lb_of_loewner_coercive
    {K : Matrix (Fin n) (Fin n) ℝ} {ρ : ℝ}
    (hK : (ρ / 2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ K)
    (x : Fin n → ℝ) :
    (ρ / 2) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (K *ᵥ x) := by
  -- `K - (ρ/2) • 1` is positive semidefinite.
  have hPSD : (K - (ρ / 2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hK)
  -- For real vectors, `star x = x`.
  have h_nn : 0 ≤ star x ⬝ᵥ
      ((K - (ρ / 2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x) :=
    hPSD.dotProduct_mulVec_nonneg x
  -- Rewrite `star x = x` (real), split the mulVec / dotProduct.
  have h_star : (star x : Fin n → ℝ) = x := by funext i; simp
  rw [h_star] at h_nn
  -- `(K - c • 1) *ᵥ x = K *ᵥ x - c • x`.
  have h_split :
      (K - (ρ / 2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x
        = K *ᵥ x - (ρ / 2 : ℝ) • x := by
    rw [Matrix.sub_mulVec]
    congr 1
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [h_split, dotProduct_sub] at h_nn
  -- `x ⬝ᵥ ((ρ/2) • x) = (ρ/2) * (x ⬝ᵥ x)`.
  have h_smul : x ⬝ᵥ ((ρ / 2 : ℝ) • x) = (ρ / 2) * (x ⬝ᵥ x) := by
    rw [dotProduct_smul]
    rfl
  rw [h_smul] at h_nn
  linarith

/-! ### Main theorem: exponential Grönwall decay -/

/-- **Grönwall exponential residual decay for the linearized NTK
gradient flow.**

Given:
* a (parametric) time-varying real symmetric kernel
  `K : ℝ → Matrix (Fin n) (Fin n) ℝ` with `K t` Hermitian for all `t`;
* a Loewner coercivity floor `(ρ / 2) • 1 ≤ K t` with `0 < ρ`;
* a residual trajectory `r : ℝ → EuclideanSpace ℝ (Fin n)` that is
  differentiable;
* the linear ODE relation `deriv r t = -toLp 2 ((K t) *ᵥ ofLp (r t))`;

then for every `T ≥ 0` the residual decays exponentially in norm:

  `‖r T‖² ≤ ‖r 0‖² · exp(-ρ · T)`.

This is the deterministic core of NTK lazy-training convergence. The
bootstrap argument in the surrounding NTK pipeline guarantees that the
empirical NTK along the trajectory stays close enough to its
initialization to inherit the coercivity floor — once that is in hand,
the present lemma supplies the exponential decay. -/
theorem ntk_residual_gronwall_decay
    {n : ℕ}
    (K : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (_hK_herm : ∀ t, (K t).IsHermitian)
    {ρ : ℝ} (_hρ_pos : 0 < ρ)
    (hK_coercive :
      ∀ t, (ρ / 2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ K t)
    (r : ℝ → EuclideanSpace ℝ (Fin n))
    (hr_diff : Differentiable ℝ r)
    (hr_ODE :
      ∀ t, deriv r t
        = -(WithLp.toLp 2 ((K t) *ᵥ (WithLp.ofLp (r t)))))
    (T : ℝ) (hT : 0 ≤ T) :
    ‖r T‖ ^ 2 ≤ ‖r 0‖ ^ 2 * Real.exp (-(ρ * T)) := by
  -- Lyapunov function V(t) := ‖r t‖².
  set V : ℝ → ℝ := fun t => ‖r t‖ ^ 2 with hV_def
  -- Auxiliary function g(t) := V(t) · exp(ρ · t).
  set g : ℝ → ℝ := fun t => V t * Real.exp (ρ * t) with hg_def
  -- Step 1: pointwise derivatives.
  -- HasDerivAt for r at t: from differentiability of r.
  have hr_hda : ∀ t, HasDerivAt r (deriv r t) t :=
    fun t => (hr_diff t).hasDerivAt
  -- HasDerivAt for V at t: 2 * ⟨r t, deriv r t⟩.
  have hV_hda :
      ∀ t, HasDerivAt V (2 * ⟪r t, deriv r t⟫_ℝ) t := by
    intro t
    have := (hr_hda t).norm_sq
    -- HasDerivAt (fun s => ‖r s‖^2) (2 * ⟪r t, deriv r t⟫) t
    exact this
  -- HasDerivAt for the exponential factor: ρ · exp(ρ t).
  have hexp_hda :
      ∀ t, HasDerivAt (fun s => Real.exp (ρ * s)) (ρ * Real.exp (ρ * t)) t := by
    intro t
    have h1 : HasDerivAt (fun s => ρ * s) ρ t := by
      simpa using ((hasDerivAt_id t).const_mul ρ)
    have h2 : HasDerivAt (fun s => Real.exp (ρ * s))
        (Real.exp (ρ * t) * ρ) t :=
      (Real.hasDerivAt_exp (ρ * t)).comp t h1
    have : Real.exp (ρ * t) * ρ = ρ * Real.exp (ρ * t) := by ring
    rw [this] at h2
    exact h2
  -- HasDerivAt for g(t).
  have hg_hda :
      ∀ t, HasDerivAt g
        (2 * ⟪r t, deriv r t⟫_ℝ * Real.exp (ρ * t)
          + V t * (ρ * Real.exp (ρ * t))) t := by
    intro t
    exact (hV_hda t).mul (hexp_hda t)
  -- Step 2: derivative of g(t) is ≤ 0 everywhere.
  -- We show: 2 * ⟨r t, deriv r t⟩ + ρ * V t ≤ 0, then multiply by exp(ρt) > 0.
  have h_inner_eq : ∀ t,
      ⟪r t, deriv r t⟫_ℝ = -((WithLp.ofLp (r t)) ⬝ᵥ ((K t) *ᵥ (WithLp.ofLp (r t)))) := by
    intro t
    rw [hr_ODE t]
    -- ⟨r t, -toLp 2 (K t *ᵥ ofLp (r t))⟩_ℝ = -⟨r t, toLp 2 (K t *ᵥ ofLp (r t))⟩
    rw [inner_neg_right]
    -- inner = ofLp (toLp ..) ⬝ᵥ star (ofLp (r t)) over reals.
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    -- star x = x for real vectors; dotProduct is symmetric.
    have h_star : (star (WithLp.ofLp (r t)) : Fin n → ℝ) = WithLp.ofLp (r t) := by
      funext i; simp
    rw [h_star]
    -- ofLp (toLp 2 y) = y.
    have h_simp :
        WithLp.ofLp (WithLp.toLp 2 ((K t) *ᵥ WithLp.ofLp (r t)))
          = (K t) *ᵥ WithLp.ofLp (r t) := WithLp.ofLp_toLp _ _
    rw [h_simp]
    -- dotProduct symmetric.
    rw [dotProduct_comm]
  have h_V_eq : ∀ t, V t = (WithLp.ofLp (r t)) ⬝ᵥ (WithLp.ofLp (r t)) := by
    intro t
    -- ‖r t‖² = ⟨r t, r t⟩_ℝ over ℝ, and that equals ofLp r t ⬝ᵥ ofLp r t.
    simp only [hV_def]
    rw [← real_inner_self_eq_norm_sq]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    have h_star : (star (WithLp.ofLp (r t)) : Fin n → ℝ) = WithLp.ofLp (r t) := by
      funext i; simp
    rw [h_star, dotProduct_comm]
  -- Pointwise: 2 * ⟨r t, deriv r t⟩ + ρ * V t ≤ 0.
  have h_lin_le_zero : ∀ t,
      2 * ⟪r t, deriv r t⟫_ℝ + ρ * V t ≤ 0 := by
    intro t
    rw [h_inner_eq t, h_V_eq t]
    -- 2 * (-(x ⬝ᵥ (K t *ᵥ x))) + ρ * (x ⬝ᵥ x) = ρ * (x ⬝ᵥ x) - 2 * (x ⬝ᵥ (K t *ᵥ x))
    set x : Fin n → ℝ := WithLp.ofLp (r t) with hx_def
    have hquad : (ρ / 2) * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((K t) *ᵥ x) :=
      quadForm_lb_of_loewner_coercive (hK_coercive t) x
    -- ρ * (x ⬝ᵥ x) ≤ 2 * (x ⬝ᵥ (K t *ᵥ x))
    have h2 : ρ * (x ⬝ᵥ x) ≤ 2 * (x ⬝ᵥ ((K t) *ᵥ x)) := by linarith
    linarith
  -- Derivative of g is ≤ 0 everywhere (multiply by exp(ρ t) > 0).
  have h_g_deriv_nonpos : ∀ t, deriv g t ≤ 0 := by
    intro t
    -- Use the HasDerivAt expression for g.
    have hgda := hg_hda t
    have hg_deriv_eq : deriv g t
        = 2 * ⟪r t, deriv r t⟫_ℝ * Real.exp (ρ * t)
          + V t * (ρ * Real.exp (ρ * t)) := hgda.deriv
    rw [hg_deriv_eq]
    -- Rewrite: A * E + V * (ρ * E) = (A + ρ * V) * E with A = 2 * ⟨..⟩.
    set A : ℝ := 2 * ⟪r t, deriv r t⟫_ℝ
    have hrw : A * Real.exp (ρ * t) + V t * (ρ * Real.exp (ρ * t))
        = (A + ρ * V t) * Real.exp (ρ * t) := by ring
    rw [hrw]
    -- (A + ρ * V t) ≤ 0 and Real.exp .. > 0, so product ≤ 0.
    have h_le : A + ρ * V t ≤ 0 := h_lin_le_zero t
    have h_exp_pos : 0 < Real.exp (ρ * t) := Real.exp_pos _
    exact mul_nonpos_of_nonpos_of_nonneg h_le h_exp_pos.le
  -- Step 3: g is differentiable everywhere.
  have hg_diff : Differentiable ℝ g := by
    intro t
    exact (hg_hda t).differentiableAt
  -- Step 4: g is antitone (since deriv g ≤ 0).
  have hg_anti : Antitone g :=
    antitone_of_deriv_nonpos hg_diff h_g_deriv_nonpos
  -- Step 5: g T ≤ g 0.
  have hgT_le_g0 : g T ≤ g 0 := hg_anti hT
  -- g 0 = V 0 * exp 0 = V 0.
  have hg0 : g 0 = V 0 := by
    simp [hg_def, Real.exp_zero]
  -- g T = V T * exp(ρ T).
  have hgT : g T = V T * Real.exp (ρ * T) := by
    simp [hg_def]
  rw [hg0, hgT] at hgT_le_g0
  -- So V T * exp(ρ T) ≤ V 0.
  -- Divide by exp(ρ T) > 0: V T ≤ V 0 * exp(-ρ T).
  have h_exp_pos : 0 < Real.exp (ρ * T) := Real.exp_pos _
  have h_exp_ne : Real.exp (ρ * T) ≠ 0 := ne_of_gt h_exp_pos
  -- V T ≤ V 0 / exp(ρ T) = V 0 * exp(-(ρ T)).
  have h_le_div : V T ≤ V 0 / Real.exp (ρ * T) :=
    (le_div_iff₀ h_exp_pos).mpr hgT_le_g0
  -- Express the RHS as `V 0 * exp(-(ρ T))`.
  have h_div_eq : V 0 / Real.exp (ρ * T) = V 0 * Real.exp (-(ρ * T)) := by
    rw [Real.exp_neg, div_eq_mul_inv]
  rw [h_div_eq] at h_le_div
  -- Translate V to ‖r ·‖^2.
  simpa only [hV_def] using h_le_div

end LTFP
