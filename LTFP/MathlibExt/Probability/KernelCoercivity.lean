/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Data.Matrix.Mul
import LTFP.MathlibExt.Probability.NTKConcentration

/-!
# Coercivity transfer between population and empirical NTK
(B8 N5 / N6 shared dynamics, I5)

For the lazy-training analysis of one-hidden-layer networks, the
**population NTK** `K = E_ν[neuronNTK]` is typically assumed to be
*coercive*: there exists `κ > 0` such that

  `κ · ‖r‖² ≤ rᵀ · K · r`  for every `r ∈ ℝⁿ`.

The downstream lazy-training analysis needs the *empirical* NTK
`K̂_m` to inherit a comparable coercivity constant. This is a
deterministic transfer step on the **good event** where the
empirical-to-population deviation is small in `l²` operator norm
(supplied by the concentration result
`empiricalNTK_opNorm_concentration_param` in
`LTFP/MathlibExt/Probability/NTKConcentration.lean`).

## Main definitions

* `KernelCoercive κ K` — coercivity of a real `n × n` matrix `K`
  with constant `κ` over `EuclideanSpace ℝ (Fin n)` (so that the
  norm `‖r‖` is the `l²` norm).

## Main results

* `empirical_coercive_of_population_and_close` — if the population
  NTK is `κ`-coercive and the empirical NTK is within `κ / 2` of the
  population NTK in `l²` operator norm, then the empirical NTK is
  `κ / 2`-coercive. This is the deterministic coercivity transfer
  step consumed by the B8 N5 / N6 shared lazy-training dynamics.

## Proof outline

For a fixed `r : EuclideanSpace ℝ (Fin n)`, write
`Δ := K̂_m − K`. The quadratic form splits linearly via
`Matrix.add_mulVec` and `Matrix.dotProduct_add`:

  `rᵀ · K̂_m · r = rᵀ · K · r + rᵀ · Δ · r`.

The population coercivity `hpop r` gives the first summand
`≥ κ · ‖r‖²`. The Cauchy–Schwarz inequality together with the `l²`
operator-norm bound `Matrix.l2_opNorm_mulVec` and the closeness
hypothesis `‖Δ‖ ≤ κ / 2` bounds the cross-term:

  `|rᵀ · Δ · r| ≤ ‖Δ‖ · ‖r‖² ≤ (κ / 2) · ‖r‖²`.

Combining yields `rᵀ · K̂_m · r ≥ (κ / 2) · ‖r‖²` as required.
-/

namespace ProbabilityTheory

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open Matrix WithLp

/-- **Coercivity of a real symmetric `n × n` matrix.**

We say a real matrix `K : Matrix (Fin n) (Fin n) ℝ` is **coercive**
with constant `κ > 0` if the associated quadratic form satisfies
`κ · ‖r‖² ≤ rᵀ · K · r` for every `r ∈ EuclideanSpace ℝ (Fin n)`.

The vector `r` is taken in `EuclideanSpace ℝ (Fin n)` so that the
norm `‖r‖` is the genuine `l²` norm; on plain `Fin n → ℝ` the
default norm is the supremum norm, which gives the wrong semantics
for this inequality. -/
def KernelCoercive {n : ℕ} (κ : ℝ) (K : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ r : EuclideanSpace ℝ (Fin n),
    κ * ‖r‖ ^ 2 ≤ dotProduct (ofLp r) (K *ᵥ ofLp r)

/-- **Coercivity transfer: empirical-from-population.**

Let `K` be the population NTK and `K̂_m` the empirical NTK on a
fixed input set `xs` with iid sample `ω`. If `K` is `κ`-coercive
and `K̂_m` is within `κ / 2` of `K` in the `l²` operator norm,
then `K̂_m` is `κ / 2`-coercive.

This is a deterministic algebraic fact that holds on the good event
of the NTK concentration bound; the concentration side is supplied
by `empiricalNTK_opNorm_concentration_param`. -/
theorem empirical_coercive_of_population_and_close
    {σ : ℝ → ℝ} {d n m : ℕ}
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ)
    (ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ))
    {κ : ℝ} (_hκ : 0 < κ)
    (hpop : KernelCoercive κ (populationNTK σ xs ν))
    (hclose :
      ‖empiricalNTK σ xs ω - populationNTK σ xs ν‖ ≤ κ / 2) :
    KernelCoercive (κ / 2) (empiricalNTK σ xs ω) := by
  -- Abbreviate K = population, K̂ = empirical, Δ = K̂ - K.
  set K : Matrix (Fin n) (Fin n) ℝ := populationNTK σ xs ν with hK_def
  set Khat : Matrix (Fin n) (Fin n) ℝ := empiricalNTK σ xs ω with hKhat_def
  set Δ : Matrix (Fin n) (Fin n) ℝ := Khat - K with hΔ_def
  intro r
  -- The closeness hypothesis, rephrased in terms of Δ.
  have hΔ_le : ‖Δ‖ ≤ κ / 2 := by
    have : ‖Δ‖ = ‖empiricalNTK σ xs ω - populationNTK σ xs ν‖ := by
      simp [hΔ_def, hKhat_def, hK_def]
    rw [this]; exact hclose
  -- Decompose: K̂ = K + Δ.
  have hKhat_eq : Khat = K + Δ := by
    simp [hΔ_def]
  -- Split the quadratic form.
  have hquad_split :
      dotProduct (ofLp r) (Khat *ᵥ ofLp r)
        = dotProduct (ofLp r) (K *ᵥ ofLp r)
          + dotProduct (ofLp r) (Δ *ᵥ ofLp r) := by
    rw [hKhat_eq, add_mulVec, dotProduct_add]
  -- Population coercivity bound on the K-quadratic form.
  have hpop_r : κ * ‖r‖ ^ 2 ≤ dotProduct (ofLp r) (K *ᵥ ofLp r) :=
    hpop r
  -- Cauchy-Schwarz: relate the Δ-quadratic form to ‖Δ‖ * ‖r‖^2.
  -- We use the inner product on EuclideanSpace and identify it with
  -- dotProduct via EuclideanSpace.inner_eq_star_dotProduct (over ℝ).
  have hCS : |dotProduct (ofLp r) (Δ *ᵥ ofLp r)| ≤ ‖Δ‖ * ‖r‖ ^ 2 := by
    -- Define s : EuclideanSpace ℝ (Fin n) as toLp 2 (Δ *ᵥ ofLp r).
    set s : EuclideanSpace ℝ (Fin n) := toLp 2 (Δ *ᵥ ofLp r) with hs_def
    -- Inner product of r with s = dotProduct (ofLp r) (Δ *ᵥ ofLp r).
    have h_inner_eq :
        inner ℝ r s = dotProduct (ofLp r) (Δ *ᵥ ofLp r) := by
      -- EuclideanSpace.inner_eq_star_dotProduct: ⟪x, y⟫ = ofLp y ⬝ᵥ star (ofLp x)
      -- Over ℝ, star = id; and dotProduct is symmetric.
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      simp [hs_def, ofLp_toLp, star_trivial, dotProduct_comm]
    -- Cauchy-Schwarz on EuclideanSpace ℝ (Fin n).
    have h_cs : |inner ℝ r s| ≤ ‖r‖ * ‖s‖ := abs_real_inner_le_norm r s
    -- Operator-norm bound: ‖s‖ = ‖toLp 2 (Δ *ᵥ ofLp r)‖ ≤ ‖Δ‖ * ‖r‖.
    have h_op : ‖s‖ ≤ ‖Δ‖ * ‖r‖ := by
      -- `l2_opNorm_mulVec` gives the bound for the vector wrapped via
      -- `(EuclideanSpace.equiv _ _).symm`, which is definitionally toLp 2.
      have := Matrix.l2_opNorm_mulVec Δ r
      -- The norm on EuclideanSpace coincides with toLp 2's norm.
      simpa [hs_def, EuclideanSpace.equiv] using this
    have h_norm_r_nn : (0 : ℝ) ≤ ‖r‖ := norm_nonneg r
    have h_chain : |inner ℝ r s| ≤ ‖r‖ * (‖Δ‖ * ‖r‖) := by
      refine h_cs.trans ?_
      exact mul_le_mul_of_nonneg_left h_op h_norm_r_nn
    rw [h_inner_eq] at h_chain
    -- Reorganize: ‖r‖ * (‖Δ‖ * ‖r‖) = ‖Δ‖ * ‖r‖^2.
    have hrw : ‖r‖ * (‖Δ‖ * ‖r‖) = ‖Δ‖ * ‖r‖ ^ 2 := by ring
    rw [hrw] at h_chain
    exact h_chain
  -- The lower bound on the Δ-quadratic form follows from the absolute
  -- value bound: -|x| ≤ x.
  have hΔ_quad_lb :
      -(‖Δ‖ * ‖r‖ ^ 2) ≤ dotProduct (ofLp r) (Δ *ᵥ ofLp r) := by
    have := neg_le_of_abs_le hCS
    linarith
  -- Weaken via hΔ_le and sq_nonneg ‖r‖.
  have hr_sq_nn : 0 ≤ ‖r‖ ^ 2 := sq_nonneg ‖r‖
  have h_weaken : -((κ / 2) * ‖r‖ ^ 2) ≤ -(‖Δ‖ * ‖r‖ ^ 2) := by
    have := mul_le_mul_of_nonneg_right hΔ_le hr_sq_nn
    linarith
  -- Assemble.
  have h_final :
      (κ / 2) * ‖r‖ ^ 2
        ≤ dotProduct (ofLp r) (Khat *ᵥ ofLp r) := by
    rw [hquad_split]
    have h1 : κ * ‖r‖ ^ 2 + -((κ / 2) * ‖r‖ ^ 2) = (κ / 2) * ‖r‖ ^ 2 := by ring
    have h2 :
        (κ / 2) * ‖r‖ ^ 2
          ≤ dotProduct (ofLp r) (K *ᵥ ofLp r)
              + dotProduct (ofLp r) (Δ *ᵥ ofLp r) := by
      have := add_le_add hpop_r
        (le_trans h_weaken hΔ_quad_lb)
      linarith
    exact h2
  exact h_final

end ProbabilityTheory
