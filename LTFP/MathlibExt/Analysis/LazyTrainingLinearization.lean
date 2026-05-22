/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Positivity

/-!
# Lazy training linearization: deterministic Taylor sub-step

A small deterministic algebraic reduction inside Bach (2024) §12.4 lazy
training analysis: given a parameter-movement bound `‖θt - θ₀‖ ≤ A/√m`
and a uniform first-order Taylor remainder `|f(θt;x) - f(θ₀;x) -
⟨∇f(θ₀;x), θt - θ₀⟩| ≤ (L/2)‖θt - θ₀‖²`, the linearization error is
bounded by `(L/2) · (A/√m)²`.

This is the deterministic final reduction inside B8 N5
(`lazy-training-linearization`). The probabilistic NTK / lazy-regime
machinery that produces `hmove` and `htaylor` themselves is still open
and DEFERRED_UPSTREAM (random-matrix concentration + uniform real
analysis around random initialization).
-/

open scoped RealInnerProductSpace

namespace LTFP.MathlibExt.Analysis

/-- Deterministic reduction from movement + Taylor bound to lazy
linearization-error bound. -/
theorem lazy_training_linearization_from_taylor
    {p : ℕ} {X : Type*}
    (f : EuclideanSpace ℝ (Fin p) → X → ℝ)
    (θ₀ θt : EuclideanSpace ℝ (Fin p))
    (grad₀ : X → EuclideanSpace ℝ (Fin p))
    (m : ℕ) (A L : ℝ)
    (hm : 0 < m) (hA : 0 ≤ A) (hL : 0 ≤ L)
    (hmove : ‖θt - θ₀‖ ≤ A / Real.sqrt (m : ℝ))
    (htaylor : ∀ x : X,
      |f θt x - (f θ₀ x + inner ℝ (grad₀ x) (θt - θ₀))|
        ≤ (L / 2) * ‖θt - θ₀‖ ^ 2) :
    ∀ x : X,
      |f θt x - (f θ₀ x + inner ℝ (grad₀ x) (θt - θ₀))|
        ≤ (L / 2) * (A / Real.sqrt (m : ℝ)) ^ 2 := by
  intro x
  have hm_real_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsqrt_pos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm_real_pos
  have hR_nonneg : 0 ≤ A / Real.sqrt (m : ℝ) :=
    div_nonneg hA (le_of_lt hsqrt_pos)
  have hnorm_sq_le : ‖θt - θ₀‖ ^ 2 ≤ (A / Real.sqrt (m : ℝ)) ^ 2 := by
    exact sq_le_sq' (by linarith [norm_nonneg (θt - θ₀)]) hmove
  have hcoef_nonneg : 0 ≤ L / 2 := by positivity
  exact le_trans (htaylor x)
    (mul_le_mul_of_nonneg_left hnorm_sq_le hcoef_nonneg)

/-- Lazy-regime event subset: if `ω` is in the event "movement bounded ∧
Taylor remainder bounded", then `ω` is in the event "linearization error
bounded by the quadratic lazy scale". Composes the deterministic Taylor
sub-step pointwise. -/
theorem lazy_training_linearization_event_subset
    {Ω : Type*} {p : ℕ} {X : Type*}
    (f : EuclideanSpace ℝ (Fin p) → X → ℝ)
    (θ₀ θt : Ω → EuclideanSpace ℝ (Fin p))
    (grad₀ : Ω → X → EuclideanSpace ℝ (Fin p))
    (m : ℕ) (A L : ℝ)
    (hm : 0 < m) (hA : 0 ≤ A) (hL : 0 ≤ L) :
    {ω : Ω | ‖θt ω - θ₀ ω‖ ≤ A / Real.sqrt (m : ℝ) ∧
      ∀ x : X, |f (θt ω) x -
        (f (θ₀ ω) x + inner ℝ (grad₀ ω x) (θt ω - θ₀ ω))|
          ≤ (L / 2) * ‖θt ω - θ₀ ω‖ ^ 2}
      ⊆
    {ω : Ω | ∀ x : X, |f (θt ω) x -
      (f (θ₀ ω) x + inner ℝ (grad₀ ω x) (θt ω - θ₀ ω))|
        ≤ (L / 2) * (A / Real.sqrt (m : ℝ)) ^ 2} := by
  intro ω hω
  exact lazy_training_linearization_from_taylor f (θ₀ ω) (θt ω) (grad₀ ω) m A L
    hm hA hL hω.1 hω.2

end LTFP.MathlibExt.Analysis
