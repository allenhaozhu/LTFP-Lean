/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Two-point Bayes-risk lower bound (algebraic core)

Proposed Mathlib path: `Mathlib/Statistics/LowerBounds/TwoPointBayes.lean`.
Proposed Mathlib namespace: `Statistics`.

This module lands the **algebraic core** of the two-point Bayes-risk
lower bound used in Le Cam's method (cf. Tsybakov, *Introduction to
Nonparametric Estimation*, Ch. 2; Wainwright, *High-Dimensional
Statistics*, Ch. 15). Given a binary parameter set `{θ₀, θ₁}` with
squared-loss separation `Δ²` and a hypothesis-testing total-variation
distance `tv = TV(P₀, P₁) ∈ [0, 1]`, the Bayes risk under the
uniform prior `π = (δ_{θ₀} + δ_{θ₁}) / 2` of any estimator `A` satisfies

`BayesRisk(A, π) = (𝔼_{P₀}[ℓ(A, θ₀)] + 𝔼_{P₁}[ℓ(A, θ₁)]) / 2`
`              ≥ (Δ² / 2) · (1 - tv) / 2`
`              = (Δ² / 4) · (1 - tv)`.

The right-hand side is the **two-point Bayes-risk lower bound**. This
file formalizes its algebraic content, treating the *per-θ risk values*
`R₀ = 𝔼_{P₀}[ℓ(A, θ₀)]` and `R₁ = 𝔼_{P₁}[ℓ(A, θ₁)]` as real parameters
and isolating the algebraic chain

`(R₀ + R₁) / 2 ≥ (Δ²/4) · (1 - tv)`  ⟹  `max R₀ R₁ ≥ (Δ²/4) · (1 - tv)`.

The first inequality is the Le Cam two-point hypothesis-testing bound
(packaged here as a hypothesis on `R₀ + R₁`, since the testing-affinity
identity is currently outside Mathlib's surface). The second inequality
is the trivial *average ≤ max* observation. Together they discharge the
"sup over hypotheses dominates the two-point Bayes-risk bound" step in
the Le Cam minimax-lower-bound derivation.

## Main definitions

* `Statistics.twoPointBayesRiskBound Δsq tv` — the scalar two-point
  Bayes-risk lower bound `(Δsq / 4) · (1 - tv)`. It depends only on the
  squared loss separation `Δsq` and the total-variation distance `tv`.

## Main results

* `Statistics.twoPointBayesRiskBound_nonneg` — the two-point Bayes-risk
  bound is nonnegative for `0 ≤ Δsq` and `tv ≤ 1`.
* `Statistics.twoPointBayesRiskBound_le_quarter_delta_sq` — the bound is
  dominated by `Δsq / 4`, the maximally-informative limit at `tv = 0`.
* `Statistics.twoPointBayesRiskBound_antitone_tv` — antitonicity in `tv`:
  as the two distributions become more distinguishable (larger TV) the
  bound shrinks.
* `Statistics.twoPointBayesRiskBound_mono_delta_sq` — monotonicity in the
  squared loss separation: farther-apart hypotheses give a stronger
  bound.
* `Statistics.average_le_max_of_pair` — algebraic core of "sup over
  hypotheses dominates the prior average": for any two real risk values,
  `(R₀ + R₁) / 2 ≤ max R₀ R₁`.
* `Statistics.max_ge_twoPointBayesRiskBound_of_average_ge` — composite
  step: from the Le Cam *average-risk* lower bound
  `(R₀ + R₁) / 2 ≥ twoPointBayesRiskBound Δsq tv`, conclude
  `max R₀ R₁ ≥ twoPointBayesRiskBound Δsq tv`. This is the algebraic
  pivot inside the two-point minimax reduction.

## Composition with the rest of the LTFP Le Cam chain

This module composes with:

* `LTFP/MathlibExt/Probability/LeCam.lean` — the `leCamBound Δ tv` scalar
  (testing-error lower bound `Δ/2 · (1 - tv)`). The Bayes-risk bound
  here is the *squared-loss* analogue: factor of `Δ²/4` instead of
  `Δ/2`, because the loss is the squared distance and the optimal
  testing error is `1/2` (not `0`).
* `LTFP/MathlibExt/Probability/Distance/Pinsker.lean` — the
  `pinsker_inequality_tvDist` family, supplying `tv ≤ √(KL/2)` so the
  two-point Bayes-risk bound becomes `(Δ²/4) · (1 - √(KL/2))` once a
  closed-form KL gap between the hypothesis distributions is in scope.
* `LTFP/Ch03_LinearLeastSquares/FixedDesign.lean` — the
  `mourtada_two_point_testing_anchor` and the family of `ols_minimax_*`
  carriers. The two-point Bayes-risk bound is the missing algebraic
  step between `sup_ge_bayes_average` (already there for finite priors)
  and the testing-side `leCamBound` (already there for the
  hypothesis-testing surrogate).

## References

* L. Le Cam, *Convergence of Estimates Under Dimensionality Restrictions*,
  Annals of Statistics, vol. 1, no. 1, pp. 38–53, 1973.
* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer,
  2009, Section 2.2 (two-point method, Bayes-risk form).
* M. J. Wainwright, *High-Dimensional Statistics: A Non-Asymptotic
  Viewpoint*, Cambridge University Press, 2019, Chapter 15.
* F. Bach, *Learning Theory from First Principles*, MIT Press, 2024,
  §3.7 (Mourtada minimax lower bound for OLS), §15.1 (Le Cam method).

## Tags

Le Cam, minimax, lower bound, two-point method, Bayes risk, squared loss
-/

namespace LTFP.MathlibExt.Probability

-- When upstreamed, replace `LTFP.MathlibExt.Probability` by `Statistics`
-- throughout this file. All declarations are intended to live in the
-- `Statistics` namespace.

/-- The scalar **two-point Bayes-risk lower bound** as a function of the
squared loss separation `Δsq = ‖θ₀ - θ₁‖²` and the total-variation
distance `tv = TV(P₀, P₁)` between the two hypothesis measures:

`twoPointBayesRiskBound Δsq tv = (Δsq / 4) * (1 - tv)`.

This is the right-hand side of the squared-loss form of Le Cam's
two-point inequality:

`inf_T (𝔼_{P₀} ℓ(T, θ₀) + 𝔼_{P₁} ℓ(T, θ₁)) / 2 ≥ (Δsq / 4) · (1 - TV(P₀, P₁))`,

where `ℓ(t, θ) = ‖t - θ‖²` is the squared-loss. The factor `Δsq/4`
(as opposed to `Δ/2` in `leCamBound` for testing error) arises from
the polarization identity for squared loss: any estimator `T` must
"pay" at least `Δsq/4` on at least one of the two hypotheses, scaled
by the testing-error guarantee `(1 - tv)/2` from the
hypothesis-distinguishability side. -/
noncomputable def twoPointBayesRiskBound (Δsq tv : ℝ) : ℝ :=
  Δsq / 4 * (1 - tv)

/-- Nonnegativity of the two-point Bayes-risk lower bound: if
`0 ≤ Δsq` (squared distance is nonneg) and `tv ≤ 1` (TV distance is at
most `1`), then `0 ≤ twoPointBayesRiskBound Δsq tv`. -/
theorem twoPointBayesRiskBound_nonneg
    {Δsq tv : ℝ} (hΔ : 0 ≤ Δsq) (htv : tv ≤ 1) :
    0 ≤ twoPointBayesRiskBound Δsq tv := by
  unfold twoPointBayesRiskBound
  have hquarter : 0 ≤ Δsq / 4 := by linarith
  have hone_sub_nn : 0 ≤ 1 - tv := by linarith
  exact mul_nonneg hquarter hone_sub_nn

/-- The two-point Bayes-risk bound is dominated by `Δsq / 4`, which is
the maximally-informative limit reached at `tv = 0` (indistinguishable
hypotheses). For `0 ≤ Δsq` and `0 ≤ tv`, the bound shrinks below this
ceiling whenever `tv > 0`. -/
theorem twoPointBayesRiskBound_le_quarter_delta_sq
    {Δsq tv : ℝ} (hΔ : 0 ≤ Δsq) (htv : 0 ≤ tv) :
    twoPointBayesRiskBound Δsq tv ≤ Δsq / 4 := by
  unfold twoPointBayesRiskBound
  have hquarter : 0 ≤ Δsq / 4 := by linarith
  have hone_sub_le : 1 - tv ≤ 1 := by linarith
  calc Δsq / 4 * (1 - tv)
      ≤ Δsq / 4 * 1 := mul_le_mul_of_nonneg_left hone_sub_le hquarter
    _ = Δsq / 4 := by ring

/-- Antitonicity in the total-variation distance: for fixed `0 ≤ Δsq`,
the map `tv ↦ twoPointBayesRiskBound Δsq tv = (Δsq/4) · (1 - tv)` is
antitone. As the two hypotheses become more distinguishable (larger
`tv`) the guaranteed Bayes-risk lower bound shrinks. -/
theorem twoPointBayesRiskBound_antitone_tv
    {Δsq : ℝ} (hΔ : 0 ≤ Δsq) :
    Antitone (fun tv : ℝ => twoPointBayesRiskBound Δsq tv) := by
  intro tv₁ tv₂ htv
  unfold twoPointBayesRiskBound
  have hquarter : 0 ≤ Δsq / 4 := by linarith
  have hone_sub_le : 1 - tv₂ ≤ 1 - tv₁ := by linarith
  exact mul_le_mul_of_nonneg_left hone_sub_le hquarter

/-- Monotonicity in the squared loss separation: for fixed `tv ≤ 1`,
the map `Δsq ↦ twoPointBayesRiskBound Δsq tv = (Δsq/4) · (1 - tv)`
is monotone. Farther-apart hypotheses give a stronger Bayes-risk
lower bound. -/
theorem twoPointBayesRiskBound_mono_delta_sq
    {tv : ℝ} (htv : tv ≤ 1) :
    Monotone (fun Δsq : ℝ => twoPointBayesRiskBound Δsq tv) := by
  intro Δ₁ Δ₂ hΔ
  unfold twoPointBayesRiskBound
  have hone_sub_nn : 0 ≤ 1 - tv := by linarith
  have hquot : Δ₁ / 4 ≤ Δ₂ / 4 := by linarith
  exact mul_le_mul_of_nonneg_right hquot hone_sub_nn

/-- The two-point Bayes-risk bound vanishes exactly when the two
hypotheses are totally separated (`tv = 1`), provided the squared loss
separation is strictly positive. When `Δsq = 0` the bound is identically
zero and the characterization is trivial. -/
theorem twoPointBayesRiskBound_eq_zero_iff
    {Δsq tv : ℝ} (hΔ : 0 < Δsq) :
    twoPointBayesRiskBound Δsq tv = 0 ↔ tv = 1 := by
  unfold twoPointBayesRiskBound
  have hquarter_ne : Δsq / 4 ≠ 0 := by
    have : 0 < Δsq / 4 := by linarith
    exact ne_of_gt this
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' : 1 - tv = 0 := by
      rcases mul_eq_zero.mp h with h₁ | h₂
      · exact absurd h₁ hquarter_ne
      · exact h₂
    linarith
  · rw [h]; ring

/-- **Algebraic core of "sup over hypotheses dominates the prior
average"** (uniform-on-{θ₀, θ₁} prior special case). For any two real
risk values `R₀, R₁`, the average is at most the maximum:

`(R₀ + R₁) / 2 ≤ max R₀ R₁`.

This is the binary-prior case of `sup_ge_bayes_average` in
`LTFP/Ch03_LinearLeastSquares/FixedDesign.lean`, specialized to two
points (no Fintype Nonempty plumbing needed). -/
theorem average_le_max_of_pair (R₀ R₁ : ℝ) :
    (R₀ + R₁) / 2 ≤ max R₀ R₁ := by
  rcases le_total R₀ R₁ with h | h
  · have hmax : max R₀ R₁ = R₁ := max_eq_right h
    rw [hmax]
    linarith
  · have hmax : max R₀ R₁ = R₀ := max_eq_left h
    rw [hmax]
    linarith

/-- **Composite step** in the two-point minimax reduction. Suppose the
Le Cam-style *average* Bayes-risk inequality has been established:

`(R₀ + R₁) / 2 ≥ twoPointBayesRiskBound Δsq tv`,

where `R₀ = 𝔼_{P₀}[ℓ(A, θ₀)]` and `R₁ = 𝔼_{P₁}[ℓ(A, θ₁)]` are the
per-hypothesis risks of an estimator `A`. Then the worst-case
(sup-over-{θ₀, θ₁}) risk also satisfies the same lower bound:

`max R₀ R₁ ≥ twoPointBayesRiskBound Δsq tv`.

This is the algebraic pivot inside the two-point minimax-lower-bound
argument: the Le Cam method produces the *average* bound on the LHS,
and this lemma converts it to a *worst-case-over-pair* bound, which
is what `ols_minimax_lower_bound_for_all_estimators` ultimately
consumes (with `{θ₀, θ₁}` substituted for the abstract parameter set
in the carrier's `h_twoPoint` hypothesis). -/
theorem max_ge_twoPointBayesRiskBound_of_average_ge
    {Δsq tv R₀ R₁ : ℝ}
    (h_avg : twoPointBayesRiskBound Δsq tv ≤ (R₀ + R₁) / 2) :
    twoPointBayesRiskBound Δsq tv ≤ max R₀ R₁ :=
  h_avg.trans (average_le_max_of_pair R₀ R₁)

/-! ### Examples

The two examples below pin down the boundary behaviour of
`twoPointBayesRiskBound`: at `tv = 0` the two hypotheses are
indistinguishable and the bound saturates at `Δsq / 4` (maximally
informative); at `tv = 1` the two hypotheses are totally separated and
the bound collapses to `0`. -/

section Examples

/-- At `tv = 0` (hypotheses indistinguishable in total variation), the
two-point Bayes-risk bound saturates at `Δsq / 4`, the maximum useful
value for a squared-loss separation of `Δsq`. -/
example (Δsq : ℝ) : twoPointBayesRiskBound Δsq 0 = Δsq / 4 := by
  unfold twoPointBayesRiskBound; ring

/-- At `tv = 1` (hypotheses totally separated), the two-point
Bayes-risk bound collapses to `0`: no minimax lower bound is guaranteed
by the binary-prior two-point method. -/
example (Δsq : ℝ) : twoPointBayesRiskBound Δsq 1 = 0 := by
  unfold twoPointBayesRiskBound; ring

end Examples

end LTFP.MathlibExt.Probability
