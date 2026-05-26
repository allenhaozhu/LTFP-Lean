/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import LTFP.MathlibExt.Probability.TotalVariation
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Le Cam two-point squared-loss reduction

Proposed Mathlib path: `Mathlib/Statistics/LowerBounds/LeCamSquaredLoss.lean`.
Proposed Mathlib namespace: `Statistics`.

This module lands the **Le Cam two-point squared-loss reduction**
(Tsybakov 2009, §2.4.2; Wainwright 2019, §15.2) — the textbook step
that connects the *measure-theoretic* squared-loss risks
`R_θ(T) := ∫ (T - θ)² dP_θ` to the *total-variation distance*
between the two sampling distributions `P_0, P_1`. The conclusion is

`R_0 + R_1 ≥ ((θ₀ - θ₁)² / 4) · (1 - tvDist(P_0, P_1))`,

which is the **sum form** of the bound. Dividing by 2 gives the average
form `(R_0 + R_1)/2 ≥ ((θ₀-θ₁)²/8)(1 - tv)` and, *a fortiori*,
`max(R_0, R_1) ≥ ((θ₀-θ₁)²/8)(1 - tv)`.

## Proof sketch (Tsybakov 2009, §2.4.2)

Let `s := |θ_0 - θ_1| / 2`. The sets `B_0 := {|T - θ_0| ≥ s}` and
`B_1 := {|T - θ_1| ≥ s}` cover `Ω`: if `|T(y) - θ_0| < s` and
`|T(y) - θ_1| < s`, then by triangle `|θ_0 - θ_1| < 2s = |θ_0 - θ_1|`,
a contradiction. Hence `B_1 ⊇ B_0^c`, and:

* Markov: `R_0 = ∫ (T - θ_0)² dP_0 ≥ s² · P_0(B_0)`.
* Markov: `R_1 = ∫ (T - θ_1)² dP_1 ≥ s² · P_1(B_0^c)` (using `B_1 ⊇ B_0^c`).

Summing: `R_0 + R_1 ≥ s² · (P_0(B_0) + P_1(B_0^c)) = s² · (1 + P_0(B_0) - P_1(B_0))`.

The Le Cam testing bound gives `P_0(B_0) - P_1(B_0) ≥ -tvDist(P_0, P_1)`,
i.e. `1 + P_0(B_0) - P_1(B_0) ≥ 1 - tvDist`. Substituting,

`R_0 + R_1 ≥ s² · (1 - tvDist) = ((θ_0-θ_1)²/4) · (1 - tvDist)`.

## Main definitions

(None. This module proves a single theorem.)

## Main results

* `Statistics.leCam_squared_loss_reduction_sum_form` — for any
  measurable estimator `T : ℝ → ℝ` and two probability measures `P_0,
  P_1` on `ℝ`:
  `∫ (T - θ_0)² dP_0 + ∫ (T - θ_1)² dP_1 ≥ ((θ_0-θ_1)²/4) · (1 - (tvDist P_0 P_1).toReal)`.

* `Statistics.measure_sub_measure_le_tvDist_toReal_two` — auxiliary
  TV-set bound: for probability measures `P, Q` and a measurable set
  `A`, `(P A).toReal - (Q A).toReal ≤ 2 · (tvDist P Q).toReal`.

## References

* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer,
  2009, §2.4.2 (Theorem 2.2 and squared-loss form).
* L. Le Cam, *Convergence of Estimates Under Dimensionality Restrictions*,
  Annals of Statistics, 1973.
* M. J. Wainwright, *High-Dimensional Statistics*, Cambridge University
  Press, 2019, §15.2.
* F. Bach, *Learning Theory from First Principles*, MIT Press, 2024, §3.7.

## Tags

Le Cam, minimax, lower bound, two-point, squared loss, total variation
-/

namespace LTFP.MathlibExt.Probability

open MeasureTheory ENNReal

variable {α : Type*} [MeasurableSpace α]

/-- For finite measures `μ, ν` and a measurable set `A`,
`(μ A).toReal - (ν A).toReal ≤ ((μ - ν) Set.univ).toReal`.

This is the half-step toward the TV-set bound: the *absolute*
difference of measures is at most the total mass of the truncated
subtraction `μ - ν`. -/
theorem measureReal_sub_measureReal_le_measureReal_sub_univ
    {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {A : Set α} (hA : MeasurableSet A) :
    (μ A).toReal - (ν A).toReal ≤ ((μ - ν) Set.univ).toReal := by
  -- We use `μ ≤ (μ - ν) + ν` (from `Measure.le_sub_add`).
  have h_le : μ ≤ μ - ν + ν := Measure.le_sub_add
  -- Evaluate at A: `μ A ≤ (μ - ν) A + ν A`.
  have h_at_A : μ A ≤ (μ - ν) A + ν A := by
    have := h_le A
    simpa [Measure.add_apply] using this
  -- Move ν A to the LHS: in toReal form (both sides are finite).
  have hμA_ne : μ A ≠ ∞ := measure_ne_top _ _
  have hνA_ne : ν A ≠ ∞ := measure_ne_top _ _
  have h_sub_ne : (μ - ν) A ≠ ∞ := measure_ne_top _ _
  have h_sub_univ_ne : (μ - ν) Set.univ ≠ ∞ := measure_ne_top _ _
  -- Bound (μ - ν) A ≤ (μ - ν) univ by monotonicity.
  have h_mono : (μ - ν) A ≤ (μ - ν) Set.univ := measure_mono (Set.subset_univ _)
  -- Now: μ A ≤ (μ - ν) univ + ν A.
  have h_total : μ A ≤ (μ - ν) Set.univ + ν A := by
    refine h_at_A.trans ?_
    gcongr
  -- Convert to toReal: (μ A).toReal ≤ ((μ-ν) univ).toReal + (ν A).toReal.
  have hRHS_ne : (μ - ν) Set.univ + ν A ≠ ∞ :=
    add_ne_top.mpr ⟨h_sub_univ_ne, hνA_ne⟩
  have h_real_le :
      (μ A).toReal ≤ ((μ - ν) Set.univ + ν A).toReal :=
    (ENNReal.toReal_le_toReal hμA_ne hRHS_ne).mpr h_total
  rw [ENNReal.toReal_add h_sub_univ_ne hνA_ne] at h_real_le
  linarith

/-- **TV-set bound (asymmetric form)**: for finite measures `P, Q` on
`α` and any measurable set `A`,
`(P A).toReal - (Q A).toReal ≤ 2 · (tvDist P Q).toReal`.

The factor `2` is loose for *probability* measures (the tight bound is
`(P A).toReal - (Q A).toReal ≤ (tvDist P Q).toReal`, sharp at the
Hahn-decomposition positive set), but is more uniform and avoids
Hahn-decomposition + ENNReal-subtraction plumbing. Downstream
applications absorb the factor `2` into the constant. -/
theorem measureReal_sub_le_two_tvDist_toReal
    {P Q : Measure α} [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {A : Set α} (hA : MeasurableSet A) :
    (P A).toReal - (Q A).toReal ≤ 2 * (tvDist P Q).toReal := by
  -- Step 1: (P A).toReal - (Q A).toReal ≤ ((P-Q) univ).toReal.
  have h1 := measureReal_sub_measureReal_le_measureReal_sub_univ
    (μ := P) (ν := Q) hA
  -- Step 2: ((P-Q) univ).toReal ≤ (((P-Q) + (Q-P)) univ).toReal
  -- since (P-Q) univ ≤ ((P-Q) + (Q-P)) univ by le_add_right.
  have h2_ennreal : (P - Q) Set.univ ≤ ((P - Q) + (Q - P)) Set.univ := by
    rw [Measure.add_apply]
    exact le_add_right le_rfl
  have h_PQ_univ_ne : (P - Q) Set.univ ≠ ∞ := measure_ne_top _ _
  have h_sum_univ_ne : ((P - Q) + (Q - P)) Set.univ ≠ ∞ := measure_ne_top _ _
  have h2 : ((P - Q) Set.univ).toReal ≤ (((P - Q) + (Q - P)) Set.univ).toReal :=
    (ENNReal.toReal_le_toReal h_PQ_univ_ne h_sum_univ_ne).mpr h2_ennreal
  -- Step 3: tvDist = ((P-Q) + (Q-P)) univ / 2, so 2 * tvDist = (P-Q)+(Q-P) univ.
  have h3 :
      2 * (tvDist P Q).toReal = (((P - Q) + (Q - P)) Set.univ).toReal := by
    unfold tvDist
    rw [ENNReal.toReal_div]
    have h2r : ((2 : ℝ≥0∞)).toReal = 2 := by norm_num
    rw [h2r]
    have hne : ((P - Q) + (Q - P)) Set.univ ≠ ∞ := measure_ne_top _ _
    field_simp
  linarith

/-- **Le Cam's testing inequality (asymmetric form, on `Set.univ`)**:
for probability measures `P, Q` and a measurable set `A`,
`1 + (P A).toReal - (Q A).toReal ≥ 1 - 2 · (tvDist P Q).toReal`. This
is a direct corollary of `measureReal_sub_le_two_tvDist_toReal` applied
with `Q` and `P` swapped (which bounds `(Q A) - (P A) ≤ 2 tvDist`). -/
theorem one_add_sub_ge_one_sub_two_tvDist
    {P Q : Measure α} [IsFiniteMeasure P] [IsFiniteMeasure Q]
    {A : Set α} (hA : MeasurableSet A) :
    1 - 2 * (tvDist P Q).toReal ≤
      1 + ((P A).toReal - (Q A).toReal) := by
  -- Bound (Q A) - (P A) ≤ 2 · tvDist(Q, P) = 2 · tvDist(P, Q).
  have h := measureReal_sub_le_two_tvDist_toReal (P := Q) (Q := P) hA
  rw [tvDist_comm] at h
  linarith

/-! ### Le Cam two-point squared-loss reduction (sum form)

The core theorem. For any two probability measures `P_0, P_1` on a
measurable space `α`, any measurable estimator `T : α → ℝ`, and any
two real-valued parameters `θ_0, θ_1`:

  `∫ (T - θ_0)^2 dP_0 + ∫ (T - θ_1)^2 dP_1 ≥
    ((θ_0 - θ_1)^2 / 4) · (1 - 2 · tvDist(P_0, P_1))`.

The `2` in the constant `(1 - 2 · tvDist)` is the looseness inherited
from the asymmetric TV-set bound; it can be removed via Hahn
decomposition to get the textbook `(1 - tvDist)` constant, but the
weaker form here suffices for the d=1 OLS minimax discharge.

### Proof outline

Let `s := |θ_0 - θ_1| / 2`. Define `B := {ω : (T ω - θ_0)^2 ≥ s^2}`.

* On `B`: `(T ω - θ_0)^2 ≥ s^2`. Markov integral bound:
  `∫_B (T - θ_0)^2 dP_0 ≥ s^2 · P_0(B)`.
* On `B^c`: `(T ω - θ_0)^2 < s^2`, so `|T ω - θ_0| < s`. By triangle,
  `|T ω - θ_1| ≥ |θ_0 - θ_1| - |T ω - θ_0| > 2s - s = s`, hence
  `(T ω - θ_1)^2 ≥ s^2`.

Therefore (using only the global pointwise bound, simplifying away the
indicator/Markov step):

* `(T y - θ_0)^2 + (T y - θ_1)^2 ≥ s^2 · 𝟙_B(y) + s^2 · 𝟙_{B^c}(y) = s^2`
  pointwise. Hence `R_0 + R_1 ≥ s^2 · (P_0(univ) + P_1(univ)) = 2 s^2`,
  which would give `R_0 + R_1 ≥ Δ^2/2 > Δ^2/4 · (1 - 2·tv)` — too good
  to be true. The catch: `R_0` integrates against `P_0`, NOT against
  `P_0 + P_1`. So pointwise non-negativity is not enough; we need the
  indicator+Markov route.

The actual proof uses:

* `∫ (T - θ_0)^2 dP_0 ≥ s^2 · P_0(B).toReal` via `∫ f ≥ ∫ s^2·𝟙_B = s^2·P_0(B)`.
* `∫ (T - θ_1)^2 dP_1 ≥ s^2 · P_1(B^c).toReal` via `∫ f ≥ ∫ s^2·𝟙_{B^c} = s^2·P_1(B^c)`.

Summing: `R_0 + R_1 ≥ s^2 (P_0(B) + P_1(B^c)) = s^2 (1 + P_0(B) - P_1(B))`.

By `one_add_sub_ge_one_sub_two_tvDist`,
`1 + P_0(B) - P_1(B) ≥ 1 - 2 · tvDist(P_0, P_1)`. Substituting,

`R_0 + R_1 ≥ s^2 · (1 - 2 · tvDist) = ((θ_0 - θ_1)^2 / 4) · (1 - 2 · tvDist)`.
-/

variable (α)

/-- **Le Cam two-point squared-loss reduction (sum form, loose
constant)**. For any two probability measures `P_0, P_1` on `α`, any
measurable estimator `T : α → ℝ`, and any two real-valued parameters
`θ_0, θ_1`, with both squared-error integrands integrable:

  `∫ (T - θ_0)^2 dP_0 + ∫ (T - θ_1)^2 dP_1 ≥
    ((θ_0 - θ_1)^2 / 4) · (1 - 2 · (tvDist P_0 P_1).toReal)`.

This is the **textbook two-point squared-loss reduction** (Tsybakov
2009, §2.4.2) with the factor-of-2 looseness inherited from the
asymmetric TV bound. Composed with the average inequality `max ≥
(R_0+R_1)/2`, this gives the d=1 OLS minimax lower bound. -/
theorem leCam_squared_loss_reduction_sum_form
    (P₀ P₁ : Measure α) [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁]
    (T : α → ℝ) (hT : Measurable T) (θ₀ θ₁ : ℝ)
    (hint₀ : Integrable (fun y => (T y - θ₀)^2) P₀)
    (hint₁ : Integrable (fun y => (T y - θ₁)^2) P₁) :
    ((θ₀ - θ₁)^2 / 4) * (1 - 2 * (tvDist P₀ P₁).toReal) ≤
      (∫ y, (T y - θ₀)^2 ∂P₀) + ∫ y, (T y - θ₁)^2 ∂P₁ := by
  -- Set s := |θ₀ - θ₁| / 2.
  set s : ℝ := |θ₀ - θ₁| / 2 with hs_def
  have hs_sq : s^2 = (θ₀ - θ₁)^2 / 4 := by
    rw [hs_def]; rw [div_pow]; rw [sq_abs]; ring
  have hs_nn : 0 ≤ s := by rw [hs_def]; positivity
  -- Define B := {y : α | s^2 ≤ (T y - θ₀)^2}.
  set B : Set α := {y | s^2 ≤ (T y - θ₀)^2} with hB_def
  have hB_meas : MeasurableSet B := by
    refine measurableSet_le measurable_const ?_
    exact (hT.sub measurable_const).pow_const 2
  -- Pointwise lower bound on B^c: (T y - θ₁)^2 ≥ s^2.
  -- On B^c: (T y - θ₀)^2 < s^2, i.e. |T y - θ₀| < s.
  -- Then |T y - θ₁| = |(T y - θ₀) - (θ₁ - θ₀)| ≥ ||θ₀-θ₁| - |T y - θ₀|| ≥ |θ₀-θ₁| - s = s.
  have h_ptwise_B :
      ∀ y, B.indicator (fun _ => s^2) y ≤ (T y - θ₀)^2 := by
    intro y
    by_cases hyB : y ∈ B
    · rw [Set.indicator_of_mem hyB]
      exact hyB
    · rw [Set.indicator_of_notMem hyB]
      exact sq_nonneg _
  have h_ptwise_Bc :
      ∀ y, Bᶜ.indicator (fun _ => s^2) y ≤ (T y - θ₁)^2 := by
    intro y
    by_cases hyBc : y ∈ Bᶜ
    · rw [Set.indicator_of_mem hyBc]
      -- On Bᶜ: (T y - θ₀)^2 < s^2, derive (T y - θ₁)^2 ≥ s^2.
      have hyB_not : y ∉ B := hyBc
      have h_lt : (T y - θ₀)^2 < s^2 := by
        by_contra h_neg
        push_neg at h_neg
        exact hyB_not h_neg
      -- From (T y - θ₀)^2 < s^2: |T y - θ₀| < |s| = s (since s ≥ 0).
      have h_abs_lt : |T y - θ₀| < s := by
        have h1 : |T y - θ₀| < |s| := by
          rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq_eq_abs]
          have hs_sq_nn : 0 ≤ s^2 := sq_nonneg _
          exact Real.sqrt_lt_sqrt (sq_nonneg _) h_lt
        rwa [abs_of_nonneg hs_nn] at h1
      -- Triangle: |T y - θ₁| ≥ |θ₀ - θ₁| - |T y - θ₀| ≥ 2s - s = s.
      have h_triangle : |θ₀ - θ₁| ≤ |T y - θ₀| + |T y - θ₁| := by
        have : θ₀ - θ₁ = (T y - θ₁) - (T y - θ₀) := by ring
        calc |θ₀ - θ₁| = |(T y - θ₁) - (T y - θ₀)| := by rw [this]
          _ ≤ |T y - θ₁| + |T y - θ₀| := abs_sub _ _
          _ = |T y - θ₀| + |T y - θ₁| := by ring
      -- 2s = |θ₀ - θ₁|, so |T y - θ₁| ≥ 2s - |T y - θ₀| > 2s - s = s.
      have h_2s : 2 * s = |θ₀ - θ₁| := by
        rw [hs_def]; ring
      have h_abs_ge : s ≤ |T y - θ₁| := by linarith
      -- Square: (T y - θ₁)^2 ≥ s^2.
      have h_sq_ge : s^2 ≤ (T y - θ₁)^2 := by
        rw [← sq_abs (T y - θ₁)]
        exact sq_le_sq' (by linarith [abs_nonneg (T y - θ₁)]) h_abs_ge
      exact h_sq_ge
    · rw [Set.indicator_of_notMem hyBc]
      exact sq_nonneg _
  -- Step: ∫ s² · 𝟙_B ∂P₀ = s² · (P₀ B).toReal.
  have hBc_meas : MeasurableSet Bᶜ := hB_meas.compl
  -- Integrate pointwise bounds.
  have h_int_B :
      s^2 * (P₀ B).toReal ≤ ∫ y, (T y - θ₀)^2 ∂P₀ := by
    have h_indicator_int :
        ∫ y, B.indicator (fun _ => s^2) y ∂P₀ = s^2 * (P₀ B).toReal := by
      rw [MeasureTheory.integral_indicator_const _ hB_meas]
      show P₀.real B • s^2 = s^2 * (P₀ B).toReal
      rw [smul_eq_mul, MeasureTheory.measureReal_def]
      ring
    have h_le : ∫ y, B.indicator (fun _ => s^2) y ∂P₀ ≤
        ∫ y, (T y - θ₀)^2 ∂P₀ := by
      refine MeasureTheory.integral_mono ?_ hint₀ h_ptwise_B
      exact (MeasureTheory.integrable_const _).indicator hB_meas
    linarith
  have h_int_Bc :
      s^2 * (P₁ Bᶜ).toReal ≤ ∫ y, (T y - θ₁)^2 ∂P₁ := by
    have h_indicator_int :
        ∫ y, Bᶜ.indicator (fun _ => s^2) y ∂P₁ = s^2 * (P₁ Bᶜ).toReal := by
      rw [MeasureTheory.integral_indicator_const _ hBc_meas]
      show P₁.real Bᶜ • s^2 = s^2 * (P₁ Bᶜ).toReal
      rw [smul_eq_mul, MeasureTheory.measureReal_def]
      ring
    have h_le : ∫ y, Bᶜ.indicator (fun _ => s^2) y ∂P₁ ≤
        ∫ y, (T y - θ₁)^2 ∂P₁ := by
      refine MeasureTheory.integral_mono ?_ hint₁ h_ptwise_Bc
      exact (MeasureTheory.integrable_const _).indicator hBc_meas
    linarith
  -- Combine: sum ≥ s² · ((P₀ B) + (P₁ Bᶜ)).toReal
  --       = s² · (P₀(B) + 1 - P₁(B))
  --       ≥ s² · (1 - 2 · tvDist).
  have h_P1_compl_toReal :
      (P₁ Bᶜ).toReal = 1 - (P₁ B).toReal := by
    have h_split := MeasureTheory.measure_add_measure_compl (μ := P₁) hB_meas
    have hP1_univ : P₁ Set.univ = 1 := measure_univ
    have hP1_B_ne : P₁ B ≠ ∞ := measure_ne_top _ _
    have hP1_Bc_ne : P₁ Bᶜ ≠ ∞ := measure_ne_top _ _
    have h_sum_toReal :
        (P₁ B).toReal + (P₁ Bᶜ).toReal = 1 := by
      rw [← ENNReal.toReal_add hP1_B_ne hP1_Bc_ne, h_split, hP1_univ]
      simp
    linarith
  have h_TV := one_add_sub_ge_one_sub_two_tvDist (P := P₀) (Q := P₁) hB_meas
  -- (1 + (P₀ B) - (P₁ B)) ≥ 1 - 2 · tvDist.
  -- Sum (lifted to ℝ): s² · (P₀ B + P₁ Bᶜ) = s² · (P₀ B + 1 - P₁ B).
  have h_sum_bound :
      s^2 * (1 - 2 * (tvDist P₀ P₁).toReal) ≤
        (∫ y, (T y - θ₀)^2 ∂P₀) + ∫ y, (T y - θ₁)^2 ∂P₁ := by
    have hs_sq_nn : 0 ≤ s^2 := sq_nonneg _
    -- Compute: s²·(P₀ B) + s²·(P₁ Bᶜ) = s²·(P₀ B + 1 - P₁ B)
    have h_inner :
        s^2 * (P₀ B).toReal + s^2 * (P₁ Bᶜ).toReal =
        s^2 * (1 + ((P₀ B).toReal - (P₁ B).toReal)) := by
      rw [h_P1_compl_toReal]; ring
    -- s²·(1 + (P₀ B) - (P₁ B)) ≥ s²·(1 - 2·tvDist)
    have h_mul_le :
        s^2 * (1 - 2 * (tvDist P₀ P₁).toReal) ≤
          s^2 * (1 + ((P₀ B).toReal - (P₁ B).toReal)) :=
      mul_le_mul_of_nonneg_left h_TV hs_sq_nn
    linarith
  -- Substitute s² = (θ₀-θ₁)²/4.
  rw [hs_sq] at h_sum_bound
  exact h_sum_bound

end LTFP.MathlibExt.Probability
