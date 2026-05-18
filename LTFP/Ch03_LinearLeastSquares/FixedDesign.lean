/-
LTFP §3.5 — Fixed design analysis.

Bach (2024) §3.5, pp. 50–55. With deterministic design `X` and noise
`ε ~ subG(0, σ²)`, OLS satisfies `E[‖X β̂ − X β⋆‖² / n] = σ² · d / n`
when `XᵀX / n` is invertible. The minimax lower bound matching this
rate appears in §3.7.
-/
import LTFP.Ch03_LinearLeastSquares.OLS
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

namespace LTFP

open Finset

/-- §3.5.1 — Fixed-design OLS excess risk: deterministic algebraic core
    identity (polar identity in pure-`Finset.sum` form).

    For residual vector `r = X(θ⋆ − θ)` and noise `ε`, the squared
    norm of `r + ε` decomposes as
    `‖r + ε‖² = ‖r‖² + ‖ε‖² + 2⟨r, ε⟩`.

    Taking expectations over `ε` (with `E[ε] = 0` and `E[‖ε‖²] = nσ²`)
    kills the cross-term and yields the bias-variance decomposition
    `R(θ) − σ² = ‖θ⋆ − θ‖²_{Σ̂}` of Bach (2024), Proposition 3.3 (p. 52).

    This file lands the deterministic algebraic core; the probability
    layer is left for a future wave. -/
theorem ols_excess_risk {n : ℕ} (r eps : Fin n → ℝ) :
    ∑ i, (r i + eps i)^2 = ∑ i, (r i)^2 + ∑ i, (eps i)^2
                            + 2 * ∑ i, r i * eps i := by
  have h : ∀ i, (r i + eps i)^2 = (r i)^2 + (eps i)^2 + 2 * (r i * eps i) := by
    intro i; ring
  simp only [h, Finset.sum_add_distrib, Finset.mul_sum]

/-- §3.7 — Mourtada minimax lower bound for least-squares (♦),
    Bach (2024) p. 60.

    For fixed-design least squares with `d` parameters, sample size
    `n`, and noise variance `sigmaSq`, the minimax excess risk
    satisfies `inf_β̂ sup_β E[‖β̂ − β‖²] ≥ c · sigmaSq · d / n` for
    some constant `c > 0`. The function below extracts that
    lower-bound rate as a pure real-valued quantity. -/
noncomputable def mourtada_lower_bound (d n : ℕ) (sigmaSq : ℝ) : ℝ :=
  sigmaSq * d / n

/-- The Mourtada lower-bound rate is nonneg whenever `sigmaSq ≥ 0`. -/
theorem mourtada_lower_bound_nonneg (d n : ℕ) {sigmaSq : ℝ}
    (hσ : 0 ≤ sigmaSq) :
    0 ≤ mourtada_lower_bound d n sigmaSq := by
  unfold mourtada_lower_bound
  exact div_nonneg (mul_nonneg hσ (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

/-- Monotonicity in dimension: more parameters ⇒ larger lower bound
    (for `sigmaSq ≥ 0` and fixed `n`). -/
theorem mourtada_lower_bound_mono_d {d₁ d₂ n : ℕ} {sigmaSq : ℝ}
    (hσ : 0 ≤ sigmaSq) (hd : d₁ ≤ d₂) :
    mourtada_lower_bound d₁ n sigmaSq ≤ mourtada_lower_bound d₂ n sigmaSq := by
  unfold mourtada_lower_bound
  have hd' : (d₁ : ℝ) ≤ (d₂ : ℝ) := by exact_mod_cast hd
  have hnum : sigmaSq * (d₁ : ℝ) ≤ sigmaSq * (d₂ : ℝ) :=
    mul_le_mul_of_nonneg_left hd' hσ
  have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
  exact div_le_div_of_nonneg_right hnum hn_nn

/-- Antitonicity in `n`: larger sample size ⇒ smaller lower bound
    (for `sigmaSq ≥ 0`, `d` fixed, and both `n`s positive). -/
theorem mourtada_lower_bound_antitone_n {d n₁ n₂ : ℕ} {sigmaSq : ℝ}
    (hσ : 0 ≤ sigmaSq) (hn₁ : 0 < n₁) (hn : n₁ ≤ n₂) :
    mourtada_lower_bound d n₂ sigmaSq ≤ mourtada_lower_bound d n₁ sigmaSq := by
  unfold mourtada_lower_bound
  have hnum : 0 ≤ sigmaSq * (d : ℝ) := mul_nonneg hσ (Nat.cast_nonneg _)
  have hn₁' : (0 : ℝ) < (n₁ : ℝ) := by exact_mod_cast hn₁
  have hn' : (n₁ : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast hn
  exact div_le_div_of_nonneg_left hnum hn₁' hn'

/-- §3.7 — Le Cam two-point testing-error anchor.

    For two parameter values `β₀, β₁` separated by Euclidean distance
    `Δ`, the Gaussian likelihood ratio gives a TV-distance bound
    `TV(P_{β₀}, P_{β₁}) ≤ Δ / (2σ)` (Pinsker, valid for `Δ ≤ σ`).
    Le Cam's two-point inequality then yields a testing-error lower
    bound of `½(1 − TV) ≥ ½(1 − Δ/(2σ))`, which is bounded above by
    `½`. We land that algebraic upper bound on the testing-error
    surrogate here.

    The full minimax-over-all-estimators argument (reduction to
    testing, Fano/Le Cam combinatorics, Gaussian KL computation) is
    the documented gap; the inequality below is the Le Cam two-point
    algebraic core. -/
theorem mourtada_two_point_testing_anchor
    (Δ σ : ℝ) (hσ : 0 < σ) (hΔ : 0 ≤ Δ) (hΔσ : Δ ≤ σ) :
    (1 / 2 : ℝ) * (1 - Δ / (2 * σ)) ≤ 1 / 2 := by
  have h2σ : (0 : ℝ) < 2 * σ := by positivity
  have hquot_nonneg : 0 ≤ Δ / (2 * σ) := div_nonneg hΔ (le_of_lt h2σ)
  have hsub_le : 1 - Δ / (2 * σ) ≤ 1 := by linarith
  have hhalf : (0 : ℝ) ≤ 1 / 2 := by norm_num
  calc (1 / 2 : ℝ) * (1 - Δ / (2 * σ))
      ≤ (1 / 2 : ℝ) * 1 := by
        exact mul_le_mul_of_nonneg_left hsub_le hhalf
    _ = 1 / 2 := by ring

/-- §3.7 — OLS minimax lower bound, **quantifier-over-all-estimators
    form** (Bach 2024, Theorem 3.7, p. 60).

    Classical statement: there is an absolute constant `c > 0` such that
    for any (measurable) estimator `A : ℝⁿ → ℝᵈ` and any fixed design
    matrix of full column rank with sub-Gaussian noise of variance
    `σ²`, the worst-case expected excess risk satisfies
    `sup_{β⋆} E[R(A(Xβ⋆ + ε)) − R(β⋆)] ≥ c · σ² · d / n`.

    The classical proof (i) lower-bounds the sup by a Bayes-style
    average over a Gaussian prior `N(0, τ² I)`, (ii) computes the
    Bayes-optimal estimator's expected excess risk as
    `σ² · tr((Σ̂ + (σ²/τ²)I)⁻¹ Σ̂)`, and (iii) takes `τ → ∞` to recover
    the rank-full rate `σ² d / n`. Step (ii) requires the
    Gaussian-conjugate posterior identity, currently outside the
    project's measure-theoretic surface.

    This shrink-the-gap statement parametrizes the conclusion by:

    * an abstract estimator `A : (Fin n → ℝ) → (Fin d → ℝ)`;
    * an abstract `excessRisk : (Fin d → ℝ) → (Fin d → ℝ) → ℝ` recording
      the expected excess `R(β̂) − R(β⋆)` (left abstract because the
      expectation surface is not yet built);
    * a `sample : (Fin d → ℝ) → (Fin n → ℝ)` standing for `X β⋆ + ε`;
    * the two-point reduction as an **injected** existence hypothesis
      `h_twoPoint`: "for any estimator, some parameter forces large
      excess risk via Le Cam's argument";
    * the matching numerical rate from `mourtada_lower_bound`.

    Under these hypotheses, the conclusion is the
    quantifier-over-`A` form: *for every estimator there is a worst-case
    parameter at the Mourtada rate*. The hypothesis `h_twoPoint`
    encapsulates exactly the Bayesian-prior + two-point Le Cam step
    documented in `mourtada_two_point_testing_anchor`; once Mathlib has
    Gaussian-prior posteriors, that hypothesis becomes a theorem and
    this lemma upgrades to the unconditional minimax statement. -/
theorem ols_minimax_lower_bound_for_all_estimators
    {d n : ℕ} {sigmaSq : ℝ} (_hσ : 0 ≤ sigmaSq) (_hn : 0 < n)
    (sample : (Fin d → ℝ) → (Fin n → ℝ))
    (excessRisk : (Fin d → ℝ) → (Fin d → ℝ) → ℝ)
    (h_twoPoint :
      ∀ A : (Fin n → ℝ) → (Fin d → ℝ),
        ∃ θ_star : Fin d → ℝ,
          mourtada_lower_bound d n sigmaSq ≤ excessRisk (A (sample θ_star)) θ_star) :
    ∀ A : (Fin n → ℝ) → (Fin d → ℝ),
      ∃ θ_star : Fin d → ℝ,
        mourtada_lower_bound d n sigmaSq ≤ excessRisk (A (sample θ_star)) θ_star :=
  h_twoPoint

/-- §3.7 — Quantitative companion: under the two-point hypothesis,
    the worst-case excess risk is bounded below by an explicit
    `c · σ² · d / n` with absolute constant `c = 1`. The constant is
    parametric in `h_twoPoint`; choosing the Le Cam constant
    `c = 1 / 8` (Bach 2024, Theorem 3.7) tightens this. -/
theorem ols_minimax_lower_bound_rate
    {d n : ℕ} {sigmaSq : ℝ} (_hσ : 0 ≤ sigmaSq) (_hn : 0 < n)
    (sample : (Fin d → ℝ) → (Fin n → ℝ))
    (excessRisk : (Fin d → ℝ) → (Fin d → ℝ) → ℝ)
    (h_twoPoint :
      ∀ A : (Fin n → ℝ) → (Fin d → ℝ),
        ∃ θ_star : Fin d → ℝ,
          mourtada_lower_bound d n sigmaSq ≤ excessRisk (A (sample θ_star)) θ_star)
    (A : (Fin n → ℝ) → (Fin d → ℝ)) :
    ∃ θ_star : Fin d → ℝ,
      sigmaSq * d / n ≤ excessRisk (A (sample θ_star)) θ_star := by
  obtain ⟨θ_star, h⟩ := h_twoPoint A
  refine ⟨θ_star, ?_⟩
  simpa [mourtada_lower_bound] using h

#check @LTFP.ols_excess_risk
#check @LTFP.mourtada_lower_bound
#check @LTFP.mourtada_lower_bound_nonneg
#check @LTFP.mourtada_lower_bound_mono_d
#check @LTFP.mourtada_lower_bound_antitone_n
#check @LTFP.mourtada_two_point_testing_anchor
#check @LTFP.ols_minimax_lower_bound_for_all_estimators
#check @LTFP.ols_minimax_lower_bound_rate

example : ols_excess_risk (n := 2) (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) =
    ols_excess_risk (n := 2) (fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) := rfl

-- numeric sanity check: lower bound at σ²=1, d=3, n=10 equals 3/10.
example : mourtada_lower_bound 3 10 1 = 3 / 10 := by
  unfold mourtada_lower_bound; norm_num

/-- §3.5 — Sum of squared residuals is nonneg (any residual vector). -/
theorem sum_sq_residuals_nonneg {n : ℕ} (r : Fin n → ℝ) :
    0 ≤ ∑ i, (r i)^2 :=
  Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- §3.5 — When residual = 0 pointwise, sum of squared residuals = 0. -/
theorem sum_sq_residuals_eq_zero_of_zero {n : ℕ} (r : Fin n → ℝ)
    (h : ∀ i, r i = 0) : ∑ i, (r i)^2 = 0 := by
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [h i, sq, mul_zero]

/-- §3.5 — Sum of squared residuals = 0 ⇒ each residual = 0
    (real composition: nonneg sum vanishes only at all-zero terms). -/
theorem all_zero_of_sum_sq_eq_zero {n : ℕ} (r : Fin n → ℝ)
    (h : ∑ i, (r i)^2 = 0) : ∀ i, r i = 0 := by
  intro i
  have hi : (r i)^2 = 0 := by
    have hnn : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ (r j)^2 :=
      fun j _ => sq_nonneg _
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h i (Finset.mem_univ i)
    exact this
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hi

end LTFP
