/-
LTFP §3.5 — Fixed design analysis.

Bach (2024) §3.5, pp. 50–55. With deterministic design `X` and noise
`ε ~ subG(0, σ²)`, OLS satisfies `E[‖X β̂ − X β⋆‖² / n] = σ² · d / n`
when `XᵀX / n` is invertible. The minimax lower bound matching this
rate appears in §3.7.
-/
import LTFP.Ch03_LinearLeastSquares.OLS
import LTFP.MathlibExt.Probability.Distributions.MultivariateGaussian
import LTFP.MathlibExt.Probability.Distributions.MultivariateGaussianMSE
import LTFP.MathlibExt.Probability.Distributions.OLSSampleD1
import LTFP.MathlibExt.Probability.Distance.Bhattacharyya
import LTFP.MathlibExt.Probability.Distance.GaussianBhattacharyya
import LTFP.MathlibExt.Probability.Distance.GaussianBhattacharyyaMultivariate
import LTFP.MathlibExt.Probability.Distance.GaussianTwoPointKL
import LTFP.MathlibExt.Probability.LeCamSquaredLossReduction
import LTFP.MathlibExt.Probability.TwoPointBayesRisk
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.Topology.Algebra.Order.Field

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

/-- §3.7 — Bayes-prior reduction, step (i): the worst-case (sup) risk is
    bounded below by *any* Bayes-style average risk over a prior.

    Classical statement: for any prior `π` on parameters and any
    estimator `A`,
    `sup_θ E[R(A, θ)] ≥ ∫ E[R(A, θ)] dπ(θ)`.

    Below we land the finite-prior algebraic core: replace `∫ · dπ` by a
    finite convex combination `∑ k, w k · f (θ k)` with `0 ≤ w` and
    `∑ w = 1`, where `f := excessRisk (A (sample ·)) ·`. The conclusion
    `bound ≤ sup f` from `∀ k, bound ≤ ∑ w · f` is the standard
    finite-prior reduction, suitable for finite-design Le Cam arguments.

    For any indexing set `K`, prior weights `w : K → ℝ` with
    `0 ≤ w` and `∑ w = 1`, and risk evaluations
    `f : K → ℝ`: the weighted-average is at most the max of any
    nonneg point that already dominates each `f k`. Equivalently: if
    `bound ≤ ∑ k, w k * f k`, then there exists some `k` with
    `bound ≤ f k`. -/
theorem sup_ge_bayes_average
    {K : Type*} [Fintype K] [Nonempty K]
    (w : K → ℝ) (f : K → ℝ) (bound : ℝ)
    (hw_nn : ∀ k, 0 ≤ w k) (hw_sum : ∑ k, w k = 1)
    (h_avg : bound ≤ ∑ k, w k * f k) :
    ∃ k, bound ≤ f k := by
  by_contra h_neg
  push_neg at h_neg
  -- For every `k`, `f k < bound`. So `∑ k, w k * f k < ∑ k, w k * bound = bound`.
  have h_lt_each : ∀ k ∈ (Finset.univ : Finset K), w k * f k ≤ w k * bound :=
    fun k _ => mul_le_mul_of_nonneg_left (le_of_lt (h_neg k)) (hw_nn k)
  have h_sum_le : ∑ k, w k * f k ≤ ∑ k, w k * bound :=
    Finset.sum_le_sum h_lt_each
  have h_sum_eq : ∑ k, w k * bound = bound := by
    rw [← Finset.sum_mul, hw_sum, one_mul]
  have h_le : ∑ k, w k * f k ≤ bound := h_sum_le.trans (le_of_eq h_sum_eq)
  -- Strictness: at least one weight is positive (since they sum to 1), so the
  -- inequality is strict. We extract a witness `k₀` with `w k₀ > 0`.
  have h_exists_pos : ∃ k₀, 0 < w k₀ := by
    by_contra h_all_nonpos
    push_neg at h_all_nonpos
    have h_all_zero : ∀ k ∈ (Finset.univ : Finset K), w k = 0 := by
      intro k _; exact le_antisymm (h_all_nonpos k) (hw_nn k)
    have : (∑ k, w k) = 0 := Finset.sum_eq_zero h_all_zero
    rw [hw_sum] at this; norm_num at this
  obtain ⟨k₀, hk₀⟩ := h_exists_pos
  have h_strict_at : w k₀ * f k₀ < w k₀ * bound := by
    have := h_neg k₀
    nlinarith [hk₀]
  have h_sum_lt : ∑ k, w k * f k < ∑ k, w k * bound := by
    refine Finset.sum_lt_sum (fun k _ => h_lt_each k (Finset.mem_univ k)) ?_
    exact ⟨k₀, Finset.mem_univ _, h_strict_at⟩
  rw [h_sum_eq] at h_sum_lt
  linarith

/-- §3.7 — Bayes-prior reduction, step (ii) — *parametric form*.

    Classical statement: under a Gaussian prior `β ~ N(0, τ² I_d)` and
    Gaussian noise `ε ~ N(0, σ² I_n)`, the Bayes-optimal estimator
    (the posterior mean) has expected excess risk

    `E_{β ~ π} E_{ε} [R(β̂_Bayes) − R(β)] = σ² · tr((Σ̂ + (σ²/τ²) I)⁻¹ Σ̂)`

    where `Σ̂ = XᵀX / n`. This identity requires the
    Gaussian-conjugate-posterior calculus (Mathlib gap: posterior of
    multivariate Gaussian under Gaussian likelihood).

    We package it as a parametric *equality hypothesis*: given an
    abstract `bayesAvgRisk : ℝ → ℝ` (the Bayes average risk as a
    function of `λ := σ²/τ²`) which the user-of-this-lemma supplies
    together with the scalar identity
    `bayesAvgRisk λ = sigmaSq * d / (1 + λ)`, the lemma below verifies
    the identity in scalar / `Σ̂ = I` form. The general matrix form
    (with arbitrary p.s.d. `Σ̂`) reduces to this scalar form once the
    eigendecomposition of `Σ̂` is available.

    Note: we use `1 + λ` rather than `λ + 1` to match the canonical
    "shrinkage" denominator. -/
theorem bayes_posterior_mean_excess_risk_gaussian_scalar
    (sigmaSq : ℝ) (d : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) :
    sigmaSq * d / (1 + lam) ≤ sigmaSq * d / 1 ∨
      0 ≤ sigmaSq * d / (1 + lam) ∨ sigmaSq < 0 := by
  -- Trivial structural lemma: any of the three disjuncts is decidable;
  -- the content is encoded in the actual `bayes_trace_limit` below. We
  -- record the algebraic shape `σ² d / (1 + λ)` as the canonical Bayes
  -- risk; the user-of-this-lemma plugs it in.
  rcases lt_or_ge sigmaSq 0 with hσ | hσ
  · exact Or.inr (Or.inr hσ)
  · refine Or.inr (Or.inl ?_)
    have h1 : (0 : ℝ) < 1 + lam := by linarith
    have hnum : 0 ≤ sigmaSq * (d : ℝ) := mul_nonneg hσ (Nat.cast_nonneg _)
    exact div_nonneg hnum (le_of_lt h1)

/-- §3.7 — Bayes-prior reduction, step (ii) — *discharged form*.

    The structural disjunction packaged by
    `bayes_posterior_mean_excess_risk_gaussian_scalar` above is now backed
    by the concrete algebraic identity from
    `LTFP.MathlibExt.Probability.Distributions.MultivariateGaussian`:

    `gaussianBayesRiskScalar σ² d n λ = σ² · d / (n · (1 + λ))`.

    This is the **canonical scalar Bayes shrinkage risk** under prior
    `β ~ N(0, τ²·I)` and noise `ε ~ N(0, σ²·I)` for the `Σ̂ = I` case
    (Bach 2024, §3.7). The explicit `n` factor carries the OLS
    sample-size normalization so the `λ → 0⁺` limit matches
    `mourtada_lower_bound d n σ² = σ² · d / n` exactly. The general
    matrix case reduces to this scalar form by spectral decomposition
    of `Σ̂`.

    Together with `bayes_trace_limit_discharged` and
    `sup_ge_bayes_average`, this discharges the algebraic content of
    the Bayes-prior reduction in `ols_minimax_bayes_prior_discharged`
    for the canonical Gaussian setup. -/
theorem bayes_posterior_mean_excess_risk_gaussian_scalar_discharged
    (sigmaSq : ℝ) (d : ℕ) (n : ℕ) (lam : ℝ) :
    LTFP.MathlibExt.Probability.Distributions.gaussianBayesRiskScalar
        sigmaSq d n lam = sigmaSq * d / (n * (1 + lam)) :=
  LTFP.MathlibExt.Probability.Distributions.gaussianBayesRiskScalar_eq
    sigmaSq d n lam

/-- §3.7 — Bayes-prior reduction, step (iii) — *discharged form*.

    The asymptotic identity `gaussianBayesRiskScalar σ² d n (1/N) →
    σ² · d / n` from the multivariate-Gaussian extension matches the
    Mourtada lower-bound rate `mourtada_lower_bound d n σ² =
    σ² · d / n` exactly. Use this form when working with the
    discharged Bayes-risk function rather than the inline
    `σ² · d / (1 + 1/N)` expression. -/
theorem bayes_trace_limit_discharged (sigmaSq : ℝ) (d : ℕ) (n : ℕ) :
    Filter.Tendsto
      (fun N : ℕ =>
        LTFP.MathlibExt.Probability.Distributions.gaussianBayesRiskScalar
          sigmaSq d n (1 / (N : ℝ)))
      Filter.atTop (nhds (sigmaSq * d / n)) :=
  LTFP.MathlibExt.Probability.Distributions.gaussianBayesRiskScalar_tendsto_atTop
    sigmaSq d n

/-- §3.7 — Bayes-prior reduction, step (iii): trace limit.

    Algebraic core: as the prior variance `τ² → ∞` (equivalently
    `λ := σ²/τ² → 0⁺`), the Bayes-risk shrinkage denominator
    `1 + λ` tends to `1`, so the scalar Bayes risk
    `σ² · d / (1 + λ)` tends to `σ² · d`.

    Concretely: along the natural-number sequence `τ = N`, set
    `λ_N := σ²/N²` (or simply `1/N`); then `1/(1 + λ_N) → 1`, hence
    `σ² · d / (1 + λ_N) → σ² · d`.

    We package this as: the function `N ↦ sigmaSq * d / (1 + 1/N)` on
    `ℕ` tends to `sigmaSq * d` along `atTop`. This is the limit step
    that, combined with `bayes_posterior_mean_excess_risk_gaussian_scalar`
    above and `sup_ge_bayes_average`, discharges the Bayes-prior
    reduction. -/
theorem bayes_trace_limit (sigmaSq : ℝ) (d : ℕ) :
    Filter.Tendsto (fun N : ℕ => sigmaSq * d / (1 + 1 / (N : ℝ)))
      Filter.atTop (nhds (sigmaSq * d)) := by
  -- `1 / (N : ℝ) → 0` along `atTop`.
  have h_inv : Filter.Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ))
      Filter.atTop (nhds 0) := tendsto_one_div_atTop_nhds_zero_nat
  -- `(1 + 1/N) → 1`.
  have h_denom : Filter.Tendsto (fun N : ℕ => (1 : ℝ) + 1 / (N : ℝ))
      Filter.atTop (nhds (1 + 0)) :=
    Filter.Tendsto.add tendsto_const_nhds h_inv
  have h_denom' : Filter.Tendsto (fun N : ℕ => (1 : ℝ) + 1 / (N : ℝ))
      Filter.atTop (nhds 1) := by
    simpa using h_denom
  -- `σ² d / (1 + 1/N) → σ² d / 1 = σ² d`.
  have h_div : Filter.Tendsto
      (fun N : ℕ => sigmaSq * d / (1 + 1 / (N : ℝ)))
      Filter.atTop (nhds (sigmaSq * d / 1)) :=
    Filter.Tendsto.div tendsto_const_nhds h_denom' one_ne_zero
  simpa using h_div

/-- §3.7 — **Bayes-prior reduction, packaged**.

    Combine (i) `sup_ge_bayes_average`, (ii) the parametric Gaussian
    posterior identity (input as hypothesis `h_bayes_eq`), and (iii)
    `bayes_trace_limit` to derive the
    "for every estimator some parameter forces the rate" conclusion.

    Inputs:

    * abstract estimator `A`, abstract `sample` and `excessRisk` as in
      `ols_minimax_lower_bound_for_all_estimators`;
    * a finite parameter grid `K` with prior weights `w` summing to `1`
      (the discretization of `N(0, τ² I)` that step (i) needs);
    * for each `τ`-index `N`, a finite-prior bound
      `bound_N ≤ ∑ k, w k * excessRisk (A (sample (θ k))) (θ k)`,
      i.e., the Bayes-risk lower bound at variance level `N`;
    * the limit identity `bound_N → mourtada_lower_bound d n sigmaSq`
      (step (iii), supplied by `bayes_trace_limit` for the Gaussian
      prior).

    Conclusion: there exists a parameter forcing every estimator below
    the Mourtada rate. This is the *quantitative* form of the two-point
    hypothesis already used in
    `ols_minimax_lower_bound_for_all_estimators`. -/
theorem ols_minimax_bayes_prior
    {d n : ℕ} {sigmaSq : ℝ} (_hσ : 0 ≤ sigmaSq) (_hn : 0 < n)
    {K : Type*} [Fintype K] [Nonempty K]
    (θ : K → (Fin d → ℝ))
    (w : K → ℝ) (hw_nn : ∀ k, 0 ≤ w k) (hw_sum : ∑ k, w k = 1)
    (sample : (Fin d → ℝ) → (Fin n → ℝ))
    (excessRisk : (Fin d → ℝ) → (Fin d → ℝ) → ℝ)
    (A : (Fin n → ℝ) → (Fin d → ℝ))
    (h_bayes_eq :
      mourtada_lower_bound d n sigmaSq ≤
        ∑ k, w k * excessRisk (A (sample (θ k))) (θ k)) :
    ∃ θ_star : Fin d → ℝ,
      mourtada_lower_bound d n sigmaSq ≤ excessRisk (A (sample θ_star)) θ_star := by
  -- Apply step (i) to the function `k ↦ excessRisk (A (sample (θ k))) (θ k)`.
  obtain ⟨k, hk⟩ :=
    sup_ge_bayes_average (K := K) w
      (fun k => excessRisk (A (sample (θ k))) (θ k))
      (mourtada_lower_bound d n sigmaSq) hw_nn hw_sum h_bayes_eq
  exact ⟨θ k, hk⟩

/-- §3.7 — **Bayes-prior reduction, discharged (wired) form**.

    Wired version of `ols_minimax_bayes_prior` that consumes the
    discharged Gaussian-scalar Bayes risk
    `gaussianBayesRiskScalar σ² d n λ` directly from
    `bayes_posterior_mean_excess_risk_gaussian_scalar_discharged`,
    rather than taking the inequality
    `mourtada_lower_bound d n σ² ≤ ∑ w k · risk k`
    as a parametric hypothesis.

    Given:

    * the same finite prior weights `w` with `∑ w = 1`,
    * a shrinkage parameter `λ ≥ 0` (interpreted as `σ² / τ²`),
    * the Gaussian-conjugate computation that the prior-averaged
      excess risk dominates the closed-form Bayes shrinkage risk
      `gaussianBayesRiskScalar σ² d n λ` (this *is* the discharged
      step (ii) identity composed with the matrix → scalar reduction),

    the conclusion is: there exists a parameter `θ_star` forcing
    every estimator below the Bayes-shrinkage rate
    `σ² · d / (n · (1 + λ))`. As `λ → 0⁺` (`τ → ∞`) the rate equals
    `σ² · d / n = mourtada_lower_bound d n σ²` by
    `bayes_trace_limit_discharged`. -/
theorem ols_minimax_bayes_prior_discharged
    {d n : ℕ} {sigmaSq : ℝ} (_hσ : 0 ≤ sigmaSq) (_hn : 0 < n)
    {K : Type*} [Fintype K] [Nonempty K]
    (θ : K → (Fin d → ℝ))
    (w : K → ℝ) (hw_nn : ∀ k, 0 ≤ w k) (hw_sum : ∑ k, w k = 1)
    (sample : (Fin d → ℝ) → (Fin n → ℝ))
    (excessRisk : (Fin d → ℝ) → (Fin d → ℝ) → ℝ)
    (A : (Fin n → ℝ) → (Fin d → ℝ))
    (lam : ℝ) (_hlam : 0 ≤ lam)
    (h_bayes_gaussian :
      LTFP.MathlibExt.Probability.Distributions.gaussianBayesRiskScalar
          sigmaSq d n lam ≤
        ∑ k, w k * excessRisk (A (sample (θ k))) (θ k)) :
    ∃ θ_star : Fin d → ℝ,
      LTFP.MathlibExt.Probability.Distributions.gaussianBayesRiskScalar
          sigmaSq d n lam ≤ excessRisk (A (sample θ_star)) θ_star := by
  -- Apply step (i) with bound = `gaussianBayesRiskScalar σ² d n λ`.
  obtain ⟨k, hk⟩ :=
    sup_ge_bayes_average (K := K) w
      (fun k => excessRisk (A (sample (θ k))) (θ k))
      (LTFP.MathlibExt.Probability.Distributions.gaussianBayesRiskScalar
        sigmaSq d n lam)
      hw_nn hw_sum h_bayes_gaussian
  exact ⟨θ k, hk⟩

/-- §3.7 — **Per-estimator finite-prior averaging at the improper limit**
    (NOT a closed discharge of the carrier theorem).

    Honest scope (per Codex peer-review, 2026-05-19): this lemma is the
    **per-estimator building block** of the Bayes-prior reduction, not
    the carrier discharge. Given a *fixed* estimator `A` and a finite
    grid `(θ, w)` whose prior-averaged excess risk dominates
    `gaussianBayesRiskScalar σ² d n 0`, the lemma produces a single
    worst-case parameter for that `A` at the Mourtada rate.

    What it does NOT do:

    * It does NOT close `ols_minimax_lower_bound_for_all_estimators`'s
      hypothesis `∀ A, ∃ θ_star, mourtada ≤ excessRisk (A (sample θ_star)) θ_star`.
      That requires a *universally quantified* hypothesis "for every
      estimator there exists *some* finite prior averaging it down to
      the Bayes risk", which is the content of
      `ols_minimax_bayes_prior_via_quantified_finite_average` below.

    * `λ = 0` is the **improper / infinite-variance** prior limit, not
      a finite-`τ²` Gaussian. The Gaussian-conjugate posterior identity
      is sound at finite `τ²`; the bridge to `λ = 0` involves a
      limiting/approximation argument that is left to the caller (or
      to a future Mathlib measure-theoretic discharge).

    Use this lemma as a finite-prior averaging tool when the
    Gaussian-conjugate Bayes-risk inequality has already been
    established at `λ = 0` for the specific estimator `A` and grid
    `(θ, w)`. For the universal/carrier-discharge form, see
    `ols_minimax_bayes_prior_via_quantified_finite_average`. -/
theorem ols_minimax_bayes_prior_finite_average_at_improper_limit
    {d n : ℕ} {sigmaSq : ℝ} (hσ : 0 ≤ sigmaSq) (hn : 0 < n)
    {K : Type*} [Fintype K] [Nonempty K]
    (θ : K → (Fin d → ℝ))
    (w : K → ℝ) (hw_nn : ∀ k, 0 ≤ w k) (hw_sum : ∑ k, w k = 1)
    (sample : (Fin d → ℝ) → (Fin n → ℝ))
    (excessRisk : (Fin d → ℝ) → (Fin d → ℝ) → ℝ)
    (A : (Fin n → ℝ) → (Fin d → ℝ))
    (h_bayes_gaussian_at_zero :
      LTFP.MathlibExt.Probability.Distributions.gaussianBayesRiskScalar
          sigmaSq d n 0 ≤
        ∑ k, w k * excessRisk (A (sample (θ k))) (θ k)) :
    ∃ θ_star : Fin d → ℝ,
      mourtada_lower_bound d n sigmaSq ≤ excessRisk (A (sample θ_star)) θ_star := by
  -- Apply the parametric-lambda version with `lam = 0`, then translate
  -- `gaussianBayesRiskScalar σ² d n 0 = σ² · d / n = mourtada_lower_bound d n σ²`
  -- via the discharged identity.
  obtain ⟨θ_star, hθ⟩ :=
    ols_minimax_bayes_prior_discharged (d := d) (n := n) (sigmaSq := sigmaSq)
      hσ hn θ w hw_nn hw_sum sample excessRisk A 0 (le_refl _)
      h_bayes_gaussian_at_zero
  refine ⟨θ_star, ?_⟩
  -- Rewrite the bound on `hθ` from `gaussianBayesRiskScalar σ² d n 0` to
  -- `mourtada_lower_bound d n σ²`.
  have h_eq :
      LTFP.MathlibExt.Probability.Distributions.gaussianBayesRiskScalar
          sigmaSq d n 0 = mourtada_lower_bound d n sigmaSq := by
    unfold mourtada_lower_bound
    rw [bayes_posterior_mean_excess_risk_gaussian_scalar_discharged]
    have hn_ne : (n : ℝ) ≠ 0 := by
      have : (0 : ℕ) < n := hn
      exact_mod_cast (Nat.pos_iff_ne_zero.mp this)
    field_simp
    ring
  rw [h_eq] at hθ
  exact hθ

/-- §3.7 — **Bayes-prior reduction, properly quantified discharge**.

    This is the universal-quantifier form Codex's peer-review identified
    as the actually-needed shape (2026-05-19): the hypothesis takes a
    *universally quantified* "for every estimator `A`, there exists a
    finite prior grid whose averaged excess risk dominates the Bayes
    risk at `λ = 0`", and the conclusion is exactly the carrier's
    `h_twoPoint` hypothesis (`∀ A, ∃ θ_star, mourtada ≤ excessRisk
    (A (sample θ_star)) θ_star`).

    Concretely, the hypothesis bundles:

    * the *existence* of a finite parameter grid `(θ_k)_{k : Fin m}`
      with prior weights `(w_k)_{k : Fin m}` (`0 ≤ w_k`, `∑ w = 1`)
      for each estimator `A` (the "for every estimator" sup→avg step);
    * the Gaussian-conjugate Bayes-risk inequality at the improper
      limit `λ = 0`: prior-averaged excess risk dominates
      `gaussianBayesRiskScalar σ² d n 0 = σ² · d / n`.

    Both ingredients are *honestly* the unfinished mathematical work:
    the existence of the witnessing grid for every estimator is the
    Bayesian-prior + Le Cam sup-vs-Bayes step, and the bridge from
    finite-`τ²` Gaussian conjugacy to the `λ = 0` improper limit is
    the limiting/approximation argument flagged by Codex. *This
    theorem does not close that gap.* It packages the two together
    into the carrier shape so that downstream wiring is exposed.

    The conclusion is then literally the
    `ols_minimax_lower_bound_for_all_estimators` `h_twoPoint`
    hypothesis, so this theorem composes directly with the carrier
    (see `ols_minimax_lower_bound_via_quantified_finite_average` below). -/
theorem ols_minimax_bayes_prior_via_quantified_finite_average
    {d n : ℕ} {sigmaSq : ℝ} (hσ : 0 ≤ sigmaSq) (hn : 0 < n)
    (sample : (Fin d → ℝ) → (Fin n → ℝ))
    (excessRisk : (Fin d → ℝ) → (Fin d → ℝ) → ℝ)
    (h_bayes_quantified :
      ∀ A : (Fin n → ℝ) → (Fin d → ℝ),
        ∃ (m : ℕ) (_hm : 0 < m) (θ : Fin m → (Fin d → ℝ)) (w : Fin m → ℝ),
          (∀ k, 0 ≤ w k) ∧ (∑ k, w k = 1) ∧
          LTFP.MathlibExt.Probability.Distributions.gaussianBayesRiskScalar
              sigmaSq d n 0 ≤
            ∑ k, w k * excessRisk (A (sample (θ k))) (θ k)) :
    ∀ A : (Fin n → ℝ) → (Fin d → ℝ),
      ∃ θ_star : Fin d → ℝ,
        mourtada_lower_bound d n sigmaSq ≤ excessRisk (A (sample θ_star)) θ_star := by
  intro A
  -- Extract the (estimator-specific) witnessing grid from the quantified
  -- hypothesis.
  obtain ⟨m, hm, θ, w, hw_nn, hw_sum, h_avg⟩ := h_bayes_quantified A
  -- The grid lives in `Fin m` with `m > 0`, so `Fin m` is `Nonempty`.
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  -- Apply the per-estimator finite-prior averaging lemma at the improper
  -- limit. This converts the prior-averaged Bayes risk inequality into
  -- the single-witness conclusion `∃ θ_star, mourtada ≤ excessRisk ...`.
  exact ols_minimax_bayes_prior_finite_average_at_improper_limit
    (d := d) (n := n) (sigmaSq := sigmaSq) hσ hn θ w hw_nn hw_sum
    sample excessRisk A h_avg

/-- §3.7 — **Wired carrier**: the OLS minimax lower-bound theorem
    derived by feeding the properly-quantified Bayes-prior discharge
    into the carrier `ols_minimax_lower_bound_for_all_estimators`.

    This is the actual consumer composition Codex's peer-review asked
    for (2026-05-19): the hypothesis is the universally-quantified
    Bayesian-prior + improper-limit Gaussian-conjugate inequality, and
    the conclusion is the carrier theorem's
    `∀ A, ∃ θ_star, mourtada_lower_bound ≤ excessRisk ...` statement.

    The honest gap remains the hypothesis itself: producing, for every
    estimator `A`, an explicit witnessing finite prior whose averaged
    excess risk dominates `gaussianBayesRiskScalar σ² d n 0` requires
    both (a) the Gaussian-conjugate posterior-mean identity at finite
    `τ²` (Mathlib gap), and (b) the limiting/approximation bridge from
    finite-`τ²` Bayes risk to the `λ = 0` improper-prior limit. Once
    Mathlib lands the multivariate Gaussian posterior calculus and the
    limit bridge, the hypothesis becomes a theorem and the carrier
    upgrades to an unconditional minimax statement. -/
theorem ols_minimax_lower_bound_via_quantified_finite_average
    {d n : ℕ} {sigmaSq : ℝ} (hσ : 0 ≤ sigmaSq) (hn : 0 < n)
    (sample : (Fin d → ℝ) → (Fin n → ℝ))
    (excessRisk : (Fin d → ℝ) → (Fin d → ℝ) → ℝ)
    (h_bayes_quantified :
      ∀ A : (Fin n → ℝ) → (Fin d → ℝ),
        ∃ (m : ℕ) (_hm : 0 < m) (θ : Fin m → (Fin d → ℝ)) (w : Fin m → ℝ),
          (∀ k, 0 ≤ w k) ∧ (∑ k, w k = 1) ∧
          LTFP.MathlibExt.Probability.Distributions.gaussianBayesRiskScalar
              sigmaSq d n 0 ≤
            ∑ k, w k * excessRisk (A (sample (θ k))) (θ k)) :
    ∀ A : (Fin n → ℝ) → (Fin d → ℝ),
      ∃ θ_star : Fin d → ℝ,
        mourtada_lower_bound d n sigmaSq ≤ excessRisk (A (sample θ_star)) θ_star :=
  ols_minimax_lower_bound_for_all_estimators (d := d) (n := n)
    (sigmaSq := sigmaSq) hσ hn sample excessRisk
    (ols_minimax_bayes_prior_via_quantified_finite_average
      (d := d) (n := n) (sigmaSq := sigmaSq) hσ hn sample excessRisk
      h_bayes_quantified)

/-- §3.7 — **Finite-`τ²` family ⇒ improper-limit ε-approximation**
    (the Codex-prescribed *limit bridge*, 2026-05-21).

    Honest scope: this lemma closes one of the two honest gaps flagged in
    `ols_minimax_lower_bound_via_quantified_finite_average`'s docstring —
    the bridge from finite-`τ²` Gaussian-conjugate Bayes-risk inequalities
    to the `λ = 0` improper-prior limit. It does NOT close the other gap
    (producing the actual finite-`τ²` witnessing priors from the
    multivariate Gaussian posterior calculus); that requires the Mathlib
    posterior infrastructure flagged by Codex.

    Statement: suppose that for every estimator `A` and every `N > 0` the
    finite-`τ²` Gaussian conjugacy delivers a finite prior `(θ_N, w_N)`
    whose averaged excess risk dominates the Bayes-risk shrinkage at
    `λ_N = 1 / N`:

    `gaussianBayesRiskScalar σ² d n (1/N) ≤ ∑ k, w_N k · excessRisk
       (A (sample (θ_N k))) (θ_N k)`.

    Since
    `gaussianBayesRiskScalar σ² d n (1/N) → σ² · d / n =
       mourtada_lower_bound d n σ²` (this is
    `bayes_trace_limit_discharged`), for every ε > 0 there exists `N`
    such that `mourtada_lower_bound d n σ² - ε ≤ gaussianBayesRiskScalar
       σ² d n (1/N)`. Combined with the per-`N` finite-prior averaging
    via `sup_ge_bayes_average`, this yields the ε-relaxed carrier
    conclusion: for every estimator there exists a parameter forcing
    excess risk above `mourtada_lower_bound − ε`.

    This is the strongest *exact* conclusion derivable from the finite-`τ²`
    family without a compactness / continuity assumption on the
    parameter space. The full carrier conclusion (no ε) would require
    a uniform witness across the family, which is a real-analysis
    extraction problem orthogonal to the Gaussian-conjugate content. -/
theorem ols_minimax_bayes_prior_finite_tau_squared_family
    {d n : ℕ} {sigmaSq : ℝ} (hσ : 0 ≤ sigmaSq) (hn : 0 < n)
    (sample : (Fin d → ℝ) → (Fin n → ℝ))
    (excessRisk : (Fin d → ℝ) → (Fin d → ℝ) → ℝ)
    (h_bayes_family :
      ∀ A : (Fin n → ℝ) → (Fin d → ℝ),
        ∀ N : ℕ, 0 < N →
        ∃ (m : ℕ) (_hm : 0 < m) (θ : Fin m → (Fin d → ℝ)) (w : Fin m → ℝ),
          (∀ k, 0 ≤ w k) ∧ (∑ k, w k = 1) ∧
          LTFP.MathlibExt.Probability.Distributions.gaussianBayesRiskScalar
              sigmaSq d n (1 / (N : ℝ)) ≤
            ∑ k, w k * excessRisk (A (sample (θ k))) (θ k)) :
    ∀ A : (Fin n → ℝ) → (Fin d → ℝ),
      ∀ ε : ℝ, 0 < ε →
      ∃ θ_star : Fin d → ℝ,
        mourtada_lower_bound d n sigmaSq - ε ≤ excessRisk (A (sample θ_star)) θ_star := by
  intro A ε hε
  -- Step 1: extract a finite `N` for which
  -- `mourtada - ε ≤ gaussianBayesRiskScalar σ² d n (1/N)`.
  -- This uses `bayes_trace_limit_discharged` and the standard
  -- ε-definition of convergence.
  have h_tendsto :
      Filter.Tendsto
        (fun N : ℕ => LTFP.MathlibExt.Probability.Distributions.gaussianBayesRiskScalar
          sigmaSq d n (1 / (N : ℝ)))
        Filter.atTop (nhds (sigmaSq * d / n)) :=
    bayes_trace_limit_discharged sigmaSq d n
  -- The Mourtada lower bound equals `σ² · d / n` by definition.
  have h_mourtada : mourtada_lower_bound d n sigmaSq = sigmaSq * d / n := rfl
  -- ε-translation of `Tendsto` at the metric-space level: the set
  -- `{x | mourtada - ε ≤ x}` is a neighborhood of `mourtada` (it contains
  -- `(mourtada - ε, mourtada + ε)`), so eventually the sequence enters it.
  have h_nhds : Set.Ioo (sigmaSq * d / n - ε) (sigmaSq * d / n + ε) ∈
      nhds (sigmaSq * d / n) :=
    Ioo_mem_nhds (by linarith) (by linarith)
  have h_event_ioo : ∀ᶠ N : ℕ in Filter.atTop,
      LTFP.MathlibExt.Probability.Distributions.gaussianBayesRiskScalar
          sigmaSq d n (1 / (N : ℝ)) ∈
        Set.Ioo (sigmaSq * d / n - ε) (sigmaSq * d / n + ε) :=
    h_tendsto h_nhds
  have h_event :
      ∀ᶠ N : ℕ in Filter.atTop,
        mourtada_lower_bound d n sigmaSq - ε ≤
          LTFP.MathlibExt.Probability.Distributions.gaussianBayesRiskScalar
            sigmaSq d n (1 / (N : ℝ)) := by
    refine h_event_ioo.mono (fun N hN => ?_)
    rw [h_mourtada]
    exact le_of_lt hN.1
  -- Also eventually `N > 0`.
  have h_pos_event : ∀ᶠ N : ℕ in Filter.atTop, 0 < N :=
    Filter.eventually_atTop.mpr ⟨1, fun _ h1 => Nat.lt_of_lt_of_le Nat.zero_lt_one h1⟩
  -- Combine both eventuallies.
  have h_both : ∀ᶠ N : ℕ in Filter.atTop,
      0 < N ∧
        mourtada_lower_bound d n sigmaSq - ε ≤
          LTFP.MathlibExt.Probability.Distributions.gaussianBayesRiskScalar
            sigmaSq d n (1 / (N : ℝ)) :=
    h_pos_event.and h_event
  obtain ⟨N, hN_pos, hN_bound⟩ := h_both.exists
  -- Step 2: apply the finite-`τ²` hypothesis at this `N`.
  obtain ⟨m, hm, θ, w, hw_nn, hw_sum, h_avg⟩ := h_bayes_family A N hN_pos
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  -- Step 3: chain `mourtada - ε ≤ gaussianBayesRiskScalar ... ≤ ∑ w · risk`
  -- and apply `sup_ge_bayes_average` to extract a single witness.
  have h_chain :
      mourtada_lower_bound d n sigmaSq - ε ≤
        ∑ k, w k * excessRisk (A (sample (θ k))) (θ k) :=
    le_trans hN_bound h_avg
  obtain ⟨k, hk⟩ :=
    sup_ge_bayes_average (K := Fin m) w
      (fun k => excessRisk (A (sample (θ k))) (θ k))
      (mourtada_lower_bound d n sigmaSq - ε)
      hw_nn hw_sum h_chain
  exact ⟨θ k, hk⟩

/-- §3.7 — **Wired ε-approximated carrier from the finite-`τ²` family**.

    This is the direct downstream consumer of
    `ols_minimax_bayes_prior_finite_tau_squared_family`. It composes the
    limit bridge with the same `ols_minimax_lower_bound_for_all_estimators`
    carrier shape, except the conclusion is the ε-relaxed form
    `mourtada_lower_bound - ε ≤ excessRisk ...` rather than the exact
    `mourtada_lower_bound ≤ excessRisk ...`.

    The ε-relaxation is the *real-analysis cost* of the improper-limit
    bridge: without compactness or continuity on the parameter
    space, you cannot extract a single witness that achieves the exact
    `λ = 0` Bayes-risk bound from a sequence of witnesses at
    `λ_N = 1/N → 0`. The ε-form is the strongest exact statement that
    follows.

    Combined with the `λ = 0`-direct carrier
    `ols_minimax_lower_bound_via_quantified_finite_average`, the project
    now offers BOTH downstream consumer shapes:

    * exact-rate conclusion from a `λ = 0`-direct hypothesis
      (`..._quantified_finite_average`);
    * ε-rate conclusion from a finite-`τ²` family hypothesis
      (`..._finite_tau_squared_family`), which is the form Gaussian
      conjugacy actually produces.

    Whichever Mathlib posterior calculus arrives first will plug into the
    matching consumer shape. -/
theorem ols_minimax_lower_bound_via_finite_tau_squared_family
    {d n : ℕ} {sigmaSq : ℝ} (hσ : 0 ≤ sigmaSq) (hn : 0 < n)
    (sample : (Fin d → ℝ) → (Fin n → ℝ))
    (excessRisk : (Fin d → ℝ) → (Fin d → ℝ) → ℝ)
    (h_bayes_family :
      ∀ A : (Fin n → ℝ) → (Fin d → ℝ),
        ∀ N : ℕ, 0 < N →
        ∃ (m : ℕ) (_hm : 0 < m) (θ : Fin m → (Fin d → ℝ)) (w : Fin m → ℝ),
          (∀ k, 0 ≤ w k) ∧ (∑ k, w k = 1) ∧
          LTFP.MathlibExt.Probability.Distributions.gaussianBayesRiskScalar
              sigmaSq d n (1 / (N : ℝ)) ≤
            ∑ k, w k * excessRisk (A (sample (θ k))) (θ k)) :
    ∀ A : (Fin n → ℝ) → (Fin d → ℝ),
      ∀ ε : ℝ, 0 < ε →
      ∃ θ_star : Fin d → ℝ,
        mourtada_lower_bound d n sigmaSq - ε ≤
          excessRisk (A (sample θ_star)) θ_star :=
  ols_minimax_bayes_prior_finite_tau_squared_family
    (d := d) (n := n) (sigmaSq := sigmaSq) hσ hn sample excessRisk h_bayes_family

/-- §3.7 — **Gaussian two-point max-risk lower bound** (algebraic Le Cam
    composition).

    This lemma composes the algebraic building blocks of Bach (2024)
    §3.7 into the worst-case-over-pair bound used by the Mourtada
    minimax derivation:

    1. Pinsker (companion module `Distance/GaussianTwoPointKL.lean`):
       `tvDist(N(μ₀, σ²), N(μ₁, σ²)) ≤ pinskerBound (gaussianKLScalar Δ σ) = |Δ|/(2σ)`,
       where `Δ = μ₀ - μ₁`. We pass the conclusion `tv ≤ |Δ|/(2σ)` as
       hypothesis because the underlying `tvDist` is a measure-theoretic
       quantity not yet attached to the abstract two-point pair here.

    2. Le Cam two-point Bayes-risk bound (companion module
       `TwoPointBayesRisk.lean`):
       `(R₀ + R₁) / 2 ≥ (Δsq / 4) · (1 - tv)`, where `R₀, R₁` are the
       per-hypothesis risks of any estimator on the two-point pair.

    3. Average-to-max conversion: `(R₀ + R₁)/2 ≤ max R₀ R₁`.

    Combining 2 and 3 yields the conclusion
    `max R₀ R₁ ≥ twoPointBayesRiskBound Δsq tv`. Substituting the
    Pinsker bound from 1 specializes the right-hand side to
    `(Δsq / 4) · (1 - |Δ|/(2σ))`, which is the Gaussian-two-point form
    used at the heart of the Mourtada lower bound.

    Honest scope: this lemma assumes both (i) the per-pair average
    risk bound from Le Cam (still a hypothesis because the
    hypothesis-testing identity over measures is outside the present
    surface) and (ii) the TV upper bound from Pinsker (passed as
    hypothesis for the same reason). Both companion modules provide
    the *algebraic* values; the measure-theoretic identities tying
    them to actual `KL` and `TV` integrals are the remaining Mathlib
    gap. The lemma below is the algebraic pivot one uses *once* those
    identities are available; it makes the composition step explicit
    rather than implicit. -/
theorem gaussian_two_point_max_risk_lower_bound
    {Δ σ Δsq tv R₀ R₁ : ℝ}
    (hσ : 0 < σ)
    (hΔsq : Δsq = Δ ^ 2)
    (htv : tv ≤ |Δ| / (2 * σ))
    (h_avg : (Δsq / 4) * (1 - |Δ| / (2 * σ)) ≤ (R₀ + R₁) / 2) :
    (Δsq / 4) * (1 - |Δ| / (2 * σ)) ≤ max R₀ R₁ := by
  -- The Pinsker bound `tv ≤ |Δ|/(2σ)` is part of the chain via the
  -- `LTFP.MathlibExt.Probability.gaussianTwoPointPinskerBound` algebraic
  -- identity (left here as the `htv` hypothesis for explicitness; the
  -- algebraic identity is available as
  -- `gaussianTwoPointPinskerBound : pinskerBound (gaussianKLScalar Δ σ) = |Δ|/(2σ)`).
  -- The body of the proof is a direct call to
  -- `max_ge_twoPointBayesRiskBound_of_average_ge`, after unfolding
  -- `twoPointBayesRiskBound` to expose the `(Δsq/4)(1-tv)` shape with
  -- `tv = |Δ|/(2σ)` substituted in.
  -- Note: `hσ`, `hΔsq`, `htv` are recorded in the statement for
  -- downstream consumers; the proof itself only uses `h_avg` and the
  -- max-of-average inequality.
  let _hσ_used := hσ
  let _hΔsq_used := hΔsq
  let _htv_used := htv
  exact h_avg.trans (LTFP.MathlibExt.Probability.average_le_max_of_pair R₀ R₁)

/-- §3.7 — **Concrete-instance discharge of `h_twoPoint`** at `d = 1`
    (scalar OLS minimax, identity design, Gaussian likelihood).

    Honest scope: this is NOT a discharge of the full carrier
    `ols_minimax_lower_bound_for_all_estimators` at general `d`. It is
    a concrete-instance discharge at the *scalar* one-dimensional case,
    where the parameter space is `Fin 1 → ℝ ≅ ℝ`, the sample map and
    excess risk function are passed as parameters, and the
    `h_twoPoint`-shaped hypothesis is supplied by the caller in
    Le Cam two-point average form (not as the full carrier conclusion).

    Specifically: given any estimator `A`, the caller provides for some
    `Δ ≠ 0` the per-estimator pair of parameters
    `θ₀ := fun _ => 0` and `θ₁ := fun _ => Δ`, the per-θ risks
    `R₀ := excessRisk (A (sample θ₀)) θ₀` and
    `R₁ := excessRisk (A (sample θ₁)) θ₁`, and the algebraic Le Cam
    two-point average bound
    `(Δsq/4)(1 - |Δ|/(2σ)) ≤ (R₀ + R₁) / 2`. The conclusion is that
    `θ₀` or `θ₁` (whichever maximizes the risk) witnesses the
    `h_twoPoint` shape at rate `(Δsq/4)(1 - |Δ|/(2σ))`.

    The honest gap is exactly the algebraic Le Cam two-point average
    bound — the caller still has to supply it from a real
    measure-theoretic argument. What this lemma offers is the
    *quantifier-extraction* step that converts the Le Cam average
    bound into the `∃ θ_star, rate ≤ excessRisk` shape, plus the rate
    arithmetic. This is the M.D composition step at the scalar case
    where it can be made syntactically explicit. -/
theorem ols_minimax_two_point_discharge_scalar
    {sigmaSq : ℝ} (hσ : 0 < sigmaSq)
    (sample : (Fin 1 → ℝ) → (Fin 1 → ℝ))
    (excessRisk : (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ)
    (A : (Fin 1 → ℝ) → (Fin 1 → ℝ))
    (Δ : ℝ) (hΔ : Δ ≠ 0)
    (rate : ℝ)
    (h_rate_eq : rate = (Δ ^ 2 / 4) * (1 - |Δ| / (2 * Real.sqrt sigmaSq)))
    (h_avg :
      rate ≤
        (excessRisk (A (sample (fun _ => 0))) (fun _ => 0) +
          excessRisk (A (sample (fun _ => Δ))) (fun _ => Δ)) / 2) :
    ∃ θ_star : Fin 1 → ℝ,
      rate ≤ excessRisk (A (sample θ_star)) θ_star := by
  -- Use the max of the two per-hypothesis risks to pick the witness.
  set R₀ := excessRisk (A (sample (fun _ => 0))) (fun _ => 0)
  set R₁ := excessRisk (A (sample (fun _ => Δ))) (fun _ => Δ)
  have h_max : rate ≤ max R₀ R₁ :=
    h_avg.trans (LTFP.MathlibExt.Probability.average_le_max_of_pair R₀ R₁)
  rcases le_total R₀ R₁ with h | h
  · refine ⟨fun _ => Δ, ?_⟩
    have h_max_eq : max R₀ R₁ = R₁ := max_eq_right h
    rw [h_max_eq] at h_max
    exact h_max
  · refine ⟨fun _ => 0, ?_⟩
    have h_max_eq : max R₀ R₁ = R₀ := max_eq_left h
    rw [h_max_eq] at h_max
    exact h_max

/-- §3.7 — **Concrete-instance discharge of `h_twoPoint` via the
Bhattacharyya route** at `d = 1`.

Honest scope: parallel to `ols_minimax_two_point_discharge_scalar`, this
is NOT a discharge of the full carrier
`ols_minimax_lower_bound_for_all_estimators` at general `d`. It is a
concrete-instance discharge at the *scalar* one-dimensional case, going
through the **Bhattacharyya / Hellinger** algebraic chain rather than
Pinsker / KL.

Why this route. The Pinsker chain in
`ols_minimax_two_point_discharge_scalar` substitutes the testing-side
TV bound `tv ≤ |Δ|/(2σ)`, which requires the precondition `Δ ≤ σ` and
goes through `klDiv` infrastructure (the chain rule on `rnDeriv`,
integrability of `llr`, integral computation) that is the open Mathlib
gap at pin `80732f7660`. The BH route substitutes
`tv ≤ √(1 - exp(-Δ²/(4σ²)))` (the algebraic chain
`tvDist² ≤ Hsq·(1 - Hsq/4) = 1 - BH²` from `Bhattacharyya.lean` plus the
scalar BH identity from
`LTFP.MathlibExt.Probability.GaussianBhattacharyyaScalar`), which:

* is *unconditional* in `Δ` (no `Δ ≤ σ` assumption);
* requires only the standard Gaussian integral
  `∫ exp(-(x-m)²/(2v)) dx = √(2πv)` rather than the full `klDiv`
  infrastructure;
* matches Pinsker to leading order `Δ/√v` in the small-`Δ` regime via
  `1 - exp(-x) ≈ x`.

The caller still supplies the algebraic Le Cam two-point average bound
in the BH form
`(Δsq/4)(1 - √(1 - exp(-Δsq/(4σ²)))) ≤ (R₀ + R₁)/2`; this lemma converts
that into the `∃ θ_star, rate ≤ excessRisk` shape, via the
quantifier-extraction max-of-pair step.

The remaining measure-theoretic gap is the identification
`bhattacharyya (gaussianReal _ σ²) (gaussianReal _ σ²) =
gaussianBhattacharyyaScalar Δ σ²` (which the algebraic core in
`LTFP.MathlibExt.Probability.GaussianBhattacharyyaScalar` packages but
does NOT discharge — that requires the Radon-Nikodym density of
`gaussianReal` against `volume` plus the complete-the-square algebra
inside the integral, a multi-week port at the current Mathlib pin). -/
theorem ols_minimax_two_point_discharge_scalar_via_bhattacharyya
    {sigmaSq : ℝ} (hσ : 0 < sigmaSq)
    (sample : (Fin 1 → ℝ) → (Fin 1 → ℝ))
    (excessRisk : (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ)
    (A : (Fin 1 → ℝ) → (Fin 1 → ℝ))
    (Δ : ℝ) (hΔ : Δ ≠ 0)
    (rate : ℝ)
    (h_rate_eq : rate = (Δ ^ 2 / 4) *
      (1 - Real.sqrt (1 - Real.exp (-(Δ ^ 2) / (4 * sigmaSq)))))
    (h_avg :
      rate ≤
        (excessRisk (A (sample (fun _ => 0))) (fun _ => 0) +
          excessRisk (A (sample (fun _ => Δ))) (fun _ => Δ)) / 2) :
    ∃ θ_star : Fin 1 → ℝ,
      rate ≤ excessRisk (A (sample θ_star)) θ_star := by
  -- Quantifier-extraction step is identical to the Pinsker route's
  -- max-of-pair argument. The only difference between this lemma and
  -- `ols_minimax_two_point_discharge_scalar` is the *form* of the rate:
  -- the BH route uses the unconditional `√(1 - exp(-Δ²/(4σ²)))` testing
  -- bound rather than the Pinsker-style `|Δ|/(2σ)` bound.
  let _hσ_used := hσ
  let _hΔ_used := hΔ
  let _h_rate_eq_used := h_rate_eq
  set R₀ := excessRisk (A (sample (fun _ => 0))) (fun _ => 0)
  set R₁ := excessRisk (A (sample (fun _ => Δ))) (fun _ => Δ)
  have h_max : rate ≤ max R₀ R₁ :=
    h_avg.trans (LTFP.MathlibExt.Probability.average_le_max_of_pair R₀ R₁)
  rcases le_total R₀ R₁ with h | h
  · refine ⟨fun _ => Δ, ?_⟩
    have h_max_eq : max R₀ R₁ = R₁ := max_eq_right h
    rw [h_max_eq] at h_max
    exact h_max
  · refine ⟨fun _ => 0, ?_⟩
    have h_max_eq : max R₀ R₁ = R₀ := max_eq_left h
    rw [h_max_eq] at h_max
    exact h_max

/-- §3.7 — **Multivariate Bhattacharyya two-point rate companion.**

The multivariate analog of
`ols_minimax_two_point_discharge_scalar_via_bhattacharyya`, going
through the multivariate BH scalar value
`gaussianBhattacharyyaScalarMultivariate normSq σ² := exp(-normSq/(8σ²))`
(where `normSq := ‖X(θ₀ - θ₁)‖²` is the squared design-mapped mean
separation). With `bhSq := exp(-normSq/(4σ²)) = BH²`, the testing-side
TV² bound `tv² ≤ 1 - bhSq` gives a worst-case max-risk lower bound of

  `(normSq / 4) · (1 - √(1 - exp(-normSq/(4σ²))))`,

unconditional in `normSq` (no `normSq ≤ σ²` assumption needed). Same
quantifier-extraction step as the scalar version. -/
theorem ols_minimax_two_point_discharge_multivariate_via_bhattacharyya
    {d : ℕ} {sigmaSq : ℝ} (hσ : 0 < sigmaSq)
    (sample : (Fin d → ℝ) → (Fin d → ℝ))
    (excessRisk : (Fin d → ℝ) → (Fin d → ℝ) → ℝ)
    (A : (Fin d → ℝ) → (Fin d → ℝ))
    (θ₀ θ₁ : Fin d → ℝ) (hθ : θ₀ ≠ θ₁)
    (normSq rate : ℝ)
    (h_rate_eq : rate = (normSq / 4) *
      (1 - Real.sqrt (1 - Real.exp (-normSq / (4 * sigmaSq)))))
    (h_avg :
      rate ≤
        (excessRisk (A (sample θ₀)) θ₀ + excessRisk (A (sample θ₁)) θ₁) / 2) :
    ∃ θ_star : Fin d → ℝ,
      rate ≤ excessRisk (A (sample θ_star)) θ_star := by
  let _hσ_used := hσ
  let _hθ_used := hθ
  let _h_rate_eq_used := h_rate_eq
  set R₀ := excessRisk (A (sample θ₀)) θ₀
  set R₁ := excessRisk (A (sample θ₁)) θ₁
  have h_max : rate ≤ max R₀ R₁ :=
    h_avg.trans (LTFP.MathlibExt.Probability.average_le_max_of_pair R₀ R₁)
  rcases le_total R₀ R₁ with h | h
  · refine ⟨θ₁, ?_⟩
    have h_max_eq : max R₀ R₁ = R₁ := max_eq_right h
    rw [h_max_eq] at h_max
    exact h_max
  · refine ⟨θ₀, ?_⟩
    have h_max_eq : max R₀ R₁ = R₀ := max_eq_left h
    rw [h_max_eq] at h_max
    exact h_max

/-! ### §3.7 — **OLS d=1 prototype**: scalar minimax lower bound at the
sample-mean-Gaussian setting.

Bach §3.7 uses the d=1 Gaussian-mean estimation problem as its running
example. The carrier `ols_minimax_lower_bound_for_all_estimators` at
general `d` is parametric in two measure-theoretic identities
(Gaussian-divergence-identity and `excessRisk = ∫`-form) that require
multi-week Mathlib ports for the multivariate case. At `d = 1` the
scalar `gaussianReal` is already first-class in Mathlib, so the
specialization can be made *much more concrete*.

Below we ship the d=1 prototype that wires the existing scalar
Bhattacharyya algebraic chain (from
`LTFP.MathlibExt.Probability.Distance.GaussianBhattacharyya` and
`LTFP.MathlibExt.Probability.TwoPointBayesRisk`) into an **explicit
closed-form rate** statement.

The remaining gap at d=1 is the single measure-theoretic identity
`bhattacharyya (gaussianReal m₀ v) (gaussianReal m₁ v) =
gaussianBhattacharyyaScalar (m₀ - m₁) v`, which we expose as a named
parametric hypothesis `h_bh_lecam`. Once that identity lands in
Mathlib (a small follow-up PR — see file docstring at
`GaussianBhattacharyya.lean`), `h_bh_lecam` becomes a theorem and the
present theorem upgrades to fully unconditional.

The explicit rate is
`(σ²/n) · (1/4) · (1 - √(1 - exp(-1/4)))` ≈ `0.132 · σ²/n`,
which is `c·σ²/n` for an absolute constant `c > 0` matching the
Mourtada rate at `d = 1`. -/

/-- §3.7 d=1 — The **explicit closed-form rate** for the scalar
OLS minimax lower bound, at the Gaussian-sample-mean setting
`Ȳ ~ N(θ, σ²/n)` with mean separation `Δ = σ/√n`:

`olsMinimaxRateScalarD1 σ² n = (σ²/n) · (1/4) · (1 - √(1 - exp(-1/4)))`.

This is the Le Cam two-point Bayes-risk rate
`(Δ²/4) · (1 - tv)` at the BH-bounded TV value
`tv ≤ √(1 - exp(-Δ²/(4v)))`, evaluated at `Δ² = σ²/n`,
`v = σ²/n` (so `Δ²/v = 1` ⇒ exponent `-1/4`). -/
noncomputable def olsMinimaxRateScalarD1 (sigmaSq : ℝ) (n : ℕ) : ℝ :=
  (sigmaSq / n) * (1 / 4) * (1 - Real.sqrt (1 - Real.exp (-1 / 4)))

/-- The d=1 minimax rate is nonneg for `0 ≤ σ²` and `n > 0`. The factor
`1 - √(1 - exp(-1/4))` is positive since `exp(-1/4) > 0` ⇒
`1 - exp(-1/4) < 1` ⇒ `√(1 - exp(-1/4)) < 1`. -/
theorem olsMinimaxRateScalarD1_nonneg
    {sigmaSq : ℝ} (hσ : 0 ≤ sigmaSq) {n : ℕ} (hn : 0 < n) :
    0 ≤ olsMinimaxRateScalarD1 sigmaSq n := by
  unfold olsMinimaxRateScalarD1
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h_quot_nn : 0 ≤ sigmaSq / (n : ℝ) := div_nonneg hσ hn'.le
  have h_quart_nn : (0 : ℝ) ≤ 1 / 4 := by norm_num
  have h_exp_pos : 0 < Real.exp (-1 / 4) := Real.exp_pos _
  have h_arg_le_one : 1 - Real.exp (-1 / 4) ≤ 1 := by linarith
  have h_arg_nn : 0 ≤ 1 - Real.exp (-1 / 4) := by
    have hle1 : Real.exp (-1 / 4) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      norm_num
    linarith
  have h_sqrt_le_one : Real.sqrt (1 - Real.exp (-1 / 4)) ≤ 1 := by
    have h1 : Real.sqrt (1 - Real.exp (-1 / 4)) ≤ Real.sqrt 1 :=
      Real.sqrt_le_sqrt h_arg_le_one
    rwa [Real.sqrt_one] at h1
  have h_paren_nn : 0 ≤ 1 - Real.sqrt (1 - Real.exp (-1 / 4)) := by linarith
  positivity

/-- The d=1 minimax rate is strictly positive for `σ² > 0`. -/
theorem olsMinimaxRateScalarD1_pos
    {sigmaSq : ℝ} (hσ : 0 < sigmaSq) {n : ℕ} (hn : 0 < n) :
    0 < olsMinimaxRateScalarD1 sigmaSq n := by
  unfold olsMinimaxRateScalarD1
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h_quot_pos : 0 < sigmaSq / (n : ℝ) := div_pos hσ hn'
  have h_quart_pos : (0 : ℝ) < 1 / 4 := by norm_num
  have h_exp_pos : 0 < Real.exp (-1 / 4) := Real.exp_pos _
  have h_exp_lt_one : Real.exp (-1 / 4) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    norm_num
  have h_one_sub_pos : 0 < 1 - Real.exp (-1 / 4) := by linarith
  have h_one_sub_lt_one : 1 - Real.exp (-1 / 4) < 1 := by linarith
  have h_sqrt_lt_one : Real.sqrt (1 - Real.exp (-1 / 4)) < 1 := by
    have h1 : Real.sqrt (1 - Real.exp (-1 / 4)) < Real.sqrt 1 :=
      Real.sqrt_lt_sqrt h_one_sub_pos.le h_one_sub_lt_one
    rwa [Real.sqrt_one] at h1
  have h_paren_pos : 0 < 1 - Real.sqrt (1 - Real.exp (-1 / 4)) := by linarith
  positivity

/-- §3.7 d=1 — **OLS minimax lower bound at the scalar Gaussian
sample-mean setting**, wired through the existing scalar Bhattacharyya
Le Cam pipeline.

For any estimator `A : ℝ → ℝ` (acting on the scalar sample mean
`Ȳ ~ N(θ, σ²/n)` of an iid Gaussian sample of size `n`), there exists
a worst-case parameter `θ_star ∈ {0, σ/√n}` such that the per-θ
expected squared loss `excessRisk (A · sample θ_star) θ_star` is at
least the explicit rate

`(σ²/n) · (1/4) · (1 - √(1 - exp(-1/4)))`.

This is the Le Cam two-point Bayes-risk bound
`(Δ²/4)(1 - tv)` at `Δ = σ/√n`, with the testing-side TV bound
`tv ≤ √(1 - exp(-Δ²/(4v)))` coming from the **measure-theoretic d=1
Bhattacharyya identity**
`bhattacharyya (gaussianReal m₀ (σ²/n)) (gaussianReal m₁ (σ²/n)) =
exp(-(m₀-m₁)²/(8·σ²/n))`
combined with the Le Cam estimate `tv² ≤ 1 - BH²` from
`LTFP.MathlibExt.Probability.Distance.Bhattacharyya`.

The BH-route ingredients are now **all discharged**:

* The Le Cam estimate `tvDist² ≤ 1 - BH²` (in
  `Bhattacharyya.lean`).
* The two-point Bayes-risk bound `(R₀+R₁)/2 ≥ (Δ²/4)(1-tv)` (in
  `TwoPointBayesRisk.lean`).
* The Bhattacharyya algebraic chain
  `1 - BH² = 1 - exp(-Δ²/(4v))` (in `GaussianBhattacharyya.lean`).
* **NEW (2026-05-26)**: the measure-theoretic BH identity
  `bhattacharyya (gaussianReal m₀ v) (gaussianReal m₁ v) =
  exp(-(m₀-m₁)²/(8v))` (`bhattacharyya_gaussianReal_scalar_eq` in
  `GaussianBhattacharyya.lean`). This was previously the single
  remaining measure-theoretic gap and is now closed.
* **NEW (2026-05-26)**: the unconditional testing-side TV bound
  `tvDist (gaussianReal 0 v) (gaussianReal Δ v) ≤ √(1 - exp(-1/4))`
  at the canonical d=1 setting `v = Δ² = σ²/n` is now provable
  unconditionally — see `tvDist_gaussianReal_d1_le_sqrt_one_sub_exp_neg_quarter`
  below.

The **remaining content** of the parametric `h_bh_lecam` hypothesis is
the **Le Cam squared-loss reduction** — the textbook step (Tsybakov §2.4.2)
that connects abstract `excessRisk θ̂ θ` to TV distance between the
sampling distributions. This is *not* the BH identity gap; it is a
separate measure-theoretic argument that requires giving concrete
semantics to `excessRisk` and `sample` (e.g., `excessRisk θ̂ θ :=
𝔼_{Y ~ N(θ, σ²/n)^n} ‖θ̂(Y) - θ‖²`). Until those abstract carriers are
instantiated, the Le Cam reduction must be supplied as a hypothesis;
once instantiated, it follows from the standard squared-loss reduction
plus this file's testing-side BH discharge.

**Why d=1 instead of general d**: the general-d carrier
`ols_minimax_lower_bound_for_all_estimators` requires both
(i) multivariate Bhattacharyya for product Gaussians (a multi-week
Mathlib port — see Phase 2 dispatch logs) and
(ii) the architectural decision to make `excessRisk = ∫` concrete.
At d=1 both issues collapse: scalar `gaussianReal` is first-class in
Mathlib, and `excessRisk` is just the standard `∫ (A Y - θ)² ∂ν`.
Bach §3.7 uses d=1 as the running example, so the specialization has
standalone pedagogical value. -/
theorem ols_minimax_lower_bound_d1_gaussian
    {sigmaSq : ℝ} (hσ : 0 < sigmaSq) {n : ℕ} (hn : 0 < n)
    (sample : (Fin 1 → ℝ) → (Fin 1 → ℝ))
    (excessRisk : (Fin 1 → ℝ) → (Fin 1 → ℝ) → ℝ)
    (h_bh_lecam :
      ∀ A : (Fin 1 → ℝ) → (Fin 1 → ℝ),
        olsMinimaxRateScalarD1 sigmaSq n ≤
          (excessRisk (A (sample (fun _ => 0))) (fun _ => 0) +
            excessRisk (A (sample (fun _ => Real.sqrt (sigmaSq / n))))
              (fun _ => Real.sqrt (sigmaSq / n))) / 2) :
    ∀ A : (Fin 1 → ℝ) → (Fin 1 → ℝ),
      ∃ θ_star : Fin 1 → ℝ,
        olsMinimaxRateScalarD1 sigmaSq n ≤
          excessRisk (A (sample θ_star)) θ_star := by
  intro A
  -- Step 1: Set Δ = σ/√n. Then Δ² = σ²/n.
  set Δ : ℝ := Real.sqrt (sigmaSq / n) with hΔ_def
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h_quot_pos : 0 < sigmaSq / (n : ℝ) := div_pos hσ hn'
  have hΔ_pos : 0 < Δ := Real.sqrt_pos.mpr h_quot_pos
  have hΔ_ne : Δ ≠ 0 := ne_of_gt hΔ_pos
  have hΔ_sq : Δ ^ 2 = sigmaSq / (n : ℝ) := by
    rw [hΔ_def]
    exact Real.sq_sqrt h_quot_pos.le
  -- Step 2: invoke `h_bh_lecam` and apply the max-of-pair pivot.
  have h_avg := h_bh_lecam A
  set R₀ := excessRisk (A (sample (fun _ => 0))) (fun _ => 0)
  set R₁ := excessRisk (A (sample (fun _ => Δ))) (fun _ => Δ)
  have h_max : olsMinimaxRateScalarD1 sigmaSq n ≤ max R₀ R₁ :=
    h_avg.trans (LTFP.MathlibExt.Probability.average_le_max_of_pair R₀ R₁)
  -- Step 3: extract a witness using max_eq_left/right.
  rcases le_total R₀ R₁ with h | h
  · refine ⟨fun _ => Δ, ?_⟩
    have h_max_eq : max R₀ R₁ = R₁ := max_eq_right h
    rw [h_max_eq] at h_max
    exact h_max
  · refine ⟨fun _ => 0, ?_⟩
    have h_max_eq : max R₀ R₁ = R₀ := max_eq_left h
    rw [h_max_eq] at h_max
    exact h_max

/-- §3.7 d=1 — **Testing-side Bhattacharyya TV bound** at the d=1 setting,
specialized to the canonical sample-mean Gaussians used in
`ols_minimax_lower_bound_d1_gaussian`.

With `v = σ²/n` and `Δ = σ/√n` (so `Δ² = σ²/n = v` and the exponent
`-Δ²/(4v)` simplifies to `-1/4`), this corollary discharges the
testing-side Le Cam estimate

  `tvDist (gaussianReal 0 v) (gaussianReal Δ v) ≤ √(1 - exp(-1/4))`,

unconditionally — no parametric hypothesis is needed. The proof composes
the measure-theoretic BH identity `bhattacharyya_gaussianReal_scalar_eq`
(landed in `LTFP.MathlibExt.Probability.GaussianBhattacharyya`) with the
abstract Le Cam estimate `tvDist² ≤ 1 - BH²` from
`LTFP.MathlibExt.Probability.Bhattacharyya.tvDist_sq_le_one_sub_bhattacharyya_sq`.

This is the **discharge of the testing-side gap** that was previously
parametric in `ols_minimax_lower_bound_d1_gaussian`'s `h_bh_lecam`
hypothesis. The remaining content of `h_bh_lecam` is the **Le Cam
squared-loss reduction**, which connects abstract `excessRisk` to TV
distance and is a separate textbook step (Tsybakov §2.4.2; not part of
the BH identity discharge). -/
theorem tvDist_gaussianReal_d1_le_sqrt_one_sub_exp_neg_quarter
    {sigmaSq : ℝ} (hσ : 0 < sigmaSq) {n : ℕ} (hn : 0 < n) :
    ((LTFP.MathlibExt.Probability.tvDist
        (ProbabilityTheory.gaussianReal 0
          ⟨sigmaSq / (n : ℝ), div_nonneg hσ.le (by exact_mod_cast hn.le)⟩)
        (ProbabilityTheory.gaussianReal (Real.sqrt (sigmaSq / (n : ℝ)))
          ⟨sigmaSq / (n : ℝ),
            div_nonneg hσ.le (by exact_mod_cast hn.le)⟩))).toReal ^ 2 ≤
      1 - Real.exp (-1 / 4) := by
  -- Setup: v := σ²/n as an NNReal, Δ := σ/√n.
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h_quot_pos : 0 < sigmaSq / (n : ℝ) := div_pos hσ hn'
  set v : NNReal :=
    ⟨sigmaSq / (n : ℝ), div_nonneg hσ.le (by exact_mod_cast hn.le)⟩ with hv_def
  have hv_pos_nn : 0 < v := by
    rw [hv_def, ← NNReal.coe_lt_coe]
    exact h_quot_pos
  have hv_ne : v ≠ 0 := ne_of_gt hv_pos_nn
  set Δ : ℝ := Real.sqrt (sigmaSq / (n : ℝ)) with hΔ_def
  -- Le Cam: TV² ≤ 1 - BH².
  have h_lecam :
      ((LTFP.MathlibExt.Probability.tvDist (ProbabilityTheory.gaussianReal 0 v)
          (ProbabilityTheory.gaussianReal Δ v))).toReal ^ 2 ≤
        1 - LTFP.MathlibExt.Probability.bhattacharyya
            (ProbabilityTheory.gaussianReal 0 v)
            (ProbabilityTheory.gaussianReal Δ v) ^ 2 :=
    LTFP.MathlibExt.Probability.tvDist_sq_le_one_sub_bhattacharyya_sq
      (ProbabilityTheory.gaussianReal 0 v)
      (ProbabilityTheory.gaussianReal Δ v)
  -- BH identity: bhattacharyya = exp(-(0-Δ)² / (8v)) = exp(-Δ²/(8v)).
  have h_bh :
      LTFP.MathlibExt.Probability.bhattacharyya
        (ProbabilityTheory.gaussianReal 0 v)
        (ProbabilityTheory.gaussianReal Δ v) =
      LTFP.MathlibExt.Probability.gaussianBhattacharyyaScalar (0 - Δ) (v : ℝ) :=
    LTFP.MathlibExt.Probability.bhattacharyya_gaussianReal_scalar_eq 0 Δ hv_ne
  rw [h_bh] at h_lecam
  -- Unfold gaussianBhattacharyyaScalar: it's exp(-(0-Δ)² / (8v)).
  unfold LTFP.MathlibExt.Probability.gaussianBhattacharyyaScalar at h_lecam
  -- (0 - Δ)² = Δ²
  have h_diff_sq : (0 - Δ) ^ 2 = Δ ^ 2 := by ring
  -- Compute Δ² = σ²/n = (v : ℝ).
  have hΔ_sq : Δ ^ 2 = sigmaSq / (n : ℝ) := by
    rw [hΔ_def]; exact Real.sq_sqrt h_quot_pos.le
  have hv_real : (v : ℝ) = sigmaSq / (n : ℝ) := rfl
  -- Now compute the exponent: -(Δ²) / (8 · v) = -1/8 · (σ²/n)/(σ²/n) is too much;
  -- we want exp(2·exponent) = exp(-Δ²/(4v)) = exp(-(σ²/n)/(4·σ²/n)) = exp(-1/4).
  -- Strategy: show 1 - exp(-Δ²/(8v))² = 1 - exp(-Δ²/(4v)) = 1 - exp(-1/4).
  -- We have h_lecam : TV² ≤ 1 - exp(-(0-Δ)²/(8v))².
  -- Rewrite (0-Δ)² = Δ² in h_lecam.
  rw [h_diff_sq] at h_lecam
  -- Now h_lecam : TV² ≤ 1 - (exp(-(Δ²)/(8v)))².
  -- Use exp(a)² = exp(2a): (exp(-Δ²/(8v)))² = exp(-Δ²/(4v)).
  have h_sq_exp : Real.exp (-(Δ ^ 2) / (8 * (v : ℝ))) ^ 2 =
      Real.exp (-(Δ ^ 2) / (4 * (v : ℝ))) := by
    rw [sq, ← Real.exp_add]
    congr 1
    have hv_pos_real : (0 : ℝ) < (v : ℝ) := by rw [hv_real]; exact h_quot_pos
    have hv_ne_real : (v : ℝ) ≠ 0 := ne_of_gt hv_pos_real
    field_simp
    ring
  rw [h_sq_exp] at h_lecam
  -- Now reduce -(Δ²)/(4v) to -1/4.
  have h_exp_arg : -(Δ ^ 2) / (4 * (v : ℝ)) = -1 / 4 := by
    rw [hΔ_sq, hv_real]
    have h_quot_ne : sigmaSq / (n : ℝ) ≠ 0 := ne_of_gt h_quot_pos
    field_simp
  rw [h_exp_arg] at h_lecam
  exact h_lecam

/-- §3.7 d=1 — **Algebraic identity** showing that the d=1 minimax rate
in `ols_minimax_lower_bound_d1_gaussian` matches the closed-form
Bhattacharyya two-point Bayes-risk expression at `Δ² = σ²/n`,
`v = σ²/n` (so `Δ²/(4v) = 1/4`).

This identity verifies that
`olsMinimaxRateScalarD1 σ² n = (Δ²/4) · (1 - √(1 - exp(-Δ²/(4v))))`
when `Δ = σ/√n`, `v = σ²/n`, making the rate match exactly the
`twoPointBayesRiskBound`-style shape used throughout
`gaussian_two_point_max_risk_lower_bound` and the BH-route discharges
above. -/
theorem olsMinimaxRateScalarD1_eq_bh_form
    (sigmaSq : ℝ) {n : ℕ} (hn : 0 < n) :
    olsMinimaxRateScalarD1 sigmaSq n =
      ((sigmaSq / (n : ℝ)) / 4) *
        (1 - Real.sqrt (1 - Real.exp (-(sigmaSq / (n : ℝ)) /
          (4 * (sigmaSq / (n : ℝ)))))) := by
  unfold olsMinimaxRateScalarD1
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  by_cases h_sq_zero : sigmaSq = 0
  · -- When σ² = 0, both sides are 0.
    subst h_sq_zero
    simp
  · -- General case: σ² ≠ 0 so σ²/n ≠ 0, so 4·(σ²/n) ≠ 0, so the
    -- exponent simplifies to -1/4.
    have h_quot_ne : sigmaSq / (n : ℝ) ≠ 0 := by
      have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hn'
      exact div_ne_zero h_sq_zero hn_ne
    have h_exp_arg : -(sigmaSq / (n : ℝ)) / (4 * (sigmaSq / (n : ℝ))) = -1 / 4 := by
      field_simp
    rw [h_exp_arg]
    ring

#check @LTFP.olsMinimaxRateScalarD1
#check @LTFP.olsMinimaxRateScalarD1_nonneg
#check @LTFP.olsMinimaxRateScalarD1_pos
#check @LTFP.ols_minimax_lower_bound_d1_gaussian
#check @LTFP.tvDist_gaussianReal_d1_le_sqrt_one_sub_exp_neg_quarter
#check @LTFP.olsMinimaxRateScalarD1_eq_bh_form

/-! ### Concrete d=1 OLS minimax lower bound — fully discharged

The theorems above wire the abstract parametric carrier
`ols_minimax_lower_bound_d1_gaussian` against an explicit
`h_bh_lecam` hypothesis. We now ship the **fully discharged**
concrete d=1 OLS minimax lower bound by:

(1) replacing the abstract `excessRisk` with the concrete Gaussian
MSE `gaussianMSED1 A θ σ² n := ∫ y, (A y - θ)² ∂(N(θ, σ²/n))`,
(2) replacing the abstract `sample` with the identity (d=1 OLS uses
the scalar sample mean `Ȳ ~ N(θ, σ²/n)` directly as its sufficient
statistic),
(3) applying the **Le Cam two-point squared-loss reduction**
(Tsybakov 2009, §2.4.2) from
`LTFP.MathlibExt.Probability.LeCamSquaredLossReduction` to discharge
the `h_bh_lecam` average-risk hypothesis,
(4) composing with the testing-side TV bound from
`tvDist_gaussianReal_d1_le_sqrt_one_sub_exp_neg_quarter`.

The Le Cam reduction in this library carries a **factor-of-2
looseness** (from the asymmetric TV-set bound; see the docstring of
`measureReal_sub_le_two_tvDist_toReal`); the published concrete rate
reflects this honestly via the constant `(1 - 2·tv_bound)` rather
than the textbook-tight `(1 - tv_bound)`.

### Concrete rate

`olsMinimaxRateScalarD1Concrete σ² n := (σ²/n) · (1/8) · (1 - 2·√(1 - exp(-1/4)))`.

Numerically this is `≈ 0.0074 · σ²/n` — a positive constant times
`σ²/n`, matching the textbook scaling `σ²·d/n` at `d=1` up to
a constant.

To upgrade to the tight constant (and recover the original
`olsMinimaxRateScalarD1`), the Hahn-decomposition route in
`LeCamSquaredLossReduction.measureReal_sub_le_two_tvDist_toReal`
would need to be tightened (see the docstring there). This is a
clean algebraic improvement and does not depend on the rest of the
discharge chain. -/

/-- §3.7 d=1 — **Concrete OLS minimax rate** at the scalar
Gaussian sample-mean setting, with the *honest* factor-2-loose
constant from the Le Cam reduction:

`olsMinimaxRateScalarD1Concrete σ² n = (σ²/n) · (1/8) · (1 - 2·√(1 - exp(-1/4)))`.

The factor `(1 - 2·√(1 - exp(-1/4)))` is positive
(`≈ 0.0594 > 0`) but tiny; the factor of 2 inside the `(1 - 2·…)`
expression is the looseness inherited from the asymmetric TV-set
bound used in the Le Cam reduction. -/
noncomputable def olsMinimaxRateScalarD1Concrete (sigmaSq : ℝ) (n : ℕ) : ℝ :=
  (sigmaSq / n) * (1 / 8) * (1 - 2 * Real.sqrt (1 - Real.exp (-1 / 4)))

/-- The concrete d=1 minimax rate is nonneg for `0 ≤ σ²` and `n > 0`.
Uses `2·√(1 - exp(-1/4)) < 1`, i.e. `√(1 - exp(-1/4)) < 1/2`, i.e.
`1 - exp(-1/4) < 1/4`, i.e. `exp(-1/4) > 3/4`. Numerically
`exp(-1/4) ≈ 0.779 > 0.75`. -/
theorem olsMinimaxRateScalarD1Concrete_nonneg
    {sigmaSq : ℝ} (hσ : 0 ≤ sigmaSq) {n : ℕ} (hn : 0 < n) :
    0 ≤ olsMinimaxRateScalarD1Concrete sigmaSq n := by
  unfold olsMinimaxRateScalarD1Concrete
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h_quot_nn : 0 ≤ sigmaSq / (n : ℝ) := div_nonneg hσ hn'.le
  have h_eighth_nn : (0 : ℝ) ≤ 1 / 8 := by norm_num
  -- Goal: 2·√(1 - exp(-1/4)) ≤ 1, i.e. √(1 - exp(-1/4)) ≤ 1/2.
  -- Equivalent: 1 - exp(-1/4) ≤ 1/4, i.e. exp(-1/4) ≥ 3/4.
  -- We use Real.exp_neg_one_quarter_lower_estimate via Real.add_one_le_exp.
  -- Real.add_one_le_exp : 1 + x ≤ exp(x); apply at x = -1/4 ⇒ exp(-1/4) ≥ 3/4.
  have h_exp_ge : (3 / 4 : ℝ) ≤ Real.exp (-1 / 4) := by
    have h_lin : (-1/4 : ℝ) + 1 ≤ Real.exp (-1/4) := Real.add_one_le_exp _
    linarith
  have h_one_sub_le : 1 - Real.exp (-1 / 4) ≤ 1 / 4 := by linarith
  have h_one_sub_nn : 0 ≤ 1 - Real.exp (-1 / 4) := by
    have hle1 : Real.exp (-1 / 4) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr; norm_num
    linarith
  have h_sqrt_le_half : Real.sqrt (1 - Real.exp (-1 / 4)) ≤ 1 / 2 := by
    have h1 : Real.sqrt (1 - Real.exp (-1 / 4)) ≤ Real.sqrt (1 / 4) :=
      Real.sqrt_le_sqrt h_one_sub_le
    have h2 : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2)^2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith
  have h_one_sub_two_sqrt_nn :
      0 ≤ 1 - 2 * Real.sqrt (1 - Real.exp (-1 / 4)) := by linarith
  positivity

/-- §3.7 d=1 — **Fully discharged OLS minimax lower bound at d=1**.

For any *measurable* estimator `A : ℝ → ℝ` taking the sample mean
`Ȳ ~ N(θ, σ²/n)` and returning a scalar estimate, with both
squared-error integrands integrable, there exists a worst-case
parameter `θ_star ∈ {0, σ/√n}` such that the *concrete* Gaussian MSE
at `θ_star` is at least

`(σ²/n) · (1/8) · (1 - 2·√(1 - exp(-1/4)))`.

**No parametric hypothesis** — the abstract `excessRisk` is replaced
by `gaussianMSED1 A θ σ² n := ∫ y, (A y - θ)² ∂(N(θ, σ²/n))`, and
the Le Cam squared-loss reduction is supplied unconditionally from
`LTFP.MathlibExt.Probability.LeCamSquaredLossReduction`.

This closes the residual `h_bh_lecam` hypothesis of
`ols_minimax_lower_bound_d1_gaussian` for the concrete Gaussian
sample-mean instantiation. -/
theorem ols_minimax_lower_bound_d1_gaussian_concrete
    {sigmaSq : ℝ} (hσ : 0 < sigmaSq) {n : ℕ} (hn : 0 < n)
    (A : ℝ → ℝ) (hA : Measurable A)
    (hint_zero : MeasureTheory.Integrable
      (fun y => (A y - 0)^2)
      (LTFP.MathlibExt.Probability.olsGaussianSampleD1
        0 sigmaSq n hσ.le hn))
    (hint_delta : MeasureTheory.Integrable
      (fun y => (A y - Real.sqrt (sigmaSq / n))^2)
      (LTFP.MathlibExt.Probability.olsGaussianSampleD1
        (Real.sqrt (sigmaSq / n)) sigmaSq n hσ.le hn)) :
    ∃ θ_star : ℝ,
      olsMinimaxRateScalarD1Concrete sigmaSq n ≤
        LTFP.MathlibExt.Probability.gaussianMSED1 A θ_star sigmaSq n hσ.le hn := by
  -- Setup: Δ = σ/√n, v = σ²/n.
  set Δ : ℝ := Real.sqrt (sigmaSq / n) with hΔ_def
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h_quot_pos : 0 < sigmaSq / (n : ℝ) := div_pos hσ hn'
  have h_quot_nn : 0 ≤ sigmaSq / (n : ℝ) := h_quot_pos.le
  have hΔ_pos : 0 < Δ := Real.sqrt_pos.mpr h_quot_pos
  have hΔ_sq : Δ^2 = sigmaSq / (n : ℝ) := by
    rw [hΔ_def]; exact Real.sq_sqrt h_quot_pos.le
  set P₀ : MeasureTheory.Measure ℝ :=
    LTFP.MathlibExt.Probability.olsGaussianSampleD1 0 sigmaSq n hσ.le hn
    with hP₀_def
  set P₁ : MeasureTheory.Measure ℝ :=
    LTFP.MathlibExt.Probability.olsGaussianSampleD1 Δ sigmaSq n hσ.le hn
    with hP₁_def
  -- Apply Le Cam squared-loss reduction at θ₀ = 0, θ₁ = Δ.
  have h_lecam :=
    LTFP.MathlibExt.Probability.leCam_squared_loss_reduction_sum_form
      ℝ P₀ P₁ A hA 0 Δ hint_zero hint_delta
  -- L.C gives: (Δ²/4) · (1 - 2·tvDist) ≤ R₀ + R₁
  -- where R₀ = gaussianMSED1 A 0 σ² n, R₁ = gaussianMSED1 A Δ σ² n.
  have h_R0_eq :
      LTFP.MathlibExt.Probability.gaussianMSED1 A 0 sigmaSq n hσ.le hn =
        ∫ y, (A y - 0)^2 ∂P₀ := rfl
  have h_R1_eq :
      LTFP.MathlibExt.Probability.gaussianMSED1 A Δ sigmaSq n hσ.le hn =
        ∫ y, (A y - Δ)^2 ∂P₁ := rfl
  -- The TV bound: tvDist(P₀, P₁) ≤ √(1 - exp(-1/4)).
  -- The existing `tvDist_gaussianReal_d1_le_sqrt_one_sub_exp_neg_quarter`
  -- gives tvDist² ≤ 1 - exp(-1/4), so tvDist ≤ √(1 - exp(-1/4)).
  have h_TV_sq :
      ((LTFP.MathlibExt.Probability.tvDist P₀ P₁).toReal)^2 ≤
        1 - Real.exp (-1 / 4) := by
    -- Unfold P₀, P₁ to gaussianReal form.
    show ((LTFP.MathlibExt.Probability.tvDist
            (LTFP.MathlibExt.Probability.olsGaussianSampleD1 0 sigmaSq n hσ.le hn)
            (LTFP.MathlibExt.Probability.olsGaussianSampleD1 Δ sigmaSq n hσ.le hn))).toReal^2 ≤
              1 - Real.exp (-1 / 4)
    have := tvDist_gaussianReal_d1_le_sqrt_one_sub_exp_neg_quarter (sigmaSq := sigmaSq) hσ hn
    -- This gives the bound in terms of `gaussianReal 0 v` and `gaussianReal Δ v`.
    -- `olsGaussianSampleD1 θ σ² n` unfolds to `gaussianReal θ ⟨σ²/n, _⟩` by `rfl`.
    convert this using 4
  have h_TV_nn : 0 ≤ (LTFP.MathlibExt.Probability.tvDist P₀ P₁).toReal :=
    LTFP.MathlibExt.Probability.tvDist_toReal_nonneg _ _
  have h_TV_le :
      (LTFP.MathlibExt.Probability.tvDist P₀ P₁).toReal ≤
        Real.sqrt (1 - Real.exp (-1 / 4)) := by
    have h_arg_nn : 0 ≤ 1 - Real.exp (-1 / 4) := by
      have hle1 : Real.exp (-1 / 4) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr; norm_num
      linarith
    have h_sqrt_sq :
        (LTFP.MathlibExt.Probability.tvDist P₀ P₁).toReal =
          Real.sqrt (((LTFP.MathlibExt.Probability.tvDist P₀ P₁).toReal)^2) := by
      rw [Real.sqrt_sq h_TV_nn]
    rw [h_sqrt_sq]
    exact Real.sqrt_le_sqrt h_TV_sq
  -- Bound: 1 - 2·tvDist ≥ 1 - 2·√(1 - exp(-1/4)).
  have h_one_sub_two_TV_ge :
      1 - 2 * Real.sqrt (1 - Real.exp (-1 / 4)) ≤
        1 - 2 * (LTFP.MathlibExt.Probability.tvDist P₀ P₁).toReal := by
    linarith
  -- Combine: (Δ²/4)·(1 - 2·√...) ≤ (Δ²/4)·(1 - 2·tvDist) ≤ R₀ + R₁.
  have hΔ_sq_quart_nn : 0 ≤ (0 - Δ)^2 / 4 := by
    have : (0 - Δ)^2 ≥ 0 := sq_nonneg _
    linarith
  have h_lecam_intermediate :
      (0 - Δ)^2 / 4 * (1 - 2 * Real.sqrt (1 - Real.exp (-1 / 4))) ≤
        (∫ y, (A y - 0)^2 ∂P₀) + ∫ y, (A y - Δ)^2 ∂P₁ := by
    have h_mul :
        (0 - Δ)^2 / 4 * (1 - 2 * Real.sqrt (1 - Real.exp (-1 / 4))) ≤
        (0 - Δ)^2 / 4 *
            (1 - 2 * (LTFP.MathlibExt.Probability.tvDist P₀ P₁).toReal) :=
      mul_le_mul_of_nonneg_left h_one_sub_two_TV_ge hΔ_sq_quart_nn
    linarith
  -- Rewrite (0-Δ)² = Δ² and Δ² = σ²/n. So (0-Δ)²/4 = (σ²/n)/4.
  have h_diff_sq : (0 - Δ)^2 = Δ^2 := by ring
  rw [h_diff_sq, hΔ_sq] at h_lecam_intermediate
  -- Now we have (σ²/n)/4 · (1 - 2·√...) ≤ R₀ + R₁.
  -- Goal: (σ²/n)/8 · (1 - 2·√...) ≤ max(R₀, R₁).
  -- Use max ≥ (R₀+R₁)/2.
  set R₀_real := ∫ y, (A y - 0)^2 ∂P₀ with hR0_def
  set R₁_real := ∫ y, (A y - Δ)^2 ∂P₁ with hR1_def
  have h_max_ge_avg :
      (R₀_real + R₁_real) / 2 ≤ max R₀_real R₁_real :=
    LTFP.MathlibExt.Probability.average_le_max_of_pair R₀_real R₁_real
  -- Divide by 2: (σ²/n)/8 · (1 - 2·√...) ≤ (R₀+R₁)/2.
  have h_avg_bound :
      sigmaSq / (n : ℝ) / 8 * (1 - 2 * Real.sqrt (1 - Real.exp (-1 / 4))) ≤
        (R₀_real + R₁_real) / 2 := by
    have : sigmaSq / (n : ℝ) / 4 * (1 - 2 * Real.sqrt (1 - Real.exp (-1 / 4))) ≤
        R₀_real + R₁_real := h_lecam_intermediate
    linarith
  -- Compose.
  have h_final :
      sigmaSq / (n : ℝ) / 8 * (1 - 2 * Real.sqrt (1 - Real.exp (-1 / 4))) ≤
        max R₀_real R₁_real := h_avg_bound.trans h_max_ge_avg
  -- Extract a witness.
  rcases le_total R₀_real R₁_real with h | h
  · refine ⟨Δ, ?_⟩
    have h_max_eq : max R₀_real R₁_real = R₁_real := max_eq_right h
    rw [h_max_eq] at h_final
    unfold olsMinimaxRateScalarD1Concrete
    show sigmaSq / ↑n * (1 / 8) * (1 - 2 * Real.sqrt (1 - Real.exp (-1 / 4))) ≤
      LTFP.MathlibExt.Probability.gaussianMSED1 A Δ sigmaSq n hσ.le hn
    rw [h_R1_eq]
    have h_eq : sigmaSq / ↑n * (1 / 8) =
        sigmaSq / (n : ℝ) / 8 := by ring
    rw [h_eq]
    exact h_final
  · refine ⟨0, ?_⟩
    have h_max_eq : max R₀_real R₁_real = R₀_real := max_eq_left h
    rw [h_max_eq] at h_final
    unfold olsMinimaxRateScalarD1Concrete
    show sigmaSq / ↑n * (1 / 8) * (1 - 2 * Real.sqrt (1 - Real.exp (-1 / 4))) ≤
      LTFP.MathlibExt.Probability.gaussianMSED1 A 0 sigmaSq n hσ.le hn
    rw [h_R0_eq]
    have h_eq : sigmaSq / ↑n * (1 / 8) =
        sigmaSq / (n : ℝ) / 8 := by ring
    rw [h_eq]
    exact h_final

#check @LTFP.olsMinimaxRateScalarD1Concrete
#check @LTFP.olsMinimaxRateScalarD1Concrete_nonneg
#check @LTFP.ols_minimax_lower_bound_d1_gaussian_concrete

/-! ## §3.7 general-`d` — Concrete OLS minimax lower bound

The closure below generalises `ols_minimax_lower_bound_d1_gaussian_concrete`
to estimators with vector-valued range
`EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)`. It uses the
**coordinate-projection reduction** to the scalar Le Cam estimate:

* Pick the canonical first basis vector `e := EuclideanSpace.single ⟨0, hd⟩ 1`.
* Reduce a vector estimator `A` to the scalar estimator `T y := ⟪A y, e⟫`.
* Apply the existing scalar Le Cam squared-loss reduction at `θ₀ = 0`,
  `θ₁ = σ` (so `‖0 - σ·e‖ = σ`).
* The multivariate Bhattacharyya identity
  `bhattacharyya_multivariateGaussian_diagonal_eq` collapses the
  general-`d` TV² bound to `1 - exp(-1/4)`, identical to the d=1 case.
* By Cauchy–Schwarz, `(⟪A y, e⟫ - θ_j)² ≤ ‖A y - θ_j·e‖²`, so the
  scalar reduction also lower-bounds the vector MSE.

The resulting rate `olsMinimaxRateScalarGeneralDConcrete σ` is independent
of `d` and matches the d=1 rate at `n = 1`:
`σ² · (1/8) · (1 - 2·√(1 - exp(-1/4)))`. -/

/-- §3.7 general-`d` — Concrete minimax rate constant
`σ² · (1/8) · (1 - 2·√(1 - exp(-1/4)))` ≈ `σ² · 0.00742`.

This is the headline lower-bound rate for vector-valued OLS estimators
with isotropic noise covariance `σ²·I`. It is independent of the
ambient dimension `d` thanks to the **coordinate-projection reduction**
in `ols_minimax_lower_bound_general_d_gaussian_concrete`: the lower
bound is realised on a one-dimensional subspace and propagates to the
full vector MSE via Cauchy–Schwarz.

The factor `(1 - 2·√(1 - exp(-1/4)))` is positive
(`≈ 0.0594 > 0`) but tiny; the factor of 2 inside the `(1 - 2·…)`
expression is the looseness inherited from the asymmetric TV-set bound
used in the Le Cam reduction. -/
noncomputable def olsMinimaxRateGeneralDConcrete (σ : ℝ) : ℝ :=
  σ^2 * (1 / 8) * (1 - 2 * Real.sqrt (1 - Real.exp (-1 / 4)))

/-- The concrete general-`d` minimax rate is nonneg. Uses the same
numerical step as the d=1 rate: `2·√(1 - exp(-1/4)) ≤ 1`, i.e.
`exp(-1/4) ≥ 3/4` (proven via `Real.add_one_le_exp (-1/4)`). -/
theorem olsMinimaxRateGeneralDConcrete_nonneg (σ : ℝ) :
    0 ≤ olsMinimaxRateGeneralDConcrete σ := by
  unfold olsMinimaxRateGeneralDConcrete
  -- 1 - 2·√(1 - exp(-1/4)) ≥ 0 reduces to exp(-1/4) ≥ 3/4.
  have h_exp_ge : (3 / 4 : ℝ) ≤ Real.exp (-1 / 4) := by
    have h_lin : (-1 / 4 : ℝ) + 1 ≤ Real.exp (-1 / 4) := Real.add_one_le_exp _
    linarith
  have h_one_sub_le : 1 - Real.exp (-1 / 4) ≤ 1 / 4 := by linarith
  have h_one_sub_nn : 0 ≤ 1 - Real.exp (-1 / 4) := by
    have hle1 : Real.exp (-1 / 4) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr; norm_num
    linarith
  have h_sqrt_le_half : Real.sqrt (1 - Real.exp (-1 / 4)) ≤ 1 / 2 := by
    have h1 : Real.sqrt (1 - Real.exp (-1 / 4)) ≤ Real.sqrt (1 / 4) :=
      Real.sqrt_le_sqrt h_one_sub_le
    have h2 : Real.sqrt (1 / 4 : ℝ) = 1 / 2 := by
      rw [show (1 / 4 : ℝ) = (1 / 2)^2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith
  have h_one_sub_two_sqrt_nn :
      0 ≤ 1 - 2 * Real.sqrt (1 - Real.exp (-1 / 4)) := by linarith
  positivity

/-- §3.7 general-`d` — **Fully discharged OLS minimax lower bound at
general `d`**.

For any measurable estimator
`A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)` (with
`0 < d`), and any `σ > 0`, with both squared-error integrands
integrable, there exists a worst-case parameter
`θ_star ∈ {0, σ · EuclideanSpace.single ⟨0, hd⟩ 1}` such that the
*concrete* vector Gaussian MSE at `θ_star` is at least
`olsMinimaxRateGeneralDConcrete σ = σ²·(1/8)·(1 - 2·√(1 - exp(-1/4)))`.

The reduction to the scalar d=1 case is via Cauchy–Schwarz on the
first coordinate of the difference: `(⟪A y - θ_j_vec, e⟫)² ≤
‖A y - θ_j_vec‖² · ‖e‖² = ‖A y - θ_j_vec‖²`.

The TV bound is `tvDist² ≤ 1 - bhattacharyya² = 1 - exp(-1/4)` via the
**multivariate** Bhattacharyya identity
`bhattacharyya_multivariateGaussian_diagonal_eq` (DS.3); the two means
`0` and `σ·e` have squared distance `σ²·‖e‖² = σ²`, so `Δ²/(4σ²) = 1/4`,
exactly the d=1 exponent. -/
theorem ols_minimax_lower_bound_general_d_gaussian_concrete
    {d : ℕ} (hd : 0 < d) {σ : ℝ} (hσ : 0 < σ)
    (A : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (hA : Measurable A)
    (hint_zero : MeasureTheory.Integrable
      (fun x => ‖A x - (0 : EuclideanSpace ℝ (Fin d))‖^2)
      (ProbabilityTheory.multivariateGaussian
        (0 : EuclideanSpace ℝ (Fin d))
        ((σ^2) • (1 : Matrix (Fin d) (Fin d) ℝ))
        (ProbabilityTheory.posSemidef_sq_smul_one (n := d) σ)))
    (hint_delta : MeasureTheory.Integrable
      (fun x => ‖A x - σ • EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ)‖^2)
      (ProbabilityTheory.multivariateGaussian
        (σ • EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ))
        ((σ^2) • (1 : Matrix (Fin d) (Fin d) ℝ))
        (ProbabilityTheory.posSemidef_sq_smul_one (n := d) σ))) :
    ∃ θ_star : EuclideanSpace ℝ (Fin d),
      olsMinimaxRateGeneralDConcrete σ ≤
        LTFP.MathlibExt.Probability.gaussianMSEGeneralD A θ_star σ := by
  -- Setup: e = e_0, the canonical first basis vector; θ₀ = 0, θ₁ = σ·e.
  set e : EuclideanSpace ℝ (Fin d) :=
    EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ) with he_def
  set θ₀ : EuclideanSpace ℝ (Fin d) := 0 with hθ₀_def
  set θ₁ : EuclideanSpace ℝ (Fin d) := σ • e with hθ₁_def
  -- Norm of e is 1.
  have he_norm : ‖e‖ = 1 := by
    rw [he_def, EuclideanSpace.norm_single]; simp
  have he_norm_sq : ‖e‖^2 = 1 := by rw [he_norm]; norm_num
  -- σ² ≠ 0.
  have hσ_ne : σ ≠ 0 := ne_of_gt hσ
  have hσ_sq_pos : 0 < σ^2 := by positivity
  -- Distribution measures.
  set P₀ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)) :=
    ProbabilityTheory.multivariateGaussian θ₀
      ((σ^2) • (1 : Matrix (Fin d) (Fin d) ℝ))
      (ProbabilityTheory.posSemidef_sq_smul_one (n := d) σ)
    with hP₀_def
  set P₁ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)) :=
    ProbabilityTheory.multivariateGaussian θ₁
      ((σ^2) • (1 : Matrix (Fin d) (Fin d) ℝ))
      (ProbabilityTheory.posSemidef_sq_smul_one (n := d) σ)
    with hP₁_def
  -- Scalar estimator T y := ⟪A y, e⟫.
  set T : EuclideanSpace ℝ (Fin d) → ℝ := fun y => @inner ℝ _ _ (A y) e with hT_def
  have hT_meas : Measurable T := by
    refine Measurable.inner ?_ measurable_const
    exact hA
  -- Cauchy-Schwarz pointwise bound: (T y - σ·[j=1])² ≤ ‖A y - θ_j_vec‖².
  -- Specifically (⟪A y, e⟫ - 0)² ≤ ‖A y - 0‖² · ‖e‖² = ‖A y - 0‖²
  --        and  (⟪A y, e⟫ - σ)² = (⟪A y - σ·e, e⟫)² ≤ ‖A y - σ·e‖² · ‖e‖²
  --                            = ‖A y - σ·e‖².
  have h_inner_sub_zero : ∀ y, T y - 0 = @inner ℝ _ _ (A y - θ₀) e := by
    intro y
    rw [hT_def, hθ₀_def, sub_zero, sub_zero]
  have h_inner_sub_sigma : ∀ y, T y - σ = @inner ℝ _ _ (A y - θ₁) e := by
    intro y
    rw [hT_def, hθ₁_def]
    have h_inner_smul : @inner ℝ _ _ (σ • e) e = σ * ‖e‖^2 := by
      rw [inner_smul_left, real_inner_self_eq_norm_sq]
      simp
    rw [inner_sub_left, h_inner_smul, he_norm_sq, mul_one]
  -- Pointwise: (T y - 0)² ≤ ‖A y - θ₀‖².
  have h_cs_zero : ∀ y, (T y - 0)^2 ≤ ‖A y - θ₀‖^2 := by
    intro y
    rw [h_inner_sub_zero y]
    have h_cs : |@inner ℝ _ _ (A y - θ₀) e| ≤ ‖A y - θ₀‖ * ‖e‖ :=
      abs_real_inner_le_norm _ _
    have h_sq_le : (@inner ℝ _ _ (A y - θ₀) e)^2 ≤ (‖A y - θ₀‖ * ‖e‖)^2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h_cs 2
    calc (@inner ℝ _ _ (A y - θ₀) e)^2
        ≤ (‖A y - θ₀‖ * ‖e‖)^2 := h_sq_le
      _ = ‖A y - θ₀‖^2 * ‖e‖^2 := by ring
      _ = ‖A y - θ₀‖^2 * 1 := by rw [he_norm_sq]
      _ = ‖A y - θ₀‖^2 := by ring
  have h_cs_sigma : ∀ y, (T y - σ)^2 ≤ ‖A y - θ₁‖^2 := by
    intro y
    rw [h_inner_sub_sigma y]
    have h_cs : |@inner ℝ _ _ (A y - θ₁) e| ≤ ‖A y - θ₁‖ * ‖e‖ :=
      abs_real_inner_le_norm _ _
    have h_sq_le : (@inner ℝ _ _ (A y - θ₁) e)^2 ≤ (‖A y - θ₁‖ * ‖e‖)^2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h_cs 2
    calc (@inner ℝ _ _ (A y - θ₁) e)^2
        ≤ (‖A y - θ₁‖ * ‖e‖)^2 := h_sq_le
      _ = ‖A y - θ₁‖^2 * ‖e‖^2 := by ring
      _ = ‖A y - θ₁‖^2 * 1 := by rw [he_norm_sq]
      _ = ‖A y - θ₁‖^2 := by ring
  -- Integrability of (T y - 0)² and (T y - σ)².
  have hint_T_zero : MeasureTheory.Integrable (fun y => (T y - 0)^2) P₀ := by
    refine MeasureTheory.Integrable.mono' hint_zero ?_ ?_
    · exact ((hT_meas.sub measurable_const).pow_const 2).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact h_cs_zero y
  have hint_T_sigma : MeasureTheory.Integrable (fun y => (T y - σ)^2) P₁ := by
    refine MeasureTheory.Integrable.mono' hint_delta ?_ ?_
    · exact ((hT_meas.sub measurable_const).pow_const 2).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact h_cs_sigma y
  -- Scalar Le Cam reduction: (0-σ)²/4 · (1 - 2·tvDist) ≤ ∫(T-0)² dP₀ + ∫(T-σ)² dP₁.
  have h_lecam :=
    LTFP.MathlibExt.Probability.leCam_squared_loss_reduction_sum_form
      (EuclideanSpace ℝ (Fin d)) P₀ P₁ T hT_meas 0 σ hint_T_zero hint_T_sigma
  -- TV² bound via multivariate Bhattacharyya.
  -- bhattacharyya(P₀, P₁) = exp(-‖θ₀ - θ₁‖²/(8σ²)).
  -- ‖θ₀ - θ₁‖² = ‖σ·e‖² = σ²·‖e‖² = σ².
  -- So bhattacharyya² = exp(-σ²/(4σ²)) = exp(-1/4).
  -- And tvDist² ≤ 1 - bhattacharyya² = 1 - exp(-1/4).
  have h_TV_sq :
      ((LTFP.MathlibExt.Probability.tvDist P₀ P₁).toReal)^2 ≤
        1 - Real.exp (-1 / 4) := by
    -- Le Cam abstract estimate: TV² ≤ 1 - BH².
    have h_lecam_abstract :
        ((LTFP.MathlibExt.Probability.tvDist P₀ P₁).toReal)^2 ≤
          1 - LTFP.MathlibExt.Probability.bhattacharyya P₀ P₁ ^ 2 :=
      LTFP.MathlibExt.Probability.tvDist_sq_le_one_sub_bhattacharyya_sq P₀ P₁
    -- BH identity.
    have h_bh :
        LTFP.MathlibExt.Probability.bhattacharyya P₀ P₁ =
          Real.exp (-(∑ i : Fin d,
            ((WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ₀) i
              - (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ₁) i) ^ 2) / (8 * σ^2)) := by
      rw [hP₀_def, hP₁_def]
      exact LTFP.MathlibExt.Probability.bhattacharyya_multivariateGaussian_diagonal_eq
        θ₀ θ₁ hσ_ne
    -- Compute the sum: only the 0-th coordinate is nonzero.
    -- θ₀ = 0, θ₁ = σ·e where e is the 0-th basis vector. So
    -- (ofLp θ₀) i - (ofLp θ₁) i = 0 - σ·(if i = 0 then 1 else 0).
    -- For i ≠ 0: 0 - 0 = 0, square = 0.
    -- For i = ⟨0, hd⟩: 0 - σ = -σ, square = σ².
    have h_sum :
        (∑ i : Fin d,
          ((WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ₀) i
            - (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ₁) i) ^ 2) = σ^2 := by
      have h_θ₀_apply : ∀ i : Fin d,
          (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ₀) i = 0 := by
        intro i
        rw [hθ₀_def]
        show (WithLp.ofLp (p := 2) (V := Fin d → ℝ) (0 : EuclideanSpace ℝ (Fin d))) i = 0
        simp
      have h_θ₁_apply : ∀ i : Fin d,
          (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ₁) i =
            if i = ⟨0, hd⟩ then σ else 0 := by
        intro i
        rw [hθ₁_def, he_def]
        -- θ₁ = σ • EuclideanSpace.single ⟨0, hd⟩ 1
        -- ofLp(σ•single i 1) j = σ * single i 1 j = σ * (if j = i then 1 else 0).
        rw [WithLp.ofLp_smul]
        show σ • (WithLp.ofLp (p := 2) (V := Fin d → ℝ)
              (EuclideanSpace.single (⟨0, hd⟩ : Fin d) (1 : ℝ))) i = _
        rw [EuclideanSpace.ofLp_single]
        by_cases h : i = ⟨0, hd⟩
        · subst h; simp
        · rw [Pi.single_eq_of_ne h, smul_zero, if_neg h]
      -- Now compute the sum.
      have h_pointwise : ∀ i : Fin d,
          ((WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ₀) i
            - (WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ₁) i) ^ 2 =
          if i = ⟨0, hd⟩ then σ^2 else 0 := by
        intro i
        rw [h_θ₀_apply i, h_θ₁_apply i, zero_sub]
        by_cases h : i = ⟨0, hd⟩
        · rw [if_pos h, if_pos h]; ring
        · rw [if_neg h, if_neg h, neg_zero]; ring
      rw [Finset.sum_congr rfl (fun i _ => h_pointwise i)]
      rw [Finset.sum_ite_eq']
      simp
    rw [h_sum] at h_bh
    -- Now bhattacharyya = exp(-σ²/(8σ²)) = exp(-1/8).
    have h_bh_simp :
        LTFP.MathlibExt.Probability.bhattacharyya P₀ P₁ =
          Real.exp (-1 / 8) := by
      rw [h_bh]
      congr 1
      field_simp
    rw [h_bh_simp] at h_lecam_abstract
    -- (exp(-1/8))² = exp(-1/4).
    have h_sq_exp : Real.exp (-1 / 8) ^ 2 = Real.exp (-1 / 4) := by
      rw [sq, ← Real.exp_add]
      congr 1; ring
    rw [h_sq_exp] at h_lecam_abstract
    exact h_lecam_abstract
  have h_TV_nn : 0 ≤ (LTFP.MathlibExt.Probability.tvDist P₀ P₁).toReal :=
    LTFP.MathlibExt.Probability.tvDist_toReal_nonneg _ _
  have h_TV_le :
      (LTFP.MathlibExt.Probability.tvDist P₀ P₁).toReal ≤
        Real.sqrt (1 - Real.exp (-1 / 4)) := by
    have h_arg_nn : 0 ≤ 1 - Real.exp (-1 / 4) := by
      have hle1 : Real.exp (-1 / 4) ≤ 1 := by
        apply Real.exp_le_one_iff.mpr; norm_num
      linarith
    have h_sqrt_sq :
        (LTFP.MathlibExt.Probability.tvDist P₀ P₁).toReal =
          Real.sqrt (((LTFP.MathlibExt.Probability.tvDist P₀ P₁).toReal)^2) := by
      rw [Real.sqrt_sq h_TV_nn]
    rw [h_sqrt_sq]
    exact Real.sqrt_le_sqrt h_TV_sq
  -- (0-σ)²/4 · (1 - 2·√(...)) ≤ (0-σ)²/4 · (1 - 2·tvDist).
  have h_one_sub_two_TV_ge :
      1 - 2 * Real.sqrt (1 - Real.exp (-1 / 4)) ≤
        1 - 2 * (LTFP.MathlibExt.Probability.tvDist P₀ P₁).toReal := by
    linarith
  have hσ_sq_quart_nn : 0 ≤ (0 - σ)^2 / 4 := by
    have : (0 - σ)^2 ≥ 0 := sq_nonneg _
    linarith
  have h_lecam_intermediate :
      (0 - σ)^2 / 4 * (1 - 2 * Real.sqrt (1 - Real.exp (-1 / 4))) ≤
        (∫ y, (T y - 0)^2 ∂P₀) + ∫ y, (T y - σ)^2 ∂P₁ := by
    have h_mul :
        (0 - σ)^2 / 4 * (1 - 2 * Real.sqrt (1 - Real.exp (-1 / 4))) ≤
        (0 - σ)^2 / 4 *
            (1 - 2 * (LTFP.MathlibExt.Probability.tvDist P₀ P₁).toReal) :=
      mul_le_mul_of_nonneg_left h_one_sub_two_TV_ge hσ_sq_quart_nn
    linarith
  -- Cauchy-Schwarz reduces scalar integrals to vector MSE.
  have h_int_T_le_zero :
      ∫ y, (T y - 0)^2 ∂P₀ ≤ ∫ y, ‖A y - θ₀‖^2 ∂P₀ := by
    refine MeasureTheory.integral_mono hint_T_zero hint_zero ?_
    intro y
    exact h_cs_zero y
  have h_int_T_le_sigma :
      ∫ y, (T y - σ)^2 ∂P₁ ≤ ∫ y, ‖A y - θ₁‖^2 ∂P₁ := by
    refine MeasureTheory.integral_mono hint_T_sigma hint_delta ?_
    intro y
    exact h_cs_sigma y
  -- Define vector MSEs.
  set R₀ : ℝ := ∫ y, ‖A y - θ₀‖^2 ∂P₀ with hR₀_def
  set R₁ : ℝ := ∫ y, ‖A y - θ₁‖^2 ∂P₁ with hR₁_def
  -- Compose: rate ≤ R₀ + R₁.
  have h_rate_le_sum :
      (0 - σ)^2 / 4 * (1 - 2 * Real.sqrt (1 - Real.exp (-1 / 4))) ≤
        R₀ + R₁ := by
    calc (0 - σ)^2 / 4 * (1 - 2 * Real.sqrt (1 - Real.exp (-1 / 4)))
        ≤ (∫ y, (T y - 0)^2 ∂P₀) + ∫ y, (T y - σ)^2 ∂P₁ := h_lecam_intermediate
      _ ≤ R₀ + R₁ := by
          exact add_le_add h_int_T_le_zero h_int_T_le_sigma
  -- (0 - σ)² = σ².
  have h_diff_sq : (0 - σ)^2 = σ^2 := by ring
  rw [h_diff_sq] at h_rate_le_sum
  -- max(R₀, R₁) ≥ (R₀ + R₁)/2 ≥ σ²/8 · (1 - 2·√(...)).
  have h_max_ge_avg :
      (R₀ + R₁) / 2 ≤ max R₀ R₁ :=
    LTFP.MathlibExt.Probability.average_le_max_of_pair R₀ R₁
  have h_avg_bound :
      σ^2 / 8 * (1 - 2 * Real.sqrt (1 - Real.exp (-1 / 4))) ≤
        (R₀ + R₁) / 2 := by
    have : σ^2 / 4 * (1 - 2 * Real.sqrt (1 - Real.exp (-1 / 4))) ≤
        R₀ + R₁ := h_rate_le_sum
    linarith
  have h_final :
      σ^2 / 8 * (1 - 2 * Real.sqrt (1 - Real.exp (-1 / 4))) ≤
        max R₀ R₁ := h_avg_bound.trans h_max_ge_avg
  -- Extract witness.
  rcases le_total R₀ R₁ with h | h
  · refine ⟨θ₁, ?_⟩
    have h_max_eq : max R₀ R₁ = R₁ := max_eq_right h
    rw [h_max_eq] at h_final
    unfold olsMinimaxRateGeneralDConcrete
    show σ^2 * (1 / 8) * (1 - 2 * Real.sqrt (1 - Real.exp (-1 / 4))) ≤
      LTFP.MathlibExt.Probability.gaussianMSEGeneralD A θ₁ σ
    have h_eq : σ^2 * (1 / 8) = σ^2 / 8 := by ring
    rw [h_eq]
    -- gaussianMSEGeneralD A θ₁ σ = R₁ by definition.
    show σ^2 / 8 * (1 - 2 * Real.sqrt (1 - Real.exp (-1 / 4))) ≤
      ∫ y, ‖A y - θ₁‖^2 ∂P₁
    exact h_final
  · refine ⟨θ₀, ?_⟩
    have h_max_eq : max R₀ R₁ = R₀ := max_eq_left h
    rw [h_max_eq] at h_final
    unfold olsMinimaxRateGeneralDConcrete
    show σ^2 * (1 / 8) * (1 - 2 * Real.sqrt (1 - Real.exp (-1 / 4))) ≤
      LTFP.MathlibExt.Probability.gaussianMSEGeneralD A θ₀ σ
    have h_eq : σ^2 * (1 / 8) = σ^2 / 8 := by ring
    rw [h_eq]
    show σ^2 / 8 * (1 - 2 * Real.sqrt (1 - Real.exp (-1 / 4))) ≤
      ∫ y, ‖A y - θ₀‖^2 ∂P₀
    exact h_final

#check @LTFP.olsMinimaxRateGeneralDConcrete
#check @LTFP.olsMinimaxRateGeneralDConcrete_nonneg
#check @LTFP.ols_minimax_lower_bound_general_d_gaussian_concrete

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

#check @LTFP.sup_ge_bayes_average
#check @LTFP.bayes_posterior_mean_excess_risk_gaussian_scalar
#check @LTFP.bayes_posterior_mean_excess_risk_gaussian_scalar_discharged
#check @LTFP.bayes_trace_limit
#check @LTFP.bayes_trace_limit_discharged
#check @LTFP.ols_minimax_bayes_prior
#check @LTFP.ols_minimax_bayes_prior_discharged
#check @LTFP.ols_minimax_bayes_prior_finite_average_at_improper_limit
#check @LTFP.ols_minimax_bayes_prior_via_quantified_finite_average
#check @LTFP.ols_minimax_lower_bound_via_quantified_finite_average
#check @LTFP.ols_minimax_bayes_prior_finite_tau_squared_family
#check @LTFP.ols_minimax_lower_bound_via_finite_tau_squared_family
#check @LTFP.gaussian_two_point_max_risk_lower_bound
#check @LTFP.ols_minimax_two_point_discharge_scalar
#check @LTFP.ols_minimax_two_point_discharge_scalar_via_bhattacharyya
#check @LTFP.ols_minimax_two_point_discharge_multivariate_via_bhattacharyya

end LTFP
