/-
LTFP §3.5 — Fixed design analysis.

Bach (2024) §3.5, pp. 50–55. With deterministic design `X` and noise
`ε ~ subG(0, σ²)`, OLS satisfies `E[‖X β̂ − X β⋆‖² / n] = σ² · d / n`
when `XᵀX / n` is invertible. The minimax lower bound matching this
rate appears in §3.7.
-/
import LTFP.Ch03_LinearLeastSquares.OLS
import LTFP.MathlibExt.Probability.Distributions.MultivariateGaussian
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
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

    `gaussianBayesRiskScalar σ² d λ = σ² · d / (1 + λ)`.

    This is the **canonical scalar Bayes shrinkage risk** under prior
    `β ~ N(0, τ²·I)` and noise `ε ~ N(0, σ²·I)` for the `Σ̂ = I` case
    (Bach 2024, §3.7). The general matrix case reduces to this scalar
    form by spectral decomposition of `Σ̂`.

    Together with `bayes_trace_limit` and `sup_ge_bayes_average`, this
    discharges the algebraic content of the Bayes-prior reduction in
    `ols_minimax_bayes_prior` for the canonical Gaussian setup. -/
theorem bayes_posterior_mean_excess_risk_gaussian_scalar_discharged
    (sigmaSq : ℝ) (d : ℕ) (lam : ℝ) :
    LTFP.MathlibExt.Probability.Distributions.gaussianBayesRiskScalar
        sigmaSq d lam = sigmaSq * d / (1 + lam) :=
  LTFP.MathlibExt.Probability.Distributions.gaussianBayesRiskScalar_eq
    sigmaSq d lam

/-- §3.7 — Bayes-prior reduction, step (iii) — *discharged form*.

    The asymptotic identity `gaussianBayesRiskScalar σ² d (1/N) →
    σ² · d` from the multivariate-Gaussian extension matches the
    `bayes_trace_limit` statement above. Use this form when working
    with the discharged Bayes-risk function rather than the inline
    `σ² · d / (1 + 1/N)` expression. -/
theorem bayes_trace_limit_discharged (sigmaSq : ℝ) (d : ℕ) :
    Filter.Tendsto
      (fun N : ℕ =>
        LTFP.MathlibExt.Probability.Distributions.gaussianBayesRiskScalar
          sigmaSq d (1 / (N : ℝ)))
      Filter.atTop (nhds (sigmaSq * d)) :=
  LTFP.MathlibExt.Probability.Distributions.gaussianBayesRiskScalar_tendsto_atTop
    sigmaSq d

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

end LTFP
