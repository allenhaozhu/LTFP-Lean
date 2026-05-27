# Minimax lower bound for least-squares (♦) — umbrella

**ID:** `ols-minimax-lower-bound`  
**Chapter:** Ch03 (Bach §3.7, p. 60)  
**Kind:** theorem  
**Difficulty:** diamond  
**Tier (inferred):** L2  
**Status:** B  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Gaussian`, `OLS`, `Ridge`, `Bayes-risk`, `Lower-bound`, `Matrix/LinAlg`

## Statement

Umbrella for the 5-node Bach §3.7 minimax-lower-bound decomposition (docs/wiki/B4_DECOMPOSITION_PLAN.md). The five logical steps: (S1) sup ≥ Bayes-average [`ols-minimax-sup-ge-bayes`, DONE], (S2) Bayes estimator = posterior mean = ridge [`gaussian-conjugate-posterior-mean`, PENDING — the actual residual], (S3) Bayes risk = `σ²/n · tr((Σ̂+λI)⁻¹ Σ̂)` [`gaussian-bayes-risk-ridge-trace`, IN_PROGRESS — scalar done], (S4) take λ → 0 [`matrix-trace-regularized-inv-limit`, DONE], (S5) compose. Carriers `ols_minimax_lower_bound_via_quantified_finite_average` (exact) and `ols_minimax_lower_bound_via_finite_tau_squared_family` (ε-relaxed) are wired but hypothesis-parametric on Node 2. Promoted from placeholder anchor (`ols_minimax_lb`) to a real Lean 4 statement of the Mourtada (2022) rate `mourtada_lower_bound d n σ² := σ² · d / n`. Critical-path estimate: 1–3 weeks dominated by Node 2.


## Bach's textbook treatment

# Book excerpt — `ols-minimax-lower-bound` (Bach 2024 §3.7, pp. 60-62)

> **Lower Bound (♦).** Goal: lower-bound the minimax excess risk
>
>     inf_{A} sup_{θ_* ∈ ℝᵈ} E_{ε ∼ N(0, σ² I)}[R_{θ_*}(A(Φ θ_* + ε))] − R*
>     ≥ σ² d / n.
>
> *Proof sketch (♦, fixed-design Gaussian, after Mourtada 2022).*
> Bound the supremum by an expectation under a Gaussian prior
> `θ_* ∼ N(0, (σ²/(λn)) I)` and use that for Gaussian conditioning the
> posterior mean equals the posterior mode, which is exactly ridge
> regression. Computing the optimal risk under that ridge form,
>
>     ≥ σ²/n · tr((Σ̂ + λ I)⁻¹ Σ̂),
>
> and as `λ → 0`, when `Σ̂` has full rank, `(Σ̂ + λ I)⁻¹ Σ̂ → I`, so
> the bound tends to `σ²/n · tr(I) = σ² d / n`.

## Lean target — pure-algebra core identity

The full Bayesian-prior argument is heavy. **Target the elementary
trace identity** at the very end of the proof: `tr(I_d) = d`.

    theorem ols_minimax_lb (d : ℕ) :
        ((1 : Matrix (Fin d) (Fin d) ℝ).trace) = d

This is `Matrix.trace_one` in Mathlib (or a one-liner via
`Finset.sum_const_one`).

## Acceptable smaller fallback

If `Matrix.trace_one` fights typeclasses, fall back to one of:

- `Finset.sum_const_one`: `∑ _ ∈ Finset.univ : Finset (Fin d), (1 : ℝ) = d`
  via `Finset.sum_const`.
- `0 ≤ d` (positivity of the dimension): `(d : ℝ) ≥ 0` via `Nat.cast_nonneg`.
- `(σ : ℝ)^2 * d ≥ 0` for `d : ℕ` (nonnegativity of the lower bound):
  via `mul_nonneg (sq_nonneg σ) (Nat.cast_nonneg d)`.

**No `sorry`, no `admit`, no `True`** — pick whichever lands cleanest.
The point of the ticket is to land *something real* in the
minimax-lower-bound neighbourhood; the full Mourtada-style Bayesian
analysis is a multi-month project deferred indefinitely.

## Prerequisites (Bach's dependency graph)

- [`gaussian-bayes-risk-ridge-trace`](./gaussian-bayes-risk-ridge-trace.md) — Bach §3.7 Node 3: Bayes risk = σ²/n · tr((Σ̂+λI)⁻¹ Σ̂)
- [`gaussian-conjugate-posterior-mean`](./gaussian-conjugate-posterior-mean.md) — Bach §3.7 Node 2: Gaussian conjugate-prior posterior mean = ridge
- [`matrix-trace-regularized-inv-limit`](./matrix-trace-regularized-inv-limit.md) — Bach §3.7 Node 4: tr((Σ̂+λI)⁻¹ Σ̂) → d as λ → 0 (full-rank Σ̂)
- [`ols-minimax-sup-ge-bayes`](./ols-minimax-sup-ge-bayes.md) — Bach §3.7 Node 1: sup-over-θ ≥ Bayes-average (finite-grid pigeonhole)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch03_LinearLeastSquares/FixedDesign.lean`
- **Theorem/def name:** `mourtada_lower_bound`
- **Status:** B
- **Primary closing commit:** `66e37dd` (theorem `ols_minimax_lower_bound_for_all_estimators`)
- **Audit class:** **B**
- **Audit notes:** Le Cam two-point + Bayes-trace step are HYPOTHESES

## Audit history (if any)

- commit `66e37dd` — theorem `ols_minimax_lower_bound_for_all_estimators` — classified **B** in PROGRESS.md §10 (Le Cam two-point + Bayes-trace step are HYPOTHESES)
- commit `8be0ac1` — theorem `ols_minimax_bayes_prior` — classified **B** in PROGRESS.md §10 (Gaussian-posterior-mean identity `bayes_posterior_mean_excess_risk_gaussian` is passed PARAMETRIC (scalar case proved, general d-dim case is the Mathlib conjugate-prior gap))

## Notes / open questions

- Carrier is **parametric** — at least one substantive hypothesis is passed through, not discharged.

