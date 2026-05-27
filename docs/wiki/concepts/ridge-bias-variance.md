# Ridge bias-variance trade-off (fixed design)

**ID:** `ridge-bias-variance`  
**Chapter:** Ch03 (Bach §3.6, p. 58)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Ridge`

## Statement

_See textbook excerpt below or [`tasks/ridge-bias-variance/`](../../../tasks/ridge-bias-variance/) if available._

## Bach's textbook treatment

# Book excerpt — `ridge-bias-variance` (Bach 2024 §3.6, p. 58)

> The ridge estimator `θ̂_λ = (ΦᵀΦ + n λ I)⁻¹ Φᵀ y` is a *linear*
> estimator: the map `y ↦ θ̂_λ` is linear in `y`. Under the linear
> model `y = Φ θ_* + ε` with zero-mean noise, this linearity is what
> drives the bias-variance decomposition:
>
>     E[θ̂_λ] = (ΦᵀΦ + n λ I)⁻¹ ΦᵀΦ θ_*    (bias term factor)
>     E[(θ̂_λ − E[θ̂_λ])²] is determined by the noise covariance.
>
> The bias term `E[θ̂_λ] − θ_*` shrinks `θ_*` away from itself by the
> ridge regularization, which is what trades variance reduction for
> bias.

## Lean target — pure-algebra core identity

The probability layer is heavy. **Target the deterministic linearity
identity** that drives the bias-variance proof — it needs no
expectation operator and no probability space:

    theorem ridge_excess_risk {n d : ℕ}
        (X : Matrix (Fin n) (Fin d) ℝ) (y₁ y₂ : Fin n → ℝ) (lam : ℝ) :
        ridgeEstimator X (y₁ + y₂) lam =
          ridgeEstimator X y₁ lam + ridgeEstimator X y₂ lam

Proof sketch (one-liner): unfold `ridgeEstimator`, then apply
`Matrix.mulVec_add` (the matrix `(XᵀX + nλI)⁻¹ * Xᵀ` is fixed, so
applying it to `y₁ + y₂` distributes).

## Acceptable smaller fallback

If the linearity statement above gets stuck, fall back to homogeneity
in `y` (scaling):

    theorem ridge_excess_risk {n d : ℕ}
        (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ) (lam c : ℝ) :
        ridgeEstimator X (c • y) lam = c • ridgeEstimator X y lam

via `Matrix.mulVec_smul`.

Or even smaller — the ridge of zero is zero:

    theorem ridge_excess_risk {n d : ℕ}
        (X : Matrix (Fin n) (Fin d) ℝ) (lam : ℝ) :
        ridgeEstimator X (0 : Fin n → ℝ) lam = 0

via `Matrix.mulVec_zero`.

**No `sorry`, no `admit`, no `True`** — pick whichever lands cleanly.
The `ridgeEstimator` definition is in the same file; you can reference
it directly.

Useful Mathlib lemmas: `Matrix.mulVec_add`, `Matrix.mulVec_smul`,
`Matrix.mulVec_zero`.

## Prerequisites (Bach's dependency graph)

- [`ols-fixed-design-bias-variance`](./ols-fixed-design-bias-variance.md) — Fixed-design OLS bias-variance decomposition
- [`ridge-closed-form`](./ridge-closed-form.md) — Ridge closed form: β̂_λ = (XᵀX + nλI)⁻¹Xᵀy

## Dependents (concepts that use this)

- [`gaussian-bayes-risk-ridge-trace`](./gaussian-bayes-risk-ridge-trace.md) — Bach §3.7 Node 3: Bayes risk = σ²/n · tr((Σ̂+λI)⁻¹ Σ̂)
- [`gaussian-conjugate-posterior-mean`](./gaussian-conjugate-posterior-mean.md) — Bach §3.7 Node 2: Gaussian conjugate-prior posterior mean = ridge
- [`matrix-trace-regularized-inv-limit`](./matrix-trace-regularized-inv-limit.md) — Bach §3.7 Node 4: tr((Σ̂+λI)⁻¹ Σ̂) → d as λ → 0 (full-rank Σ̂)
- [`ols-minimax-sup-ge-bayes`](./ols-minimax-sup-ge-bayes.md) — Bach §3.7 Node 1: sup-over-θ ≥ Bayes-average (finite-grid pigeonhole)

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch03_LinearLeastSquares/Ridge.lean`
- **Theorem/def name:** `ridge_excess_risk`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

