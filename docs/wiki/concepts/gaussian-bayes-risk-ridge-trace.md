# Bach §3.7 Node 3: Bayes risk = σ²/n · tr((Σ̂+λI)⁻¹ Σ̂)

**ID:** `gaussian-bayes-risk-ridge-trace`  
**Chapter:** Ch03 (Bach §3.7, p. 61)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** in_progress  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Gaussian`, `Ridge`, `Bayes-risk`, `Matrix/LinAlg`

## Statement

Node 3 of the B4 decomposition. Closed-form Bayes excess risk for ridge under a Gaussian prior: `E_{θ,ε}[‖X β̂_ridge − Xθ‖²/n] = σ²/n · tr((Σ̂+λI)⁻¹ Σ̂)`. Scalar (`Σ̂ = I`) case landed as `gaussianBayesRiskScalar_eq` giving `σ²·d/(n(1+λ))`. General-Σ̂ lift via spectral diagonalisation + trace-cyclic remains open (M-scale, ~1-2 days; uses `Matrix.IsHermitian.spectralTheorem` + `ridge_excess_risk`). Independent of Node 2 — pure linear algebra reduction.


## Bach's textbook treatment

_No book excerpt available._ See [`tasks/gaussian-bayes-risk-ridge-trace/`](../../../tasks/gaussian-bayes-risk-ridge-trace/) if a context kit has been built, or generate one with `python -m tools.context_kit`.

## Prerequisites (Bach's dependency graph)

- [`gaussian-conjugate-posterior-mean`](./gaussian-conjugate-posterior-mean.md) — Bach §3.7 Node 2: Gaussian conjugate-prior posterior mean = ridge
- [`ridge-bias-variance`](./ridge-bias-variance.md) — Ridge bias-variance trade-off (fixed design)

## Dependents (concepts that use this)

- [`ols-minimax-lower-bound`](./ols-minimax-lower-bound.md) — Minimax lower bound for least-squares (♦) — umbrella

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch03_LinearLeastSquares/MultivariateGaussian.lean`
- **Theorem/def name:** `gaussianBayesRiskScalar_eq`
- **Status:** in_progress
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- **No verified book excerpt** — verify before citing this concept by a textbook equation number; equation labels in synthesized notes can drift relative to the canonical Bach (2024) PDF.

