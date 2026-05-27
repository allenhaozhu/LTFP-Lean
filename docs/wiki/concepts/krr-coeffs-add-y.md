# KRR coefficients linear in labels

**ID:** `krr-coeffs-add-y`  
**Chapter:** Ch07 (Bach §7.4)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** `RKHS`

## Statement

_See textbook excerpt below or [`tasks/krr-coeffs-add-y/`](../../../tasks/krr-coeffs-add-y/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — KRR coefficients linear in labels

**Concept ID:** `krr-coeffs-add-y`
**Chapter:** Ch 7
**Section:** §7.4.1 (derived corollary of closed form)
**Pages:** 196 (book) / PDF p. 212
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For fixed Gram matrix $K$ and regularization $\lambda > 0$, the KRR coefficient map $y \mapsto \hat\alpha_\lambda(y) = (K + n\lambda I)^{-1} y$ is additive in $y$: for all $y_1, y_2 \in \mathbb{R}^n$,

$$\hat\alpha_\lambda(y_1 + y_2) = \hat\alpha_\lambda(y_1) + \hat\alpha_\lambda(y_2).$$

## Proof (verbatim)

Bach does not state this as a numbered theorem; it is **immediate** from the closed-form $\hat\alpha_\lambda = (K + n\lambda I)^{-1} y$ (equation (7.7), p. 196), since matrix-vector multiplication is linear:

$(K + n\lambda I)^{-1}(y_1 + y_2) = (K + n\lambda I)^{-1} y_1 + (K + n\lambda I)^{-1} y_2.$ (Sketch.)

Bach references the underlying "KRR is a linear estimator" structure explicitly in §7.6.1 ("Kernel Ridge Regression as a Linear Estimator," p. 196 onward).

## Notes

- Lean form `krrCoeffs_add_y` in `LTFP/Ch07_Kernels/Algorithms.lean`.
- Together with `krr-coeffs-smul-y` and `krr-coeffs-zero-y`, establishes that KRR is a *linear* estimator in the labels (the basis for §7.6's bias-variance decomposition).
- Proof technique: linearity of matrix-vector multiplication.

## Prerequisites (Bach's dependency graph)

- [`krr-coeffs`](./krr-coeffs.md) — Kernel ridge regression coefficient α̂_λ = (K + nλI)⁻¹ y

## Dependents (concepts that use this)

- [`krr-predictor-add-y`](./krr-predictor-add-y.md) — KRR predictor linear in labels (composition)

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch07_Kernels/Algorithms.lean`
- **Theorem/def name:** `krrCoeffs_add_y`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

