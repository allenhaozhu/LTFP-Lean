# KRR coefficients homogeneous in labels

**ID:** `krr-coeffs-smul-y`  
**Chapter:** Ch07 (Bach §7.4)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** `RKHS`

## Statement

_See textbook excerpt below or [`tasks/krr-coeffs-smul-y/`](../../../tasks/krr-coeffs-smul-y/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — KRR coefficients homogeneous in labels

**Concept ID:** `krr-coeffs-smul-y`
**Chapter:** Ch 7
**Section:** §7.4.1 / §7.6.1 (derived corollary)
**Pages:** 196 (book) / PDF p. 212
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For fixed Gram matrix $K$ and regularization $\lambda > 0$, the KRR coefficient map $y \mapsto \hat\alpha_\lambda(y) = (K + n\lambda I)^{-1} y$ is homogeneous: for any scalar $c \in \mathbb{R}$,

$$\hat\alpha_\lambda(c \cdot y) = c \cdot \hat\alpha_\lambda(y).$$

## Proof (verbatim)

Not stated as a numbered lemma; immediate from $\hat\alpha_\lambda = (K + n\lambda I)^{-1} y$ together with the homogeneity of matrix-vector multiplication: $(K + n\lambda I)^{-1}(c y) = c (K + n\lambda I)^{-1} y$. (Sketch.)

Bach's §7.6.1 ("Kernel Ridge Regression as a Linear Estimator," p. 196) makes the linearity statement explicit.

## Notes

- Lean form `krrCoeffs_smul_y` in `LTFP/Ch07_Kernels/Algorithms.lean`.
- Trivial corollary of the closed-form (7.7); paired with `krr-coeffs-add-y` to give linearity.
- Used in the bias-variance decomposition of §7.6.2 (KRR is a linear estimator, so its bias and variance decompose into deterministic + label-noise components).

## Prerequisites (Bach's dependency graph)

- [`krr-coeffs`](./krr-coeffs.md) — Kernel ridge regression coefficient α̂_λ = (K + nλI)⁻¹ y

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch07_Kernels/Algorithms.lean`
- **Theorem/def name:** `krrCoeffs_smul_y`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

