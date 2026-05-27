# KRR coefficients with zero labels = 0

**ID:** `krr-coeffs-zero-y`  
**Chapter:** Ch07 (Bach §7.4)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** `RKHS`

## Statement

_See textbook excerpt below or [`tasks/krr-coeffs-zero-y/`](../../../tasks/krr-coeffs-zero-y/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — KRR coefficients with zero labels = 0

**Concept ID:** `krr-coeffs-zero-y`
**Chapter:** Ch 7
**Section:** §7.4.1 (derived corollary)
**Pages:** 196 (book) / PDF p. 212
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

When the label vector is zero ($y = 0 \in \mathbb{R}^n$), the KRR coefficient vector is zero:

$$\hat\alpha_\lambda(0) = (K + n\lambda I)^{-1} \cdot 0 = 0.$$

## Proof (verbatim)

Not stated as a numbered lemma; trivial from $\hat\alpha_\lambda = (K + n\lambda I)^{-1} y$ (equation (7.7), p. 196) and the fact that any linear map sends $0$ to $0$. (Sketch.)

## Notes

- Lean form `krrCoeffs_zero_y` in `LTFP/Ch07_Kernels/Algorithms.lean`.
- Edge-case lemma; together with `krr-coeffs-add-y` and `krr-coeffs-smul-y`, fully characterizes $\hat\alpha_\lambda$ as a linear map $\mathbb{R}^n \to \mathbb{R}^n$.
- Sanity check that the KRR predictor with no signal returns the zero function.

## Prerequisites (Bach's dependency graph)

- [`krr-coeffs`](./krr-coeffs.md) — Kernel ridge regression coefficient α̂_λ = (K + nλI)⁻¹ y

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch07_Kernels/Algorithms.lean`
- **Theorem/def name:** `krrCoeffs_zero_labels`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

