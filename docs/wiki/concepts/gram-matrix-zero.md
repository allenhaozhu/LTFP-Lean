# Gram matrix of zero kernel = 0

**ID:** `gram-matrix-zero`  
**Chapter:** Ch07 (Bach §7.4)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Kernel`, `Matrix/LinAlg`

## Statement

_See textbook excerpt below or [`tasks/gram-matrix-zero/`](../../../tasks/gram-matrix-zero/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Gram matrix of zero kernel = 0

**Concept ID:** `gram-matrix-zero`
**Chapter:** Ch 7
**Section:** §7.4 (derived sanity check)
**Pages:** 182, 196 (book) / PDF pp. 198, 212
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

If $k \equiv 0$ (the zero kernel: $k(x, y) = 0$ for all $x, y$), then the corresponding Gram matrix is the zero matrix: $K = 0 \in \mathbb{R}^{n \times n}$.

## Proof (verbatim)

Not stated by Bach; trivial corollary of $K_{ij} = k(x_i, x_j)$ (p. 182). Since each entry vanishes, the matrix is zero. (Sketch.)

## Notes

- Lean form `gramMatrix_zero` in `LTFP/Ch07_Kernels/Algorithms.lean`.
- Edge-case / sanity-check lemma. Used to derive `krr-predictor-zero-kernel`.
- The zero kernel is positive-definite ($\alpha^\top 0 \alpha = 0 \ge 0$) but degenerate — its RKHS contains only the zero function.

## Prerequisites (Bach's dependency graph)

- [`gram-matrix`](./gram-matrix.md) — Gram matrix Kᵢⱼ = k(xᵢ, xⱼ)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch07_Kernels/Algorithms.lean`
- **Theorem/def name:** `gramMatrix_zero`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

