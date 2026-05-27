# Gram matrix diagonal: K i i = k(xᵢ, xᵢ)

**ID:** `gram-matrix-diag`  
**Chapter:** Ch07 (Bach §7.4)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Matrix/LinAlg`

## Statement

_See textbook excerpt below or [`tasks/gram-matrix-diag/`](../../../tasks/gram-matrix-diag/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Gram matrix diagonal: K i i = k(xᵢ, xᵢ)

**Concept ID:** `gram-matrix-diag`
**Chapter:** Ch 7
**Section:** §7.4 (boundedness assumption uses it)
**Pages:** 182, 196 (book) / PDF pp. 198, 212
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For any $i \in \{1, \dots, n\}$, the diagonal entry of the Gram matrix is the self-kernel at the $i$-th data point:

$$K_{ii} = k(x_i, x_i) = \|\phi(x_i)\|_\mathcal{H}^2.$$

## Proof (verbatim)

Bach uses this in §7.4 when stating the boundedness assumption (p. 196):

"*We assume that features are bounded; that is, for all $i \in \{1, \dots, n\}$, $k(x_i, x_i) = \|\phi(x_i)\|_\mathcal{H}^2 \le R^2$.*"

The identity $K_{ii} = k(x_i, x_i)$ is the diagonal case of the defining equation $K_{ij} = k(x_i, x_j)$ (p. 182). (Sketch.)

## Notes

- Lean form `gramMatrix_diag` in `LTFP/Ch07_Kernels/Algorithms.lean`.
- Direct corollary of `gram-matrix-eq-kernel`.
- Crucial role: linking the boundedness assumption $\|\phi(x_i)\|^2 \le R^2$ (used in §7.5 Lipschitz analyses) to the matrix-level statement $\mathrm{tr}(K)/n \le R^2$.

## Prerequisites (Bach's dependency graph)

- [`gram-matrix`](./gram-matrix.md) — Gram matrix Kᵢⱼ = k(xᵢ, xⱼ)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch07_Kernels/Algorithms.lean`
- **Theorem/def name:** `gramMatrix_diag`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

