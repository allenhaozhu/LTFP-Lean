# Gram matrix entry equals kernel evaluation

**ID:** `gram-matrix-eq-kernel`  
**Chapter:** Ch07 (Bach §7.4)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Kernel`, `Neural-network`, `Matrix/LinAlg`

## Statement

_See textbook excerpt below or [`tasks/gram-matrix-eq-kernel/`](../../../tasks/gram-matrix-eq-kernel/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Gram matrix entry equals kernel evaluation

**Concept ID:** `gram-matrix-eq-kernel`
**Chapter:** Ch 7
**Section:** §7.2 / §7.4 (definitional)
**Pages:** 182, 196 (book) / PDF pp. 198, 212
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Definitional rewrite for the Gram matrix: for all $i, j \in \{1, \dots, n\}$,

$$K_{ij} = k(x_i, x_j).$$

## Proof (verbatim)

This is Bach's defining identity for the Gram matrix (p. 182):

"*where $K \in \mathbb{R}^{n\times n}$ is the kernel matrix (Gram matrix of the feature vectors), such that* $K_{ij} = \langle\phi(x_i), \phi(x_j)\rangle = k(x_i, x_j).$"

(By definition.)

## Notes

- Lean form `gramMatrix_eq_kernel` (the `simp` form of the definition) in `LTFP/Ch07_Kernels/Algorithms.lean`.
- "Sanity-check" definitional lemma; useful for unfolding `gramMatrix` in proofs.
- Used to derive `gram-matrix-diag`, `gram-matrix-symm`, `gram-matrix-zero`.

## Prerequisites (Bach's dependency graph)

- [`gram-matrix`](./gram-matrix.md) — Gram matrix Kᵢⱼ = k(xᵢ, xⱼ)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch07_Kernels/Algorithms.lean`
- **Theorem/def name:** `gramMatrix_eq_kernel`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

