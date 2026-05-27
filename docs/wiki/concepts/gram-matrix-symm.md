# Gram matrix is symmetric for symmetric kernel

**ID:** `gram-matrix-symm`  
**Chapter:** Ch07 (Bach §7.4)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Kernel`, `Matrix/LinAlg`

## Statement

_See textbook excerpt below or [`tasks/gram-matrix-symm/`](../../../tasks/gram-matrix-symm/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Gram matrix is symmetric for symmetric kernel

**Concept ID:** `gram-matrix-symm`
**Chapter:** Ch 7
**Section:** §7.2 / §7.3 (implicit)
**Pages:** 182, 183 (book) / PDF pp. 198, 199
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

If $k : \mathcal{X} \times \mathcal{X} \to \mathbb{R}$ is symmetric ($k(x, y) = k(y, x)$), then the Gram matrix $K \in \mathbb{R}^{n \times n}$ with $K_{ij} = k(x_i, x_j)$ is symmetric: $K^\top = K$.

## Proof (verbatim)

Not stated as a numbered lemma. Bach takes symmetry of $K$ for granted; see p. 183:

"*The associated kernel matrix is then a matrix of dot products between pairs of points (i.e., the Gram matrix of feature vectors) and is thus symmetric positive semidefinite (see the proof of proposition 7.3).*"

The proof is one-line algebra: $K_{ji} = k(x_j, x_i) = k(x_i, x_j) = K_{ij}$, using the assumed symmetry of $k$. (Sketch.)

## Notes

- Lean form `gramMatrix_symm` in `LTFP/Ch07_Kernels/Algorithms.lean`.
- Bach derives symmetry from the dot-product representation; we generalize to "any symmetric kernel."
- Critical for the closed-form KRR derivation: the optimality condition $(K^2 + n\lambda K)\alpha = Ky$ implicitly uses $K^\top = K$.
- Combined with PSD-ness this gives the full "symmetric positive semidefinite" characterization that powers the spectral theorem applied to $K$ (used in §7.6).

## Prerequisites (Bach's dependency graph)

- [`gram-matrix`](./gram-matrix.md) — Gram matrix Kᵢⱼ = k(xᵢ, xⱼ)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch07_Kernels/Algorithms.lean`
- **Theorem/def name:** `gramMatrix_symm_of_symm_kernel`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

