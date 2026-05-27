# Gram matrix Kᵢⱼ = k(xᵢ, xⱼ)

**ID:** `gram-matrix`  
**Chapter:** Ch07 (Bach §7.4, p. 196)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Matrix/LinAlg`

## Statement

_See textbook excerpt below or [`tasks/gram-matrix/`](../../../tasks/gram-matrix/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Gram matrix Kᵢⱼ = k(xᵢ, xⱼ)

**Concept ID:** `gram-matrix`
**Chapter:** Ch 7
**Section:** §7.4 (Algorithms) — but defined inline in §7.2 / §7.3
**Pages:** 182, 183, 196 (book) / PDF pp. 198, 199, 212
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Given $n$ data points $x_1, \dots, x_n \in \mathcal{X}$ and a positive-definite kernel $k : \mathcal{X} \times \mathcal{X} \to \mathbb{R}$, the **kernel matrix** (Gram matrix of feature vectors) $K \in \mathbb{R}^{n\times n}$ is defined by

$$K_{ij} = \langle\phi(x_i), \phi(x_j)\rangle = k(x_i, x_j).$$

Equivalently if $\Phi \in \mathbb{R}^{n \times d}$ is the feature matrix with $i$th row $\phi(x_i)$, then $K = \Phi \Phi^\top$.

## Proof (verbatim)

Bach introduces the Gram matrix as a definition right after the representer theorem:

"$K \in \mathbb{R}^{n\times n}$ is the kernel matrix (Gram matrix of the feature vectors), such that $K_{ij} = \langle\phi(x_i), \phi(x_j)\rangle = k(x_i, x_j)$" (p. 182).

The reverse-direction PSD property and the $\Phi\Phi^\top$ identity are stated again at p. 183:

"If $\mathcal{H} = \mathbb{R}^d$, and $\Phi \in \mathbb{R}^{n\times d}$ is the matrix of features (design matrix in the context of regression) with the $i$th row composed of $\phi(x_i)$, then $K = \Phi\Phi^\top \in \mathbb{R}^{n\times n}$ is the kernel matrix, while $\frac{1}{n}\Phi^\top\Phi \in \mathbb{R}^{d\times d}$ is the empirical noncentered covariance matrix."

## Notes

- Bach interchangeably uses "Gram matrix" and "kernel matrix"; the Lean encoding `gramMatrix` (in `LTFP/Ch07_Kernels/Algorithms.lean`) follows the "Gram" naming.
- The Gram matrix is automatically symmetric PSD whenever $k$ is positive-definite (Aronszajn 1950, Proposition 7.3 first half) — this is exactly the property exploited in the KRR derivation.
- Used in: KRR closed form ($\alpha = (K + n\lambda I)^{-1} y$), kernel PCA, Nyström approximation, dual problems.
- Key intermediate facts Bach cites: symmetry of $k \Rightarrow K = K^\top$; PSD of $K$ from $\alpha^\top K \alpha = \|\sum_i \alpha_i \phi(x_i)\|^2$.

## Prerequisites (Bach's dependency graph)

- [`kernel-foundation`](./kernel-foundation.md) — Positive-definite kernel foundation: IsPSDKernel

## Dependents (concepts that use this)

- [`gram-matrix-diag`](./gram-matrix-diag.md) — Gram matrix diagonal: K i i = k(xᵢ, xᵢ)
- [`gram-matrix-eq-kernel`](./gram-matrix-eq-kernel.md) — Gram matrix entry equals kernel evaluation
- [`gram-matrix-symm`](./gram-matrix-symm.md) — Gram matrix is symmetric for symmetric kernel
- [`gram-matrix-zero`](./gram-matrix-zero.md) — Gram matrix of zero kernel = 0
- [`krr-coeffs`](./krr-coeffs.md) — Kernel ridge regression coefficient α̂_λ = (K + nλI)⁻¹ y

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch07_Kernels/Algorithms.lean`
- **Theorem/def name:** `gramMatrix`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

