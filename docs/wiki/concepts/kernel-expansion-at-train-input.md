# Kernel expansion at training input

**ID:** `kernel-expansion-at-train-input`  
**Chapter:** Ch07 (Bach §7.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Kernel`

## Statement

_See textbook excerpt below or [`tasks/kernel-expansion-at-train-input/`](../../../tasks/kernel-expansion-at-train-input/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Kernel expansion at training input

**Concept ID:** `kernel-expansion-at-train-input`
**Chapter:** Ch 7
**Section:** §7.2 (Representer Theorem) — derived identity
**Pages:** 182 (book) / PDF p. 198
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

When the kernel-expansion predictor is evaluated at a training input $x_j$, the result is the $j$-th component of $K\alpha$:

$$f_\alpha(x_j) = \sum_{i=1}^n \alpha_i\, k(x_j, x_i) = (K\alpha)_j, \qquad j \in \{1, \dots, n\}.$$

## Proof (verbatim)

Bach derives exactly this identity on p. 182:

"*We then have, if $\theta = \sum_{i=1}^n \alpha_i \phi(x_i)$,*
$$\forall j \in \{1, \dots, n\},\ \langle\theta, \phi(x_j)\rangle = \sum_{i=1}^n \alpha_i k(x_i, x_j) = (K\alpha)_j,$$
*where* $K \in \mathbb{R}^{n\times n}$ *is the kernel matrix (Gram matrix of the feature vectors), such that* $K_{ij} = \langle\phi(x_i), \phi(x_j)\rangle = k(x_i, x_j)$."

## Notes

- Lean form `kernelExpansion_at_train_input` in `LTFP/Ch07_Kernels/Representer.lean`.
- Bach uses this identity to reformulate the empirical risk solely in terms of $y, K, \alpha$ (equation (7.2), p. 182): $\frac{1}{n}\sum_i \ell(y_i, (K\alpha)_i) + \frac{\lambda}{2}\alpha^\top K\alpha$.
- Bridge between the "infinite-dimensional $\theta \in \mathcal{H}$" view and the "finite-dimensional $\alpha \in \mathbb{R}^n$" view of representer-theorem algorithms.
- Proof technique: expand $\theta = \sum_i \alpha_i \phi(x_i)$, use bilinearity of $\langle\cdot,\cdot\rangle$, then apply the kernel definition $k(x_i, x_j) = \langle\phi(x_i),\phi(x_j)\rangle$.

## Prerequisites (Bach's dependency graph)

- [`kernel-expansion`](./kernel-expansion.md) — Kernel-expansion predictor f(x) = ∑ᵢ αᵢ k(x, xᵢ)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch07_Kernels/Representer.lean`
- **Theorem/def name:** `kernelExpansion_at_train_input`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

