# Kernel-expansion predictor f(x) = ∑ᵢ αᵢ k(x, xᵢ)

**ID:** `kernel-expansion`  
**Chapter:** Ch07 (Bach §7.2, p. 181)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Kernel`

## Statement

_See textbook excerpt below or [`tasks/kernel-expansion/`](../../../tasks/kernel-expansion/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Kernel-expansion predictor f(x) = ∑ᵢ αᵢ k(x, xᵢ)

**Concept ID:** `kernel-expansion`
**Chapter:** Ch 7
**Section:** §7.2 (Representer Theorem)
**Pages:** 181-182 (book) / PDF pp. 197-198
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Given a feature map $\phi : \mathcal{X} \to \mathcal{H}$, training inputs $x_1, \dots, x_n \in \mathcal{X}$, coefficients $\alpha \in \mathbb{R}^n$, and a parameter $\theta = \sum_{i=1}^n \alpha_i \phi(x_i)$, the prediction function at any test point $x \in \mathcal{X}$ is

$$f(x) = \langle \theta, \phi(x)\rangle = \sum_{i=1}^n \alpha_i \langle \phi(x_i),\phi(x)\rangle = \sum_{i=1}^n \alpha_i k(x, x_i).$$

The kernel function $k : \mathcal{X} \times \mathcal{X} \to \mathbb{R}$ is the symmetric dot-product map $k(x, x') = \langle\phi(x), \phi(x')\rangle$.

## Proof (verbatim)

Bach derives this expression as the **immediate consequence** of the Representer Theorem (Proposition 7.1 / Corollary 7.1, p. 181) plus the definition of the kernel:

"Given corollary 7.1, we can reformulate the learning problem. We will need the kernel function $k : \mathcal{X} \times \mathcal{X} \to \mathbb{R}$, which is a symmetric function equal to the dot product between feature vectors: $k(x, x') = \langle\phi(x), \phi(x')\rangle.$ We then have, if $\theta = \sum_{i=1}^n \alpha_i \phi(x_i)$,
$$\forall j \in \{1, \dots, n\},\ \langle\theta, \phi(x_j)\rangle = \sum_{i=1}^n \alpha_i k(x_i, x_j) = (K\alpha)_j,$$
… Note that for any test point $x \in \mathcal{X}$, we have defined the prediction function as
$$f(x) = \langle\theta, \phi(x)\rangle = \sum_{i=1}^n \alpha_i \langle\phi(x_i), \phi(x)\rangle = \sum_{i=1}^n \alpha_i k(x, x_i).$$"

## Notes

- This is the **algorithmic payoff** of the representer theorem: the predictor only ever needs kernel evaluations $k(x, x_i)$ — never the (possibly infinite-dimensional) feature vector $\phi(x)$ itself.
- Bach calls this principle the **kernel trick** (p. 182): "explicitly computing the feature vector $\phi(x)$ is never needed, as we solely need dot products."
- Lean form `kernelExpansion` lives in `LTFP/Ch07_Kernels/Representer.lean`; it is the canonical predictor template used by KRR (`krrPredictor` = `kernelExpansion ∘ krrCoeffs`).
- Proof technique: bilinearity of the inner product, applied to the finite sum $\sum_i \alpha_i \phi(x_i)$.

## Prerequisites (Bach's dependency graph)

- [`kernel-foundation`](./kernel-foundation.md) — Positive-definite kernel foundation: IsPSDKernel

## Dependents (concepts that use this)

- [`kernel-expansion-add`](./kernel-expansion-add.md) — Kernel expansion is linear in coefficients
- [`kernel-expansion-at-train-input`](./kernel-expansion-at-train-input.md) — Kernel expansion at training input
- [`kernel-expansion-eq`](./kernel-expansion-eq.md) — Kernel expansion definitional
- [`kernel-expansion-smul`](./kernel-expansion-smul.md) — Kernel expansion is homogeneous in coefficients
- [`krr-predictor`](./krr-predictor.md) — Kernel ridge regression predictor
- [`representer-theorem`](./representer-theorem.md) — Representer theorem (orthogonal-projection core)

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch07_Kernels/Representer.lean`
- **Theorem/def name:** `kernelExpansion`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

