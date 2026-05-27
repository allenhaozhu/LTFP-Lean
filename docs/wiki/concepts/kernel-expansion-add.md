# Kernel expansion is linear in coefficients

**ID:** `kernel-expansion-add`  
**Chapter:** Ch07 (Bach §7.4.6, p. 201)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Kernel`

## Statement

_See textbook excerpt below or [`tasks/kernel-expansion-add/`](../../../tasks/kernel-expansion-add/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Kernel expansion is linear in coefficients

**Concept ID:** `kernel-expansion-add`
**Chapter:** Ch 7
**Section:** §7.4.6 (Kernelization of Linear Algorithms)
**Pages:** 201 (book) / PDF p. 217
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

The kernel-expansion predictor $f_\alpha(x) = \sum_{i=1}^n \alpha_i k(x, x_i)$ is *additive* in the coefficient vector: for all $\alpha, \beta \in \mathbb{R}^n$,

$$f_{\alpha + \beta}(x) = f_\alpha(x) + f_\beta(x), \qquad \forall x \in \mathcal{X}.$$

Combined with the homogeneity property (`kernel-expansion-smul`), this means $\alpha \mapsto f_\alpha$ is $\mathbb{R}$-linear.

## Proof (verbatim)

Bach does not state this as a numbered theorem; it is implicit in his §7.4.6 discussion that "*these algorithms can be cast only through the matrices of dot products between observations and can thus be applied after the feature transformation*."

The algebra is one line:
$f_{\alpha + \beta}(x) = \sum_i (\alpha_i + \beta_i) k(x, x_i) = \sum_i \alpha_i k(x, x_i) + \sum_i \beta_i k(x, x_i) = f_\alpha(x) + f_\beta(x).$ (Sketch.)

This linearity is also visible in Bach's identity $\langle\theta, \phi(x_j)\rangle = (K\alpha)_j$ (p. 182), since $K(\alpha + \beta) = K\alpha + K\beta$.

## Notes

- Lean form `kernelExpansion_add` in `LTFP/Ch07_Kernels/Algorithms.lean`.
- One of the "kernelization of linear algorithms" identities that Bach groups in §7.4.6 (p. 201). Used to derive:
  - linearity of the predictor in labels (`krr-predictor-add-y`);
  - kernel PCA, kernel ridge regression composition with sum-of-targets training schemes.
- Proof technique: pure algebra (distributivity of addition over sums).

## Prerequisites (Bach's dependency graph)

- [`kernel-expansion`](./kernel-expansion.md) — Kernel-expansion predictor f(x) = ∑ᵢ αᵢ k(x, xᵢ)

## Dependents (concepts that use this)

- [`krr-predictor-add-y`](./krr-predictor-add-y.md) — KRR predictor linear in labels (composition)

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch07_Kernels/Algorithms.lean`
- **Theorem/def name:** `kernelExpansion_add`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

