# Uniform local-averaging weights wᵢ(x) = 1/n

**ID:** `uniform-local-weights`  
**Chapter:** Ch06 (Bach §6.2.1, p. 157)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/uniform-local-weights/`](../../../tasks/uniform-local-weights/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Uniform local-averaging weights wᵢ(x) = 1/n

**Concept ID:** `uniform-local-weights`
**Chapter:** Ch 6
**Section:** 6.2.1
**Pages:** 157
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
From §6.2.1 "Linear Estimators" (p. 157), Bach introduces the general linear estimator template:

> In this chapter, we will consider linear estimators, where the conditional distribution is of the form
> $$\hat p(y\mid x) = \sum_{i=1}^{n} \hat w_i(x)\,\delta_{y_i}(y),$$
> where $\delta_{y_i}$ is the Dirac probability distribution at $y_i$ (putting a unit mass at $y_i$), and the weight functions $\hat w_i : \mathcal X \to \mathbb R$, $i = 1, \ldots, n$ depend on the input data only (for simplicity) and satisfies (almost surely in $x$):
> $$\forall x \in \mathcal X,\ \forall i \in \{1, \ldots, n\},\ \hat w_i(x) \geqslant 0,\ \text{and}\ \sum_{i=1}^{n} \hat w_i(x) = 1. \quad (6.1)$$

For regression (p. 157):

> For regression: $\mathcal Y = \mathbb R$: $\hat f(x) = \sum_{i=1}^{n} \hat w_i(x)\, y_i$. This is why the terminology "linear estimators" is sometimes used: as a function of the response vector in $\mathbb R^n$, the estimator is linear.

The **uniform** weight scheme `wᵢ(x) = 1/n` is the canonical fallback case Bach uses repeatedly: it is invoked in (6.2) on p. 158 as the convention when no training point falls in a partition cell ("if no training data point lies in $A(x)$, then $\hat w_i(x)$ is equal to $1/n$ for each $i$"), and again in §6.2.4 (p. 162) for kernel weights when all kernel evaluations vanish.

## Proof (verbatim)
N/A — this is a definition. Bach introduces the uniform-weight fallback in two paragraphs:

> (p. 158) with the convention that if no training data point lies in $A(x)$, then $\hat w_i(x)$ is equal to $1/n$ for each $i \in \{1, \ldots, n\}$.

> (p. 162) with the convention that if $k(x, x_i) = 0$ for all $i \in \{1, \ldots, n\}$, then $\hat w_i(x)$ is equal to $1/n$ for each $i$ (which is the same convention used for estimators based on partitions in section 6.2.2).

The constant weight `1/n` trivially satisfies (6.1): nonneg, and `∑ 1/n = 1`.

## Notes
- Lean carrier: `LTFP/Ch06_LocalAveraging/Estimators.lean#uniformWeights`. The Lean definition strips the input-dependence, giving the constant scheme `(fun _ _ => (n : ℝ)⁻¹)` — appropriate since uniformity in `x` is the defining feature.
- Companion theorem `uniformWeights_localAvg_eq_mean` (proved alongside) recovers the empirical mean: `localAvg Y uniformWeights x = (1/n) · ∑ Y i`.
- Bach uses this as the **degenerate** weight scheme — both as a fallback when no neighbors exist (partitions, kernels) and as the worst-case "underfitting" bias scenario (§6.3, p. 165: "the worst-case scenario is that weights are uniform (leading to underfitting)").
- No proof technique needed — pure definition.

## Prerequisites (Bach's dependency graph)

- [`local-averaging`](./local-averaging.md) — Local averaging predictors (k-NN, partition, kernel)

## Dependents (concepts that use this)

- [`local-avg-bias-term`](./local-avg-bias-term.md) — Pointwise bias term of a local-averaging estimator

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch06_LocalAveraging/Estimators.lean`
- **Theorem/def name:** `uniformWeights`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

