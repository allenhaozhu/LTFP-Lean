# SGD with sum-of-estimators algebraic rewrite

**ID:** `sgd-add-g`  
**Chapter:** Ch05 (Bach §F3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Gradient-descent`, `SGD`

## Statement

_See textbook excerpt below or [`tasks/sgd-add-g/`](../../../tasks/sgd-add-g/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — SGD with sum-of-estimators algebraic rewrite

**Concept ID:** `sgd-add-g`
**Chapter:** Ch 5
**Section:** 5.4 (algebraic rearrangement of Algorithm 5.2)
**Pages:** 134-135 (book), PDF pp. 150-151
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For two estimators $g_1, g_2 : \mathbb{R}^d \to \mathbb{R}^d$ and point $\theta$,
$$\text{sgdStep}(g_1 + g_2,\, \gamma,\, \theta) = \theta - \gamma(g_1(\theta) + g_2(\theta)) = \text{sgdStep}(g_1, \gamma, \theta) - \gamma \cdot g_2(\theta).$$
This linearity of the SGD update in the estimator is implicit in Bach's
treatment of mini-batch SGD (Section 5.4, after Algorithm 5.2), where the
mini-batch estimator is the *average* of per-sample estimators and the
expectation distributes linearly across the sum.

## Proof (verbatim)

Algebraic distributivity of scalar multiplication over addition in
$\mathbb{R}^d$: $\gamma(g_1(\theta) + g_2(\theta)) = \gamma g_1(\theta) + \gamma g_2(\theta)$.

## Notes

- Foundation-level algebraic helper, no probabilistic content.
- Useful in mini-batch analyses (Exercise 5.27) where one decomposes the
  batch gradient as a sum of per-sample stochastic gradients and applies
  expectation pointwise via (H-1).
- Lean form: `sgdStep (fun θ => g₁ θ + g₂ θ) γ θ = sgdStep g₁ γ θ - γ • g₂ θ`.

## Prerequisites (Bach's dependency graph)

- [`stochastic-gd-foundation`](./stochastic-gd-foundation.md) — Stochastic gradient descent foundation: sgdStep

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/StochasticGD.lean`
- **Theorem/def name:** `sgdStep_add_g`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

