# SGD step with zero step is no-op (any estimator)

**ID:** `sgd-step-zero-step`  
**Chapter:** Ch05 (Bach §F3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Gradient-descent`, `SGD`

## Statement

_See textbook excerpt below or [`tasks/sgd-step-zero-step/`](../../../tasks/sgd-step-zero-step/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — SGD step with zero step is no-op (any estimator)

**Concept ID:** `sgd-step-zero-step`
**Chapter:** Ch 5
**Section:** 5.4 (Algorithm 5.2, $\gamma = 0$ instance)
**Pages:** 134-135 (book), PDF pp. 150-151
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For any (possibly random) estimator $g : \mathbb{R}^d \to \mathbb{R}^d$ and
point $\theta$,
$$\text{sgdStep}(g, 0, \theta) = \theta - 0 \cdot g(\theta) = \theta.$$
Bach does not single this out; it is immediate from Algorithm 5.2 with
$\gamma_t = 0$.

## Proof (verbatim)

Algebraic: $0 \cdot v = 0$ in $\mathbb{R}^d$, so $\theta - 0 \cdot g(\theta) = \theta$.

## Notes

- The SGD-flavour mirror of `gd-step-zero-step`. Holds for arbitrary estimator
  `g`, requiring neither (H-1) unbiasedness nor (H-2) bounded gradients —
  the result is algebraic, not probabilistic.
- Lean form: `sgdStep g 0 θ = θ`.
- Used as the rewrite at the successor step in `sgd-iterate-zero-step`.

## Prerequisites (Bach's dependency graph)

- [`stochastic-gd-foundation`](./stochastic-gd-foundation.md) — Stochastic gradient descent foundation: sgdStep

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/StochasticGD.lean`
- **Theorem/def name:** `sgdStep_zero_step`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

