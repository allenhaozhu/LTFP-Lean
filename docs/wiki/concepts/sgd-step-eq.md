# SGD update increment formula (definitional)

**ID:** `sgd-step-eq`  
**Chapter:** Ch05 (Bach §F3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Gradient-descent`, `SGD`

## Statement

_See textbook excerpt below or [`tasks/sgd-step-eq/`](../../../tasks/sgd-step-eq/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — SGD update increment formula (definitional)

**Concept ID:** `sgd-step-eq`
**Chapter:** Ch 5
**Section:** 5.4 (Algorithm 5.2, definitional rewrite)
**Pages:** 134-135 (book), PDF pp. 150-151
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Definitional rewrite of the SGD update map: for estimator $g : \mathbb{R}^d \to \mathbb{R}^d$,
step size $\gamma \in \mathbb{R}$, and point $\theta \in \mathbb{R}^d$,
$$\text{sgdStep}(g, \gamma, \theta) = \theta - \gamma \cdot g(\theta).$$
This is the algebraic form of Algorithm 5.2; the stochastic content lives
entirely in the choice of `g`.

## Proof (verbatim)

By definition. Exists as a separate lemma to expose the increment to rewrite
tactics.

## Notes

- The structural twin of `gd-step-eq`. The two update maps are algebraically
  identical; their distinct names track *semantic* roles in Lean.
- No probabilistic hypotheses (H-1) or (H-2) needed — purely definitional.

## Prerequisites (Bach's dependency graph)

- [`stochastic-gd-foundation`](./stochastic-gd-foundation.md) — Stochastic gradient descent foundation: sgdStep

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/StochasticGD.lean`
- **Theorem/def name:** `sgdStep_eq`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

