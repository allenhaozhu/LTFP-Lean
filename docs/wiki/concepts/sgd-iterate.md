# Multi-step SGD iterate

**ID:** `sgd-iterate`  
**Chapter:** Ch05 (Bach §5.4, p. 134)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Gradient-descent`, `SGD`

## Statement

_See textbook excerpt below or [`tasks/sgd-iterate/`](../../../tasks/sgd-iterate/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Multi-step SGD iterate

**Concept ID:** `sgd-iterate`
**Chapter:** Ch 5
**Section:** 5.4 (Algorithm 5.2, recursion form)
**Pages:** 134-135 (book), PDF pp. 150-151
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

The SGD iterate is the recursion $\theta_t = \theta_{t-1} - \gamma_t g_t(\theta_{t-1})$
for $t\ge 1$, starting from $\theta_0\in\mathbb{R}^d$, where $g_t$ is a
stochastic gradient estimator satisfying $\mathbb{E}[g_t(\theta_{t-1})\,|\,\theta_{t-1}] = F'(\theta_{t-1})$.

In Lean: `sgdIterate : ℕ → Rd` with `sgdIterate 0 = θ₀` and
`sgdIterate (t+1) = sgdStep (g t) γ (sgdIterate t)`, parameterised by a family
of (random) estimators `g : ℕ → Rd → Rd`.

## Proof (verbatim)

Definitional. Bach emphasises:
- "Note that we need to condition over $\theta_{t-1}$ because $\theta_{t-1}$
  encapsulates all the randomness due to past iterations, and we only require
  fresh randomness at time $t$."
- The estimator family $g_t$ is allowed to depend on the iteration index.

## Notes

- Used in Proposition 5.7 (SGD for convex Lipschitz $F$) and Proposition 5.8
  (SGD for strongly convex problems).
- The Lean definition does *not* require the unbiasedness hypothesis as part of
  the iterate; that is a separate hypothesis attached to convergence theorems.
- For Bach's two ML setups: (i) ERM with sampling-with-replacement, (ii) single-
  pass on fresh i.i.d. samples (yielding a generalisation bound directly).

## Prerequisites (Bach's dependency graph)

- [`stochastic-gd-foundation`](./stochastic-gd-foundation.md) — Stochastic gradient descent foundation: sgdStep

## Dependents (concepts that use this)

- [`sgd-iterate-zero-step`](./sgd-iterate-zero-step.md) — SGD with zero step size is a no-op

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch05_Optimization/SGD.lean`
- **Theorem/def name:** `sgdIterate`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

