# SGD with zero step size is a no-op

**ID:** `sgd-iterate-zero-step`  
**Chapter:** Ch05 (Bach §5.4)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Gradient-descent`, `SGD`

## Statement

_See textbook excerpt below or [`tasks/sgd-iterate-zero-step/`](../../../tasks/sgd-iterate-zero-step/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — SGD with zero step size is a no-op

**Concept ID:** `sgd-iterate-zero-step`
**Chapter:** Ch 5
**Section:** 5.4 (consequence of Algorithm 5.2)
**Pages:** 134-135 (book), PDF pp. 150-151
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Setting $\gamma_t = 0$ in the SGD recursion $\theta_t = \theta_{t-1} - \gamma_t g_t(\theta_{t-1})$
gives $\theta_t = \theta_{t-1}$, hence $\theta_t = \theta_0$ for every $t \ge 0$,
regardless of the stochastic estimator family $(g_t)$. Bach treats this as a
trivial algebraic observation.

## Proof (verbatim)

Immediate from Algorithm 5.2 with $\gamma_t = 0$: the update becomes the identity.

## Notes

- The proof in Lean is by induction on `t`, applying `sgdStep_zero_step` at the
  successor step.
- Holds even without hypothesis (H-1) (unbiasedness) or (H-2) (bounded estimator):
  it is purely algebraic.
- Useful for testing the SGD iterate definition and as a base case for more
  refined zero-step lemmas.

## Prerequisites (Bach's dependency graph)

- [`sgd-iterate`](./sgd-iterate.md) — Multi-step SGD iterate

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch05_Optimization/SGD.lean`
- **Theorem/def name:** `sgdIterate_zero_step`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

