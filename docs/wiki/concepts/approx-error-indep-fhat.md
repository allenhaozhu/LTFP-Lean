# Approximation error independent of specific predictor

**ID:** `approx-error-indep-fhat`  
**Chapter:** Ch04 (Bach §4.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/approx-error-indep-fhat/`](../../../tasks/approx-error-indep-fhat/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Approximation error independent of specific predictor

**Concept ID:** `approx-error-indep-fhat`
**Chapter:** Ch 4
**Section:** 4.3
**Pages:** 84-85
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
The approximation error
$$\text{approx}(F) = \inf_{f \in F} R(f) - R^*$$
depends only on F and the data distribution p, and not on any specific predictor f̂ ∈ F.

## Proof (verbatim)
"The approximation error inf_{f ∈ F} R(f) − R^* is deterministic and depends on the
underlying distribution and class F of functions: the larger the class, the smaller the
approximation error.

Bounding the approximation error requires assumptions on the Bayes predictor (sometimes also
called the 'target function') f_*, and hence on the testing distribution."

## Notes
- Trivial structural fact: `inf` is a property of (F, p), not of any specific f̂.
- Useful as a sanity check / lemma when arguing that f̂ being random doesn't affect the
  approximation half of the excess-risk decomposition.
- Lean version: λ f̂. approx_error F p = constant_in_f_hat.

## Prerequisites (Bach's dependency graph)

- [`approximation-error`](./approximation-error.md) — Approximation error: best-in-class − Bayes risk

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/RiskDecomposition.lean`
- **Theorem/def name:** `approximationError_indep_fhat`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

