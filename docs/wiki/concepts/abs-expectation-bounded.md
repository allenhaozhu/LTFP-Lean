# Bounded RV: |X| ≤ B ⇒ |E[X]| ≤ B

**ID:** `abs-expectation-bounded`  
**Chapter:** Ch05 (Bach §F9)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/abs-expectation-bounded/`](../../../tasks/abs-expectation-bounded/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Bounded RV: |X| ≤ B ⇒ |E[X]| ≤ B

**Concept ID:** `abs-expectation-bounded`
**Chapter:** Ch 5
**Section:** §5.4 / Foundation F9 (corollary of triangle + bounded)
**Pages:** 134-138 (book)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

If $|X| \le B$ almost surely (with $B \ge 0$) and $\mu$ is a probability
measure, then $|\mathbb{E}[X]| \le B$.

Bach uses this style of bound (without explicitly stating it as a lemma) in
the SGD analysis whenever the stochastic gradient has an a.s. bound (H-2)
and one wants a numerical bound on the expectation.

## Proof (verbatim)

Combination of two foundation lemmas:
1. By `abs-expectation-le-exp-abs` (Jensen / triangle):
   $|\mathbb{E}[X]| \le \mathbb{E}[|X|]$.
2. By `expectation-le-const` applied to $|X| \le B$:
   $\mathbb{E}[|X|] \le B$.
Chaining the two gives $|\mathbb{E}[X]| \le B$.

## Notes

- Lean form combines `abs_integral_le_integral_abs` with the corollary
  `expectation-le-const`.
- Used in any convergence proof that wants to translate "$|g| \le B$ a.s." into
  a deterministic bound on $\|\mathbb{E}[g]\|$.
- Essentially the practical workhorse of bounded-stochastic-gradient analysis.

## Prerequisites (Bach's dependency graph)

- [`abs-expectation-le-exp-abs`](./abs-expectation-le-exp-abs.md) — Triangle inequality for expectation |E[X]| ≤ E[|X|]
- [`expectation-le-const`](./expectation-le-const.md) — Expectation bounded by a sup constant

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/MeasureProb.lean`
- **Theorem/def name:** `abs_expectation_le_of_bounded`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

