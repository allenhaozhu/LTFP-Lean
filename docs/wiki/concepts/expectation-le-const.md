# Expectation bounded by a sup constant

**ID:** `expectation-le-const`  
**Chapter:** Ch05 (Bach §F9)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/expectation-le-const/`](../../../tasks/expectation-le-const/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Expectation bounded by a sup constant

**Concept ID:** `expectation-le-const`
**Chapter:** Ch 5
**Section:** §5.4 / Foundation F9 (corollary of expectation-mono + expectation-const)
**Pages:** 134-138 (book)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

If $X \le c$ almost surely (with $c$ a constant) and $\mu$ is a probability
measure, then $\mathbb{E}[X] \le c$.

Bach uses this style of reasoning in the proof of Proposition 5.7 when bounding
$\mathbb{E}\|g_t(\theta_{t-1})\|_2^2 \le B^2$ from the a.s. bound (H-2)
$\|g_t(\theta_{t-1})\|_2^2 \le B^2$ (PDF p. 153).

## Proof (verbatim)

Combination of two foundation lemmas: by `expectation-mono`, $X \le c$ a.s.
gives $\mathbb{E}[X] \le \mathbb{E}[c]$; by `expectation-const`, $\mathbb{E}[c] = c$.

## Notes

- Lean form: `(∀ᵐ x ∂μ, X x ≤ c) → IsProbabilityMeasure μ → ∫ x, X x ∂μ ≤ c`.
- Foundation lemma; not in Mathlib as a one-line statement but immediate from
  `integral_mono` and `integral_const`.
- Paired with `expectation-ge-const` to give `expectation-in-interval`.

## Prerequisites (Bach's dependency graph)

- [`expectation-const`](./expectation-const.md) — E[c] = c under probability measure
- [`expectation-mono`](./expectation-mono.md) — Expectation is monotone

## Dependents (concepts that use this)

- [`abs-expectation-bounded`](./abs-expectation-bounded.md) — Bounded RV: |X| ≤ B ⇒ |E[X]| ≤ B
- [`expectation-in-interval`](./expectation-in-interval.md) — m ≤ X ≤ M ⇒ m ≤ E[X] ≤ M

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/MeasureProb.lean`
- **Theorem/def name:** `expectation_le_const_of_le`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

