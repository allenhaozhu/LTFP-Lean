# relu z ≤ z when z ≥ 0

**ID:** `relu-le-id-of-nonneg`  
**Chapter:** Ch09 (Bach §F6)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/relu-le-id-of-nonneg/`](../../../tasks/relu-le-id-of-nonneg/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — relu z ≤ z when z ≥ 0

**Concept ID:** `relu-le-id-of-nonneg`
**Chapter:** Ch 9
**Section:** 9.2 (F6 foundation file in LTFP-Lean)
**Pages:** 249 (book; PDF page 265)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For all z ≥ 0,

>     relu(z) = (z)_+ ≤ z.

(In fact equality, see `relu-eq-self-of-nonneg`. The inequality form is the weaker
half kept as a separate lemma in the LTFP-Lean foundation file.)

## Proof (verbatim)

If z ≥ 0, then (z)_+ = max(z, 0) = z, hence (z)_+ ≤ z trivially.

## Notes

- **Intermediate lemmas:** none.
- **Technique in one line:** equality on non-negatives implies the inequality.
- **Why kept as a separate lemma.** Useful for one-sided bounds where the
  caller doesn't want to perform the case split or doesn't care about equality.
  Bach does not isolate it; this is an LTFP-Lean foundation convenience.

## Prerequisites (Bach's dependency graph)

- [`neural-net-foundation`](./neural-net-foundation.md) — Neural-network foundation: ReLU activation

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/NeuralNet.lean`
- **Theorem/def name:** `relu_le_id_of_nonneg`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

