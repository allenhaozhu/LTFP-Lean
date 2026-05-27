# ReLU(z) = 0 ↔ z ≤ 0

**ID:** `relu-eq-zero-iff`  
**Chapter:** Ch09 (Bach §F6)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/relu-eq-zero-iff/`](../../../tasks/relu-eq-zero-iff/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — ReLU(z) = 0 ↔ z ≤ 0

**Concept ID:** `relu-eq-zero-iff`
**Chapter:** Ch 9
**Section:** 9.2 (F6 foundation file in LTFP-Lean)
**Pages:** 249, 263 (book; PDF pages 265, 279)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For all z ∈ R,

>     relu(z) = (z)_+ = 0   ⟺   z ≤ 0.

## Proof (verbatim)

Two directions:

- (⇒) If max(z, 0) = 0 then z ≤ max(z, 0) = 0.
- (⇐) If z ≤ 0 then max(z, 0) = 0.

## Notes

- **Intermediate lemmas:** `z ≤ max(z, 0)` (a `le_max_left`-style fact) for the
  forward direction; `max(z, 0) = 0 ↔ z ≤ 0` is precisely the statement.
- **Technique in one line:** definition of `max` plus a sign case split.
- **Where used in Bach.** Equation (9.9), p. 263 ("(x − b)_+ = 0 as soon as
  b > x") uses the ⇐ direction. Several arguments in §9.3 implicitly use the
  ⇒ direction to characterise the active region of a hidden neuron.
- **Companion lemmas.** `relu-neg-eq-zero` is the strict-inequality one-sided
  version.

## Prerequisites (Bach's dependency graph)

- [`neural-net-foundation`](./neural-net-foundation.md) — Neural-network foundation: ReLU activation

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/NeuralNet.lean`
- **Theorem/def name:** `relu_eq_zero_iff`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

