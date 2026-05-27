# relu z = z when z ≥ 0

**ID:** `relu-eq-self-of-nonneg`  
**Chapter:** Ch09 (Bach §F6)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/relu-eq-self-of-nonneg/`](../../../tasks/relu-eq-self-of-nonneg/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — relu z = z when z ≥ 0

**Concept ID:** `relu-eq-self-of-nonneg`
**Chapter:** Ch 9
**Section:** 9.2 (F6 foundation file in LTFP-Lean)
**Pages:** 249 (book; PDF page 265)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For all z ≥ 0,

>     relu(z) = (z)_+ = z.

Bach writes (u)_+ = max{u, 0} (p. 249); the identity-on-non-negatives equality
is the immediate consequence.

## Proof (verbatim)

If z ≥ 0, then max(z, 0) = z, hence (z)_+ = z.

## Notes

- **Intermediate lemmas:** none.
- **Technique in one line:** definition of `max` on a non-negative argument.
- **Used in Bach.** Equation (9.6), p. 257: `(x − a_0)_+ = (x + R)_+ = x + R` on
  [−R, R] (since x + R ≥ 0). This is exactly the equality form.
- **Companion:** `relu-of-nonneg` (same fact, different naming convention),
  `relu-le-id-of-nonneg` (the inequality form).

## Prerequisites (Bach's dependency graph)

- [`neural-net-foundation`](./neural-net-foundation.md) — Neural-network foundation: ReLU activation

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/NeuralNet.lean`
- **Theorem/def name:** `relu_eq_self_of_nonneg`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

