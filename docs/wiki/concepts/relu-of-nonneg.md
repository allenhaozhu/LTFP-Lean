# ReLU is identity on nonneg inputs

**ID:** `relu-of-nonneg`  
**Chapter:** Ch09 (Bach §F6)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/relu-of-nonneg/`](../../../tasks/relu-of-nonneg/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — ReLU is identity on non-negative inputs

**Concept ID:** `relu-of-nonneg`
**Chapter:** Ch 9
**Section:** 9.2 / 9.3.1 (used implicitly throughout)
**Pages:** 249, 256-257 (book; PDF pages 265, 272-273)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For all z ≥ 0,

>     relu(z) = (z)_+ = max(z, 0) = z.

Bach does not isolate this as a lemma — he just writes (u)_+ = max{u, 0} (p. 249)
and uses the identity-on-non-negatives behaviour silently.

## Proof (verbatim)

Immediate: if z ≥ 0, then max(z, 0) = z.

## Notes

- **Intermediate lemmas:** none.
- **Technique in one line:** definition of `max` on a non-negative argument.
- **Where used in Bach.** Equation (9.6) p. 257 uses the identity in the form
  `(x − a_0)_+ = (x + R)_+ = x + R` on [−R, R] (after a_0 = −R and so x − a_0 ≥ 0).
- **Companion lemmas.** Equivalent reformulations are catalogued separately as
  `relu-eq-self-of-nonneg` (the equality variant) and `relu-le-id-of-nonneg` (the
  inequality variant `(z)_+ ≤ z` when z ≥ 0, which is in fact equality).

## Prerequisites (Bach's dependency graph)

- [`neural-net-foundation`](./neural-net-foundation.md) — Neural-network foundation: ReLU activation

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/NeuralNet.lean`
- **Theorem/def name:** `relu_of_nonneg`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

