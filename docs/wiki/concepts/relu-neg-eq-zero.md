# ReLU at strictly negative is zero

**ID:** `relu-neg-eq-zero`  
**Chapter:** Ch09 (Bach §F6)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/relu-neg-eq-zero/`](../../../tasks/relu-neg-eq-zero/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — ReLU at strictly negative input is zero

**Concept ID:** `relu-neg-eq-zero`
**Chapter:** Ch 9
**Section:** 9.2 (F6 foundation file in LTFP-Lean)
**Pages:** 249, 256-257 (book; PDF pages 265, 272-273)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For all z < 0,

>     relu(z) = (z)_+ = 0.

Bach uses this implicitly throughout §9.3 when arguing that (w^⊤ x + b)_+ is
zero on the half-space w^⊤ x + b < 0 (the "switched off" side of the ReLU).

## Proof (verbatim)

If z < 0, then max(z, 0) = 0, hence (z)_+ = 0.

## Notes

- **Intermediate lemmas:** none.
- **Technique in one line:** definition of `max` on a strictly negative
  argument.
- **Where used in Bach.** Equation (9.9), p. 263:
  > using the fact that (x − b)_+ = 0 as soon as b > x.
  is precisely this lemma applied to z = x − b. This vanishing is what makes
  the upper-limit of integration finite (the integral truncates at b = x), and
  is essential to the Taylor-with-integral-remainder proof of equation (9.10).
- **Companion lemmas.** `relu-eq-zero-iff` is the biconditional version
  (`relu(z) = 0 ↔ z ≤ 0`).

## Prerequisites (Bach's dependency graph)

- [`neural-net-foundation`](./neural-net-foundation.md) — Neural-network foundation: ReLU activation

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/NeuralNet.lean`
- **Theorem/def name:** `relu_neg_eq_zero`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

