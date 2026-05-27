# ReLU is monotone

**ID:** `relu-mono`  
**Chapter:** Ch09 (Bach §F6)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/relu-mono/`](../../../tasks/relu-mono/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — ReLU is monotone

**Concept ID:** `relu-mono`
**Chapter:** Ch 9
**Section:** 9.2 / 9.3.3 (used implicitly)
**Pages:** 253-254, 260-263 (book; PDF pages 269-270, 276-279)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For all z, z' ∈ R with z ≤ z',

>     relu(z) = (z)_+ ≤ (z')_+ = relu(z').

Bach does not isolate this as a lemma. He invokes monotonicity-of-`max(·, 0)`
implicitly when arguing about the slopes of (w^⊤ x + b)_+ on the two sides of a
kink (§9.3.1, §9.3.3).

## Proof (verbatim)

Immediate from `max(·, 0)` being monotone non-decreasing (`max` is monotone in each
argument).

Equivalent argument: `(z)_+ = max(z, 0) ≤ max(z', 0) = (z')_+` since z ≤ z' and
0 ≤ 0.

## Notes

- **Intermediate lemmas:** monotonicity of `max` in each argument (standard).
- **Technique in one line:** monotone-in-each-argument property of `max`, applied
  to the pair (z, z') and the constant pair (0, 0).
- **Where used in Bach.** Used implicitly in the CPA construction (p. 257) when
  reasoning that the slope of (w^⊤ x + b)_+ is 0 on one side of the kink b = −w^⊤ x
  and is the slope of `w^⊤ x + b` on the other side.
- **Also used implicitly in §9.2.3** (p. 254, equation derivation before (9.3))
  through proposition 4.3 / 4.4 of chapter 4: the 1-Lipschitz contraction property
  of ReLU. Monotonicity is a corollary of being 1-Lipschitz with `relu(0) = 0`,
  but is also the simpler standalone fact.

## Prerequisites (Bach's dependency graph)

- [`neural-net-foundation`](./neural-net-foundation.md) — Neural-network foundation: ReLU activation

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/NeuralNet.lean`
- **Theorem/def name:** `relu_mono`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

