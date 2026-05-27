# ReLU subadditivity: relu(x+y) ≤ relu x + relu y

**ID:** `relu-add-le`  
**Chapter:** Ch09 (Bach §F6)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/relu-add-le/`](../../../tasks/relu-add-le/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — ReLU subadditivity

**Concept ID:** `relu-add-le`
**Chapter:** Ch 9
**Section:** 9.2 / 9.3 (used implicitly)
**Pages:** 253, 261 (book; PDF pages 269, 277)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For all x, y ∈ R,

>     relu(x + y) = (x + y)_+ ≤ (x)_+ + (y)_+ = relu(x) + relu(y).

Bach does not state this explicitly. The lemma is the convexity / sub-additivity
property of the `max(·, 0)` function (which is convex, with f(0) = 0).

## Proof (verbatim)

Two-line case split:

- (x + y)_+ = max(x + y, 0). Since `(x)_+ + (y)_+ ≥ x + y` (each term is ≥ its
  argument) and `(x)_+ + (y)_+ ≥ 0` (both terms are ≥ 0), we get
  `(x)_+ + (y)_+ ≥ max(x + y, 0) = (x + y)_+`.

Equivalently, ReLU is convex with ReLU(0) = 0, so for λ = 1/2, sub-additivity is
a special case of Jensen / convexity.

## Notes

- **Intermediate lemmas:** none beyond `max(a, b) ≥ a` and `max(a, b) ≥ b`.
- **Technique in one line:** two `max` lower bounds + transitivity.
- **Where used in Bach (implicitly).** Convexity of ReLU is the only structural
  fact Bach needs for the variation-norm machinery: the convex hull of single-
  neuron functions s(w^⊤ · + b)_+ is the unit ball of γ_1 (§9.3.2, §9.3.6). The
  point-wise sub-additivity inequality is a downstream consequence of this
  convexity.

## Prerequisites (Bach's dependency graph)

- [`neural-net-foundation`](./neural-net-foundation.md) — Neural-network foundation: ReLU activation

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/NeuralNet.lean`
- **Theorem/def name:** `relu_add_le`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

