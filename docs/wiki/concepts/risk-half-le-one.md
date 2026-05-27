# Risk ≤ 1/2 implies risk ≤ 1

**ID:** `risk-half-le-one`  
**Chapter:** Ch15 (Bach §15.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/risk-half-le-one/`](../../../tasks/risk-half-le-one/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Risk ≤ 1/2 implies risk ≤ 1

**Concept ID:** `risk-half-le-one`
**Chapter:** Ch 15
**Section:** §15.1.4 (Cor 15.1 derivation)
**Pages:** 437 (book) / 453 (PDF)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Carrier `LTFP.Ch15_LowerBounds.Statistical.risk_half_le_one`. Algebraic
implication used in Bach's chain when bounding the testing error after
applying Fano:

> If a risk `R` satisfies `R ≤ 1/2`, then `R ≤ 1`.

The Lean proof is `by linarith`.

## Proof (verbatim)

Bach §15.1.5 (p. 437), the calculation following Lemma 15.2:

> "Then, the minimax lower bound is A/2. Thus, the lower bound is
> essentially the largest possible A for a given M such that we can
> find M points in Θ, which are all 2√A apart."

When Bach derives `A · (1 − log 2/log M · ¼ · log(M) − ¼) = A/2`, the
A/2 numeric upper bound is what is propagated; the chain `R ≤ 1/2 ≤ 1`
keeps the risk in the unit interval throughout.

## Notes

- **Bach's technique in one line:** standard chaining of unit-interval
  upper bounds — once `R ≤ 1/2`, the cruder bound `R ≤ 1` follows.
- Used in the algebraic post-processing of Fano outputs.

## Prerequisites (Bach's dependency graph)

- [`testing-error-nonneg`](./testing-error-nonneg.md) — Statistical lower-bound anchor: testing error nonneg

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch15_LowerBounds/Statistical.lean`
- **Theorem/def name:** `risk_half_le_one`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

