# Multicategory loss is bounded by 1

**ID:** `multicategory-loss-le-one`  
**Chapter:** Ch13 (Bach §13.1.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/multicategory-loss-le-one/`](../../../tasks/multicategory-loss-le-one/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Multicategory loss is bounded by 1

**Concept ID:** `multicategory-loss-le-one`
**Chapter:** Ch 13
**Section:** 13.1.1 / 13.2 (loss-matrix range)
**Pages:** 380, 387
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Sanity lemma: `multicategoryLoss y ŷ ≤ 1` for all `y, ŷ`.

This is a direct consequence of Bach's loss-matrix specialization to the
0-1 loss in §13.2 (page 387):

> "The usual 0–1 loss from section 13.1 corresponds to L_{ij} = 1_{i≠j}."

An indicator function takes values in `{0, 1}` and therefore is bounded
above by `1`. Bach uses this implicit upper bound throughout Chapter 13
when stating generalization bounds — for instance, in §13.1.2 / §13.1.3 he
applies Rademacher / bounded-difference arguments that need the loss to be
bounded in `[0, 1]`.

## Proof (verbatim)
Definitional. The 0-1 indicator `1_{y ≠ ŷ}` is either `0` or `1`; in
either case it is `≤ 1`. In Lean's `if-then-else` form: both branches
(`0` and `1`) satisfy `_ ≤ 1`, so the `if` is `≤ 1`.

## Notes
- Used as a bounded-loss precondition for any Rademacher / McDiarmid /
  Hoeffding bound applied to the multicategory loss.
- Technique in one line: case-split on `y = ŷ`; both branches are `≤ 1`.
- No ambiguity — purely the range of a 0-1 indicator.

## Prerequisites (Bach's dependency graph)

- [`multicategory-loss`](./multicategory-loss.md) — Multicategory 0-1 loss for k classes

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch13_StructuredPrediction/Multicategory.lean`
- **Theorem/def name:** `multicategoryLoss_le_one`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

