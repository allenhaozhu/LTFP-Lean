# Multicat loss in 0-1 unit interval

**ID:** `multicat-loss-in-unit`  
**Chapter:** Ch13 (Bach §13.1.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/multicat-loss-in-unit/`](../../../tasks/multicat-loss-in-unit/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Multicat loss in 0-1 unit interval

**Concept ID:** `multicat-loss-in-unit`
**Chapter:** Ch 13
**Section:** 13.2 (loss-matrix definition) / 13.1.3 (Rademacher bounds)
**Pages:** 387
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Sanity lemma: `0 ≤ multicategoryLoss y ŷ ≤ 1` for all labels `y, ŷ`.

This is the joint range bound: a combination of nonnegativity (the loss
is an indicator, hence `≥ 0`) and the upper bound `≤ 1` (also from the
indicator form). Both follow from the loss-matrix specialization in
§13.2 (page 387):

> "The usual 0–1 loss from section 13.1 corresponds to L_{ij} = 1_{i≠j}."

This unit-interval boundedness is the standing hypothesis under which Bach
applies generic concentration tools in §13.1.2 / §13.1.3 (pages 382-385)
to derive Rademacher / bounded-difference generalization bounds for
multicategory classification. The two-sided bound `0 ≤ ℓ ≤ 1` is what
allows McDiarmid's inequality (Theorem 1.18 / §1.3) and the Rademacher
contraction inequality to apply directly.

## Proof (verbatim)
Definitional. Combine `multicategoryLoss y ŷ ∈ {0, 1}` (see
`multicat-zero-or-one`) with the two facts `0 ≤ 0` and `0 ≤ 1 ≤ 1`. Both
elements of `{0, 1}` lie in the unit interval, so the value does.

## Notes
- This is the bundled `[0, 1]` membership, packaged for direct use in
  Rademacher / McDiarmid / Hoeffding bounds applied to the multicategory
  loss.
- Derivable from `multicategory-loss-le-one` plus the symmetric
  nonnegativity statement, but recorded as its own lemma so downstream
  generalization-bound proofs can apply it in one rewrite.
- Technique in one line: case-split on `y = ŷ`; both branches land in
  `[0, 1]`.
- No ambiguity — joint range of a 0-1 indicator.

## Prerequisites (Bach's dependency graph)

- [`multicategory-loss`](./multicategory-loss.md) — Multicategory 0-1 loss for k classes

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch13_StructuredPrediction/Multicategory.lean`
- **Theorem/def name:** `multicategoryLoss_in_unit`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

