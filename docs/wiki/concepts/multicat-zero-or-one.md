# Multicat loss is 0 or 1

**ID:** `multicat-zero-or-one`  
**Chapter:** Ch13 (Bach §13.1.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/multicat-zero-or-one/`](../../../tasks/multicat-zero-or-one/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Multicat loss is 0 or 1

**Concept ID:** `multicat-zero-or-one`
**Chapter:** Ch 13
**Section:** 13.2 (loss-matrix definition)
**Pages:** 387
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Sanity lemma: `multicategoryLoss y ŷ = 0 ∨ multicategoryLoss y ŷ = 1`
for all labels `y, ŷ`.

Bach does not state this as a numbered proposition — it is the trichotomy
fact that an indicator-valued loss only takes two values. From §13.2
(page 387):

> "The usual 0–1 loss from section 13.1 corresponds to L_{ij} = 1_{i≠j}."

The Iverson bracket `1_{i ≠ j}` equals `1` when `i ≠ j` and `0` when
`i = j`; no other values are possible. This dichotomy is what justifies
the name "0–1 loss" and what makes it bounded (see also
`multicategory-loss-le-one`).

## Proof (verbatim)
Definitional. Case-split on `y = ŷ`. In Lean's `if-then-else`: the
"then" branch is `0`, the "else" branch is `1`, so the value is in
`{0, 1}` either way.

## Notes
- Used as a precondition for Bernoulli/Hoeffding-style bounds, where the
  loss must take values in a two-point set.
- Technique in one line: case-split + matching constructor.
- No ambiguity. This is the defining property of an indicator function.

## Prerequisites (Bach's dependency graph)

- [`multicategory-loss`](./multicategory-loss.md) — Multicategory 0-1 loss for k classes

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch13_StructuredPrediction/Multicategory.lean`
- **Theorem/def name:** `multicategoryLoss_zero_or_one`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

