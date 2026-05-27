# Multicategory loss is symmetric

**ID:** `multicategory-loss-symm`  
**Chapter:** Ch13 (Bach §13.1.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/multicategory-loss-symm/`](../../../tasks/multicategory-loss-symm/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Multicategory loss is symmetric

**Concept ID:** `multicategory-loss-symm`
**Chapter:** Ch 13
**Section:** 13.2 (loss-matrix definition)
**Pages:** 387
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Sanity lemma: `multicategoryLoss y₁ y₂ = multicategoryLoss y₂ y₁`.

Bach does not state this symmetry as a numbered proposition — it is a
direct algebraic consequence of the loss-matrix form he gives in §13.2
(page 387):

> "Multicategory classification: Y = {1, . . . , k} and a loss matrix
> L ∈ R^{k×k}, with ℓ(i, j) = L_{ij}. The usual 0–1 loss from section 13.1
> corresponds to L_{ij} = 1_{i≠j}, but in most applications, errors do not
> have the same cost (e.g., in spam prediction, classifying a legitimate
> email as spam costs much more than the opposite)."

The 0-1 loss matrix `L_{ij} = 1_{i ≠ j}` is symmetric because `i ≠ j ↔
j ≠ i`. Bach himself notes (in the same paragraph) that the *general*
loss matrix need NOT be symmetric — this is the spam example. So the
symmetry is *specific* to the 0-1 loss, not inherited from the structured
prediction framework.

## Proof (verbatim)
Definitional. From `1_{i ≠ j} = 1_{j ≠ i}`, or in Lean's `if-then-else`
form, `(if y₁ = y₂ then 0 else 1) = (if y₂ = y₁ then 0 else 1)` by
`Eq.comm` on the test.

## Notes
- Trivial; included so that downstream symmetric proofs (e.g., for
  symmetric Rademacher-style bounds) can rewrite either argument.
- Technique in one line: rewrite `y₁ = y₂ ↔ y₂ = y₁`.
- No ambiguity. Specific to the 0-1 loss; cost-sensitive variants
  (Bach's "spam" example, page 387) are explicitly NOT symmetric.

## Prerequisites (Bach's dependency graph)

- [`multicategory-loss`](./multicategory-loss.md) — Multicategory 0-1 loss for k classes

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch13_StructuredPrediction/Multicategory.lean`
- **Theorem/def name:** `multicategoryLoss_symm`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

