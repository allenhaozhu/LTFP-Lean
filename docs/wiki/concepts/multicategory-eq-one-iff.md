# Multicat loss = 1 iff prediction wrong

**ID:** `multicategory-eq-one-iff`  
**Chapter:** Ch13 (Bach §13.1.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/multicategory-eq-one-iff/`](../../../tasks/multicategory-eq-one-iff/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Multicat loss = 1 iff prediction wrong

**Concept ID:** `multicategory-eq-one-iff`
**Chapter:** Ch 13
**Section:** 13.2 (loss-matrix definition)
**Pages:** 387
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Characterization lemma: `multicategoryLoss y ŷ = 1 ↔ y ≠ ŷ`.

This is the defining identification between the 0-1 loss value and the
disagreement event. Bach gives the loss-matrix form in §13.2 (page 387):

> "The usual 0–1 loss from section 13.1 corresponds to L_{ij} = 1_{i≠j}."

The Iverson-bracket identity `1_{i ≠ j} = 1 ↔ i ≠ j` is the statement
of this lemma. Bach uses this characterization implicitly throughout
Chapter 13 whenever he expresses an expected risk as a probability of
misclassification — e.g. on page 380:

> "the Bayes predictor for the 0–1 loss, equal to arg max_{z∈{1,...,k}}
> P(y = z|x)."

The Bayes risk for the 0-1 loss is `E[multicategoryLoss y f(x)]
= P(y ≠ f(x))`; this identification only works because
`multicategoryLoss y f(x) = 1_{y ≠ f(x)}` precisely when prediction is
wrong (this lemma) and `0` otherwise (see `multicat-loss-diag`).

## Proof (verbatim)
Definitional. `multicategoryLoss y ŷ = if y = ŷ then 0 else 1`. The
value equals `1` exactly in the "else" branch, i.e. exactly when
`y ≠ ŷ`. Forward: if the value is `1`, the "then" branch (value `0`)
is excluded by `0 ≠ 1`, forcing `y ≠ ŷ`. Backward: if `y ≠ ŷ`, the
`if`-test is false, so the value is `1`.

## Notes
- Bridges the algebraic definition (`multicategoryLoss`) and the
  probabilistic interpretation (`P(y ≠ f(x))`) used in Bayes-risk
  derivations.
- Technique in one line: case-split on `y = ŷ`, decide both directions
  of the iff.
- No ambiguity — purely the iff form of the indicator definition.

## Prerequisites (Bach's dependency graph)

- [`multicategory-loss`](./multicategory-loss.md) — Multicategory 0-1 loss for k classes

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch13_StructuredPrediction/Multicategory.lean`
- **Theorem/def name:** `multicategoryLoss_eq_one_iff`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

