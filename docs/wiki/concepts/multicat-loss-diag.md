# multicategoryLoss y y = 0

**ID:** `multicat-loss-diag`  
**Chapter:** Ch13 (Bach §13.1.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/multicat-loss-diag/`](../../../tasks/multicat-loss-diag/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — multicategoryLoss y y = 0

**Concept ID:** `multicat-loss-diag`
**Chapter:** Ch 13
**Section:** 13.2 (loss-matrix definition)
**Pages:** 387
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Sanity lemma: `multicategoryLoss y y = 0` for every label `y`. The
diagonal of the loss matrix vanishes for the 0-1 loss.

Bach does not state this as a numbered proposition — it is the trivial
diagonal of the 0-1 loss matrix in §13.2 (page 387):

> "The usual 0–1 loss from section 13.1 corresponds to L_{ij} = 1_{i≠j}."

Substituting `i = j` gives `L_{ii} = 1_{i ≠ i} = 0`. Bach also relies on
this implicitly in §13.5 (page 398), where the structured-SVM construction
subtracts `ℓ(y, y)` from the margin constraint precisely because it is
zero for "honest" losses (i.e., losses minimized at the diagonal):

> "we assume that for any z ∈ Y, y ↦ ℓ(y, z) is minimized at z."

For the 0-1 loss the minimum equals zero exactly, so the `ℓ(y, y)` term
drops out of `S(y, h(x, ·))` entirely.

## Proof (verbatim)
Definitional. `multicategoryLoss y y = if y = y then 0 else 1 = 0`.

## Notes
- Lets the structured-SVM surrogate (equation 13.12, page 399) simplify
  whenever the label-pair coincides.
- Technique in one line: `if true then 0 else _ = 0` via `Eq.refl`.
- No ambiguity. This vanishing is *specific* to losses minimized at the
  diagonal — Bach uses the assumption explicitly in §13.5 (page 398).

## Prerequisites (Bach's dependency graph)

- [`multicategory-loss`](./multicategory-loss.md) — Multicategory 0-1 loss for k classes

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch13_StructuredPrediction/Multicategory.lean`
- **Theorem/def name:** `multicategoryLoss_diag`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

