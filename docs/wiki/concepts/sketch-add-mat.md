# Sketching is linear in matrix

**ID:** `sketch-add-mat`  
**Chapter:** Ch10 (Bach §F7)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** `Matrix/LinAlg`

## Statement

_See textbook excerpt below or [`tasks/sketch-add-mat/`](../../../tasks/sketch-add-mat/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Sketching is linear in matrix (alias of sketch-add-matrix)

**Concept ID:** `sketch-add-mat`
**Chapter:** Ch 10
**Section:** F7 (algebraic sanity lemma supporting §10.2)
**Pages:** 288-294
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
Identical statement to `sketch-add-matrix` (it shares the same Lean target
`LTFP/Foundations/RandomProjection.lean#sketch_add_matrix`). Registered as a
second concept ID for cross-referencing convenience inside Chapter 10
discussions:

    sketch (Φ + Ψ) x = sketch Φ x + sketch Ψ x.

See `sketch-add-matrix/book_excerpt.md` for the Bach reference (equation 10.1,
page 292, expansion of the sketched prediction into matrix-additive pieces).

## Proof (verbatim)
Definitional — left-distributivity of matrix-vector multiplication, i.e.,
Mathlib's `Matrix.add_mulVec`.

## Notes
- Duplicate registry entry; same proof obligation as `sketch-add-matrix`.
- Technique in one line: unfold `sketch`, apply `Matrix.add_mulVec`.
- Ambiguity: registry has two IDs (`sketch-add-mat` and `sketch-add-matrix`)
  both pointing at the same Lean theorem. Treat them as aliases.

## Prerequisites (Bach's dependency graph)

- [`random-projection-foundation`](./random-projection-foundation.md) — Random-projection foundation: sketch matrix application

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/RandomProjection.lean`
- **Theorem/def name:** `sketch_add_matrix`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

