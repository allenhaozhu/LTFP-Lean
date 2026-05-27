# Sketching with the zero matrix annihilates input

**ID:** `sketch-zero-matrix`  
**Chapter:** Ch10 (Bach §F7)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** `Matrix/LinAlg`

## Statement

_See textbook excerpt below or [`tasks/sketch-zero-matrix/`](../../../tasks/sketch-zero-matrix/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Sketching with the zero matrix annihilates input

**Concept ID:** `sketch-zero-matrix`
**Chapter:** Ch 10
**Section:** F7 (algebraic sanity lemma supporting §10.2)
**Pages:** 288-290
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
Algebraic prerequisite of §10.2's sketching framework: when the sketch matrix
`S ∈ ℝˢˣⁿ` is identically zero, every sketched vector vanishes:

    sketch 0 x = 0 · x = 0    for every x.

Bach does not state this as a separate theorem; he relies on it implicitly
throughout the chapter (e.g., page 291 expansion of `S(j)Φ` after splitting
`S(j) = [S₁(j) | S₂(j)]`, where the zero block on `U = [I; 0]` annihilates the
lower component).

## Proof (verbatim)
Definitional. `0 · x = 0` is the standard rule for matrix-vector multiplication
with a zero matrix. In Mathlib this is `Matrix.zero_mulVec`.

## Notes
- Foundation-tier sanity check; required so downstream §10.2 manipulations
  (equations 10.1–10.6) can freely substitute zero sketches without invoking
  Mathlib internals each time.
- Technique in one line: unfold `sketch`, apply `Matrix.zero_mulVec`.
- No ambiguity — purely algebraic.

## Prerequisites (Bach's dependency graph)

- [`random-projection-foundation`](./random-projection-foundation.md) — Random-projection foundation: sketch matrix application

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/RandomProjection.lean`
- **Theorem/def name:** `sketch_zero_matrix`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

