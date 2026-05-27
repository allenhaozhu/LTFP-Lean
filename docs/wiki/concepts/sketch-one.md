# Sketching by identity is identity

**ID:** `sketch-one`  
**Chapter:** Ch10 (Bach §F7)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/sketch-one/`](../../../tasks/sketch-one/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Sketching by identity is identity

**Concept ID:** `sketch-one`
**Chapter:** Ch 10
**Section:** F7 (algebraic sanity lemma supporting §10.2)
**Pages:** 288-290
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
Algebraic sanity lemma: when the sketch matrix is the identity `I ∈ ℝⁿˣⁿ`,
the sketch operation is the identity map:

    sketch I x = I · x = x    for every x ∈ ℝⁿ.

Bach uses this implicitly at the beginning of §10.2.1 (page 290) when
discussing the "single-sketch" case `m = 1` against the unsketched OLS
estimator: setting `S = I` recovers ordinary least-squares.

## Proof (verbatim)
Definitional. `I · x = x` is the standard rule for the identity matrix
acting on a vector. In Mathlib this is `Matrix.one_mulVec`.

## Notes
- Foundation-tier sanity check; required so §10.2 can treat the
  unsketched OLS estimator as the degenerate case of the sketched estimator
  with `S = I`.
- Technique in one line: unfold `sketch`, apply `Matrix.one_mulVec`.
- No ambiguity — purely algebraic.

## Prerequisites (Bach's dependency graph)

- [`random-projection-foundation`](./random-projection-foundation.md) — Random-projection foundation: sketch matrix application

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/RandomProjection.lean`
- **Theorem/def name:** `sketch_one`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

