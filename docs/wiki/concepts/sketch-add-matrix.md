# Sketch is linear in matrix

**ID:** `sketch-add-matrix`  
**Chapter:** Ch10 (Bach §F7)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** `Matrix/LinAlg`

## Statement

_See textbook excerpt below or [`tasks/sketch-add-matrix/`](../../../tasks/sketch-add-matrix/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Sketch is linear in matrix

**Concept ID:** `sketch-add-matrix`
**Chapter:** Ch 10
**Section:** F7 (algebraic sanity lemma supporting §10.2)
**Pages:** 288-294
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
Algebraic sanity lemma: the sketch operation is additive in the matrix slot:

    sketch (Φ + Ψ) x = sketch Φ x + sketch Ψ x.

Bach uses linearity in the matrix slot implicitly throughout §10.2 — most
prominently at equation (10.1) (page 292) where he expands

    E_{S(j)} ŷ(j) − Φθ* = Δε + [Δ − I] Φθ*,

decomposing the sketched prediction into separate contributions from `Δ` and
from the bias term `Φθ*`. The decomposition only goes through if sketching is
linear in the matrix argument (here, the design `Φ` is shifted by `−I`).

## Proof (verbatim)
Definitional. `(Φ + Ψ) · x = Φ · x + Ψ · x` is the standard left-distributivity
of matrix-vector multiplication. In Mathlib this is `Matrix.add_mulVec`.

## Notes
- Foundation-tier sanity check; required for the bias/variance decomposition
  on page 292 (equations 10.1, 10.2) to be algebraically clean.
- Technique in one line: unfold `sketch`, apply `Matrix.add_mulVec`.
- No ambiguity — purely algebraic.

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

