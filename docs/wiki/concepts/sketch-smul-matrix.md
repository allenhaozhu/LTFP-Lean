# Sketching scales the matrix

**ID:** `sketch-smul-matrix`  
**Chapter:** Ch10 (Bach §F7)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** `Matrix/LinAlg`

## Statement

_See textbook excerpt below or [`tasks/sketch-smul-matrix/`](../../../tasks/sketch-smul-matrix/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Sketching scales the matrix

**Concept ID:** `sketch-smul-matrix`
**Chapter:** Ch 10
**Section:** F7 (algebraic sanity lemma supporting §10.2)
**Pages:** 288-296
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
Algebraic sanity lemma: scalar multiplication commutes with sketching in the
matrix slot:

    sketch (c · Φ) x = c · sketch Φ x.

Bach uses scalar–matrix homogeneity routinely in §10.2 — e.g., when factoring
constants `1/m` (the averaging coefficient across the `m` sketches) out of
the averaged estimator `θ̂ = (1/m) Σ_j θ̂(j)` discussed at the top of
§10.2.1 (page 290) and throughout the bias/variance computations on pages
292–294.

## Proof (verbatim)
Definitional. `(c · Φ) · x = c · (Φ · x)` follows from the bilinearity of
matrix-vector multiplication. In Mathlib this is `Matrix.smul_mulVec_assoc`.

## Notes
- Foundation-tier sanity check; required for `1/m`-averaging and scaling
  arguments in §10.2.1's Gaussian-sketching analysis.
- Technique in one line: unfold `sketch`, apply `Matrix.smul_mulVec_assoc`.
- No ambiguity — purely algebraic.

## Prerequisites (Bach's dependency graph)

- [`random-projection-foundation`](./random-projection-foundation.md) — Random-projection foundation: sketch matrix application

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/RandomProjection.lean`
- **Theorem/def name:** `sketch_smul_matrix`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

