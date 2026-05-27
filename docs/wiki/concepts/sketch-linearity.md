# Random projection sketch is linear in input

**ID:** `sketch-linearity`  
**Chapter:** Ch10 (Bach §10.2, p. 290)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/sketch-linearity/`](../../../tasks/sketch-linearity/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Random projection sketch is linear in input

**Concept ID:** `sketch-linearity`
**Chapter:** Ch 10
**Section:** 10.2 "Random Projections and Averaging"
**Pages:** 290
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
Section 10.2 (page 290) defines the sketched least-squares estimator
implicitly through the closed form

    θ̂(j) = (Φᵀ (S(j))ᵀ S(j) Φ)⁻¹ Φᵀ (S(j))ᵀ S(j) y,

and uses the linearity of `S` (and hence of `S(j)Φ` and `S(j)y`) in the input
vector throughout the derivation of equations (10.1)–(10.6). The sketch
operation `x ↦ Sx` is a linear map ℝⁿ → ℝˢ, so in particular

    sketch S (x + y) = sketch S x + sketch S y.

## Proof (verbatim)
Definitional. Matrix-vector multiplication is left-linear in its second
argument:

    S · (x + y) = Sx + Sy.

In Mathlib this is `Matrix.mulVec_add`.

## Notes
- Used in the page-291–294 derivations: every time the noise vector `ε` and
  the bias term `Φθ*` are sketched separately and then re-added, additivity
  in the input slot is invoked.
- Technique in one line: unfold `sketch`, apply `Matrix.mulVec_add`.
- No ambiguity — purely algebraic. The page-290 declaration ("we consider
  s ≥ d Gaussian random projections, with typically s ≤ n") fixes the
  shapes; linearity holds for arbitrary `S`, not only Gaussian.

## Prerequisites (Bach's dependency graph)

- [`random-projection-foundation`](./random-projection-foundation.md) — Random-projection foundation: sketch matrix application

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch10_Ensemble/RandomProjections.lean`
- **Theorem/def name:** `sketch_add`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

