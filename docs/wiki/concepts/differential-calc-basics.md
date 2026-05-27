# Gradient, Hessian, chain rule

**ID:** `differential-calc-basics`  
**Chapter:** Ch01 (Bach §1.1.5, p. 7)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/differential-calc-basics/`](../../../tasks/differential-calc-basics/) if available._

## Bach's textbook treatment

# Book excerpt — `differential-calc-basics` (Bach 2024 §1.1.5, p. 7)

§1.1.5 introduces the standard differential-calculus toolkit used
throughout the book: gradient `∇f : ℝᵈ → ℝᵈ`, Hessian `∇²f`,
chain rule, and the basic identity `∇(½ ‖x − a‖²) = x − a`.

For LTFP we just need a stable *anchor* symbol for downstream chapters
to import. The cleanest choice is to package the gradient identity
above as a one-line theorem reusing Mathlib:

    theorem gradient_basics (a : EuclideanSpace ℝ (Fin d)) :
        ∀ x, gradient (fun x => (1/2) * ‖x - a‖^2) x = x - a

If proving the gradient identity end-to-end turns out to be unwieldy
inside Mathlib's `gradient` API, an acceptable alternative is to
state a much smaller fact (e.g., a sanity check on the gradient of
a constant function) and leave the full identity for a follow-up
ticket. Pick whichever is easier to land cleanly with NO `sorry`.

Either way the theorem must be a real proven statement, not
`True := trivial`.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch01_Preliminaries/DiffCalc.lean`
- **Theorem/def name:** `gradient_basics`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

