# Inverting a 2×2 matrix

**ID:** `matrix-2x2-inverse`  
**Chapter:** Ch01 (Bach §1.1.2, p. 4)  
**Kind:** lemma  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** `Matrix/LinAlg`

## Statement

_See textbook excerpt below or [`tasks/matrix-2x2-inverse/`](../../../tasks/matrix-2x2-inverse/) if available._

## Bach's textbook treatment

# Book excerpt — `matrix-2x2-inverse` (Bach 2024 §1.1.2, p. 4)

For a 2×2 matrix `A = [[a, b], [c, d]]` with determinant
`det A = a·d − b·c ≠ 0`, the inverse is

    A⁻¹ = (1 / det A) · [[d, −b], [−c, a]],

and `A · A⁻¹ = A⁻¹ · A = I`.

Lean formulation we want:

    theorem matrix_2x2_inverse (A : Matrix (Fin 2) (Fin 2) ℝ) (hdet : A.det ≠ 0) :
      A * A⁻¹ = 1

The proof reuses Mathlib's `Matrix.mul_nonsing_inv`, which states this
fact for any square matrix whose determinant is a unit (use
`isUnit_iff_ne_zero.mpr hdet`).

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch01_Preliminaries/LinAlg.lean`
- **Theorem/def name:** `matrix_2x2_inverse`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

