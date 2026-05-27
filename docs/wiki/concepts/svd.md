# Singular value decomposition

**ID:** `svd`  
**Chapter:** Ch01 (Bach §1.1.4, p. 6)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** partial  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/svd/`](../../../tasks/svd/) if available._

## Bach's textbook treatment

# Book excerpt — `svd` (Bach 2024 §1.1.4, pp. 6-7)

> Given a rectangular matrix `X ∈ ℝⁿˣᵈ` with `n ≥ d`, there exist an
> orthogonal `V ∈ ℝᵈˣᵈ` (i.e. `VᵀV = VVᵀ = I`), a matrix
> `U ∈ ℝⁿˣᵈ` with orthonormal columns (i.e. `UᵀU = I`), and a vector
> `s ∈ ℝᵈ_+` of nonnegative singular values such that
>
>     X = U · Diag(s) · Vᵀ.
>
> (When `n > d`, `UUᵀ ≠ I` — this is the "economy-size" SVD.) The
> squared singular values `sᵢ²` are the eigenvalues of `XXᵀ` and `XᵀX`.

## Lean target

Mathlib's full SVD coverage is **partial**. Aim for a real, substantive
fact in this neighbourhood that compiles cleanly.

**Preferred (the "singular values squared are real & ≥ 0" half of SVD):**

    theorem svd_exists {n d : ℕ}
        (X : Matrix (Fin n) (Fin d) ℝ) :
        (Xᵀ * X).PosSemidef

One-liner via `Matrix.posSemidef_transpose_mul_self`.

## Acceptable smaller fallback

If the preferred form fights typeclasses, fall back to the symmetry
of the Gram matrix:

    theorem svd_exists {n d : ℕ}
        (X : Matrix (Fin n) (Fin d) ℝ) :
        (Xᵀ * X).IsHermitian

In either case **no `sorry`, no `admit`, no `True`**. Pick whichever
formulation you can land cleanly. Document your choice in the doc-string.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = partial`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch01_Preliminaries/LinAlg.lean`
- **Theorem/def name:** `svd_exists`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

