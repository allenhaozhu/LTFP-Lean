# Zero vector is k-sparse for any k

**ID:** `is-k-sparse-zero-any`  
**Chapter:** Ch08 (Bach §8.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Lasso/Sparse`

## Statement

_See textbook excerpt below or [`tasks/is-k-sparse-zero-any/`](../../../tasks/is-k-sparse-zero-any/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Zero vector is k-sparse for any k

**Concept ID:** `is-k-sparse-zero-any`
**Chapter:** Ch 8
**Section:** §8.2 (Variable Selection by the ℓ₀-penalty)
**Pages:** 226
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach does not state "0 is k-sparse for every k" as a numbered lemma —
it is immediate from `is-k-sparse-zero` (0 is 0-sparse) plus
`is-k-sparse-mono` (0 ≤ k for every k ∈ ℕ), or directly from
‖0‖₀ = 0 ≤ k.

## Proof (verbatim)

(sketch) — Bach does not give a separate proof. One-liner:
‖0‖₀ = 0 ≤ k for every k ∈ ℕ, so 0 is k-sparse.

## Notes

- Convenience extension of `is-k-sparse-zero` to arbitrary k.
- Lean target `LTFP/Ch08_Sparse/L0.lean#isKSparse_zero_any`.
- Bach's proof technique: standard (n/a).

## Prerequisites (Bach's dependency graph)

- [`is-k-sparse`](./is-k-sparse.md) — k-sparsity predicate IsKSparse

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch08_Sparse/L0.lean`
- **Theorem/def name:** `isKSparse_zero_any`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

