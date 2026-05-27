# k-sparsity then (k+1)-sparsity

**ID:** `is-k-sparse-succ`  
**Chapter:** Ch08 (Bach §8.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Lasso/Sparse`

## Statement

_See textbook excerpt below or [`tasks/is-k-sparse-succ/`](../../../tasks/is-k-sparse-succ/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — k-sparsity then (k+1)-sparsity

**Concept ID:** `is-k-sparse-succ`
**Chapter:** Ch 8
**Section:** §8.2 (Variable Selection by the ℓ₀-penalty)
**Pages:** 226
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach does not state "k-sparse ⇒ (k+1)-sparse" as a numbered lemma —
it is a special case of `is-k-sparse-mono` with k' = k + 1, using
k ≤ k + 1.

The property is the +1 step instance of the general monotonicity:
if ‖θ‖₀ ≤ k, then ‖θ‖₀ ≤ k + 1 trivially.

## Proof (verbatim)

(sketch) — Bach does not give a separate proof. One-liner:
‖θ‖₀ ≤ k ≤ k + 1, so θ is (k + 1)-sparse.

## Notes

- Trivial successor step of `is-k-sparse-mono`.
- Lean target `LTFP/Ch08_Sparse/L0.lean#isKSparse_succ_of_kSparse`.
- Used for inductive arguments on sparsity level.
- Bach's proof technique: standard (n/a).

## Prerequisites (Bach's dependency graph)

- [`is-k-sparse`](./is-k-sparse.md) — k-sparsity predicate IsKSparse

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch08_Sparse/L0.lean`
- **Theorem/def name:** `isKSparse_succ_of_kSparse`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

