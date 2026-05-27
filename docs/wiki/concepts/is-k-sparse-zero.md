# Zero vector is 0-sparse

**ID:** `is-k-sparse-zero`  
**Chapter:** Ch08 (Bach §8.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Lasso/Sparse`

## Statement

_See textbook excerpt below or [`tasks/is-k-sparse-zero/`](../../../tasks/is-k-sparse-zero/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Zero vector is 0-sparse

**Concept ID:** `is-k-sparse-zero`
**Chapter:** Ch 8
**Section:** §8.2 (Variable Selection by the ℓ₀-penalty)
**Pages:** 226
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach does not state `IsKSparse 0 0` as a numbered lemma — it is
immediate from the definition ‖θ‖₀ = |{j : θⱼ ≠ 0}|. For θ = 0
every coordinate is zero, so the support is empty and ‖0‖₀ = 0,
which is ≤ 0; equivalently, the zero vector is 0-sparse.

## Proof (verbatim)

(sketch) — Bach does not give a separate proof. Direct: supp(0) = ∅,
|∅| = 0 ≤ 0, so 0 is 0-sparse.

## Notes

- Trivial boundary lemma.
- Lean target `LTFP/Ch08_Sparse/L0.lean#isKSparse_zero`.
- Bach's proof technique: standard (n/a).

## Prerequisites (Bach's dependency graph)

- [`is-k-sparse`](./is-k-sparse.md) — k-sparsity predicate IsKSparse

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch08_Sparse/L0.lean`
- **Theorem/def name:** `isKSparse_zero`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

