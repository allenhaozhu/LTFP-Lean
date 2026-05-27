# Every vector is d-sparse (trivial upper bound)

**ID:** `is-k-sparse-dim`  
**Chapter:** Ch08 (Bach §8.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Lasso/Sparse`

## Statement

_See textbook excerpt below or [`tasks/is-k-sparse-dim/`](../../../tasks/is-k-sparse-dim/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Every vector is d-sparse (trivial upper bound)

**Concept ID:** `is-k-sparse-dim`
**Chapter:** Ch 8
**Section:** §8.2 (Variable Selection by the ℓ₀-penalty)
**Pages:** 226 (also a remark on p. 227)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach does not state "every θ ∈ ℝᵈ is d-sparse" as a numbered lemma,
but the fact is implicit: the support supp(θ) ⊂ {1,…,d} always has
cardinality ≤ d, so ‖θ‖₀ ≤ d for every θ.

Bach uses this trivial bound when commenting on the regime k ≥ d/2
(p. 227, observations after Proposition 8.1):

> The assumption that k < d/2 is not a real issue, as when k ≥ d/2, then the classical bound σ²d/n is of the same order as σ²k log(d/k)/n.

Here Bach implicitly invokes ‖θ\*‖₀ ≤ d to fall back on the dense
OLS bound.

## Proof (verbatim)

(sketch) — Bach does not give a separate proof. Direct:
supp(θ) ⊂ {1,…,d} ⇒ |supp(θ)| ≤ d ⇒ ‖θ‖₀ ≤ d, so θ is d-sparse.

## Notes

- Trivial upper bound; the "do-nothing" sparsity assumption.
- Lean target `LTFP/Ch08_Sparse/L0.lean#isKSparse_dim`.
- Used implicitly to handle edge cases where the sparsity level
  exceeds the ambient dimension.
- Bach's proof technique: standard (n/a).

## Prerequisites (Bach's dependency graph)

- [`is-k-sparse`](./is-k-sparse.md) — k-sparsity predicate IsKSparse

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch08_Sparse/L0.lean`
- **Theorem/def name:** `isKSparse_dim`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

