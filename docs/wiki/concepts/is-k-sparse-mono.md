# k-sparsity is monotone in k

**ID:** `is-k-sparse-mono`  
**Chapter:** Ch08 (Bach §8.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Lasso/Sparse`

## Statement

_See textbook excerpt below or [`tasks/is-k-sparse-mono/`](../../../tasks/is-k-sparse-mono/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — k-sparsity is monotone in k

**Concept ID:** `is-k-sparse-mono`
**Chapter:** Ch 8
**Section:** §8.2 (Variable Selection by the ℓ₀-penalty)
**Pages:** 226
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach does not state monotonicity (‖θ‖₀ ≤ k ∧ k ≤ k' ⇒ ‖θ‖₀ ≤ k')
as a numbered lemma — it is immediate from transitivity of ≤ on ℕ.

The property is used implicitly when Bach widens sparsity hypotheses
(e.g., in the proof of Proposition 8.1, p. 226: "for any θ such that
‖θ‖₀ ≤ k, we have ‖θ − θ\*‖₀ ≤ 2k").

## Proof (verbatim)

(sketch) — Bach does not give a separate proof. One-liner:
if ‖θ‖₀ ≤ k and k ≤ k', then by transitivity ‖θ‖₀ ≤ k', so θ is
k'-sparse.

## Notes

- Trivial monotonicity lemma.
- Lean target `LTFP/Ch08_Sparse/L0.lean#IsKSparse.mono`.
- Bach's proof technique: standard (transitivity of ≤).

## Prerequisites (Bach's dependency graph)

- [`is-k-sparse`](./is-k-sparse.md) — k-sparsity predicate IsKSparse

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch08_Sparse/L0.lean`
- **Theorem/def name:** `IsKSparse.mono`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

