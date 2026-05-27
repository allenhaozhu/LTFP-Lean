# k-sparsity predicate IsKSparse

**ID:** `is-k-sparse`  
**Chapter:** Ch08 (Bach §8.2)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Lasso/Sparse`

## Statement

_See textbook excerpt below or [`tasks/is-k-sparse/`](../../../tasks/is-k-sparse/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — k-sparsity predicate IsKSparse

**Concept ID:** `is-k-sparse`
**Chapter:** Ch 8
**Section:** §8.2 (Variable Selection by the ℓ₀-penalty)
**Pages:** 226 (also chapter summary, p. 221)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Verbatim from §8.2 (p. 226):

> In this section, we assume that the target vector θ\* has at most k nonzero components (i.e., ‖θ\*‖₀ ≤ k). We denote by A = supp(θ\*) the "support" of θ\*; that is, the subset of {1, …, d} composed of j such that (θ\*)ⱼ ≠ 0. We have |A| ≤ k.

The chapter summary (p. 221) frames the same notion:

> ℓ₀-penalty: For fixed design linear regression, **if the optimal predictor has k nonzeros**, then we can replace the rate σ²d/n by σ²k log d / n …

So `IsKSparse θ k` means ‖θ‖₀ ≤ k, equivalently |supp(θ)| ≤ k, equivalently
"at most k coordinates of θ are nonzero".

## Proof (verbatim)

(definition; not a theorem)

## Notes

- The predicate `IsKSparse θ k` corresponds exactly to Bach's
  hypothesis "‖θ\*‖₀ ≤ k" used throughout §8.2 and §8.3.
- Equivalent characterizations: |supp(θ)| ≤ k; or there exists
  A ⊂ {1,…,d} with |A| ≤ k such that supp(θ) ⊂ A.
- This is the working hypothesis of every k-sparse generalization
  bound in the chapter (Propositions 8.1, 8.2, 8.4).
- Lean target `LTFP/Ch08_Sparse/L0.lean#IsKSparse`.
- Bach's proof technique: n/a (definition).
- **Flagged ambiguity:** Bach uses both "k nonzeros" and "at most
  k nonzeros". The predicate `IsKSparse` should encode "at most k"
  (i.e., ‖θ‖₀ ≤ k, not ‖θ‖₀ = k) to match Bach's usage in §8.2 ("‖θ\*‖₀ ≤ k").

## Prerequisites (Bach's dependency graph)

- [`l0-norm`](./l0-norm.md) — ℓ₀ 'norm': count of non-zero coordinates

## Dependents (concepts that use this)

- [`is-k-sparse-dim`](./is-k-sparse-dim.md) — Every vector is d-sparse (trivial upper bound)
- [`is-k-sparse-mono`](./is-k-sparse-mono.md) — k-sparsity is monotone in k
- [`is-k-sparse-succ`](./is-k-sparse-succ.md) — k-sparsity then (k+1)-sparsity
- [`is-k-sparse-zero`](./is-k-sparse-zero.md) — Zero vector is 0-sparse
- [`is-k-sparse-zero-any`](./is-k-sparse-zero-any.md) — Zero vector is k-sparse for any k

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch08_Sparse/L0.lean`
- **Theorem/def name:** `IsKSparse`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

