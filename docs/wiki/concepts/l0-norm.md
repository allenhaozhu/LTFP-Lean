# ℓ₀ 'norm': count of non-zero coordinates

**ID:** `l0-norm`  
**Chapter:** Ch08 (Bach §8.2, p. 226)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/l0-norm/`](../../../tasks/l0-norm/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — ℓ₀ 'norm': count of non-zero coordinates

**Concept ID:** `l0-norm`
**Chapter:** Ch 8
**Section:** §8.1 (Introduction) and §8.2 (Variable Selection by the ℓ₀-penalty)
**Pages:** 221–222, 226
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Verbatim from the chapter summary (p. 221) and §8.1 introduction (p. 222):

> ℓ₀-penalty: For fixed design linear regression, if the optimal predictor has k nonzeros, then we can replace the rate σ²d/n by σ²k log d / n with an ℓ₀-penalty on the square loss (which is computationally hard).

> We will consider two variable selection techniques — namely, the penalization by **‖θ‖₀, which is the number of nonzeros in θ (often miscalled "ℓ₀-norm")**, and the ℓ₁-norm.

And the formal use in §8.2 (p. 226):

> In this section, we assume that the target vector θ\* has at most k nonzero components (i.e., ‖θ\*‖₀ ≤ k). We denote by A = supp(θ\*) the "support" of θ\*; that is, the subset of {1, …, d} composed of j such that (θ\*)ⱼ ≠ 0. We have |A| ≤ k.

## Proof (verbatim)

(definition; not a theorem)

## Notes

- ‖θ‖₀ is **the count of non-zero components** of θ ∈ ℝᵈ. Bach explicitly calls it "often miscalled 'ℓ₀-norm'" — it is not a norm (fails positive homogeneity: ‖2θ‖₀ = ‖θ‖₀ ≠ 2‖θ‖₀).
- Equivalent characterization via support: ‖θ‖₀ = |supp(θ)| = |{j : θⱼ ≠ 0}|.
- The k-sparsity predicate `IsKSparse θ k` corresponds to ‖θ‖₀ ≤ k.
- **Flagged ambiguity:** Bach's text uses the symbol ‖·‖₀ throughout, even though it is not a norm. The Lean formalization (`LTFP/Ch08_Sparse/L0.lean#l0Norm`) may name it `l0Norm` (matching textbook notation) or `l0Count` (emphasizing it is a count); pick one and document.
- Bach's proof technique (n/a): this is a definition introduced as working notation in §8.2.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

- [`is-k-sparse`](./is-k-sparse.md) — k-sparsity predicate IsKSparse

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch08_Sparse/L0.lean`
- **Theorem/def name:** `l0Norm`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

