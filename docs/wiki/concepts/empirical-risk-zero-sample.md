# Empirical risk on empty sample = 0

**ID:** `empirical-risk-zero-sample`  
**Chapter:** Ch02 (Bach §2.3.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `ERM`

## Statement

_See textbook excerpt below or [`tasks/empirical-risk-zero-sample/`](../../../tasks/empirical-risk-zero-sample/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Empirical risk on empty sample = 0

**Concept ID:** `empirical-risk-zero-sample`
**Chapter:** Ch 2
**Section:** 2.2.2 (definition of empirical risk)
**Pages:** 27
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach defines the empirical risk only for `n ≥ 1` (Definition 2.2, p. 27):

>     R̂(f) = (1/n) Σ_{i=1}^n ℓ(yi, f(xi)).

The `n = 0` case is a **library convention**: an empty sum is `0`, so we
take `R̂_∅(f) = 0` (or, equivalently, leave it undefined and adopt the
extended-real convention `0 / 0 := 0` when normalizing).

The Lean concept `empirical-risk-zero-sample` records this convention as a
definitional lemma: `empiricalRisk ℓ ∅ f = 0`.

## Proof (verbatim)

Not in Bach. The convention follows from
`∑_{i ∈ ∅} _ = 0` (Mathlib `Finset.sum_empty`) and the standard `0 / n` or
`0 * n⁻¹` handling.

In Lean: `simp [empiricalRisk, Finset.sum_empty]`.

## Notes

- Pure library convention; Bach is silent on the empty-sample case.
- Useful as a base case in inductive proofs over sample size (e.g., when
  showing empirical risk is monotone in the sample's loss values).
- The alternative convention `R̂_∅ := undefined` is mathematically valid but
  inconvenient — every Lean lemma about `R̂_n` would need an `n ≥ 1`
  hypothesis. We accept the `0` convention.

## Prerequisites (Bach's dependency graph)

- [`empirical-risk`](./empirical-risk.md) — Empirical risk R̂_n(f)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch02_SupervisedLearning/ERM.lean`
- **Theorem/def name:** `empiricalRisk_zero_sample`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

