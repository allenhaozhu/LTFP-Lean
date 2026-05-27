# Empirical Φ-risk is nonneg under nonneg surrogate

**ID:** `empirical-phi-risk-nonneg`  
**Chapter:** Ch04 (Bach §4.4)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/empirical-phi-risk-nonneg/`](../../../tasks/empirical-phi-risk-nonneg/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Empirical Φ-risk is nonneg under nonneg surrogate

**Concept ID:** `empirical-phi-risk-nonneg`
**Chapter:** Ch 4
**Section:** 4.4
**Pages:** 85-86
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
If Φ : R → R is nonnegative (which is true for square, hinge, logistic, exponential, and
margin-based 0-1), then for any sample {(x_i, y_i)}_{i=1}^n and any score g : X → R,
$$\hat R_\Phi(g) = \frac{1}{n} \sum_{i=1}^n \Phi(y_i g(x_i)) \ge 0.$$

## Proof (verbatim)
Bach uses this implicitly in §4.4 when bounding loss functions in [0, ℓ_∞]: "We assume that
the loss functions for all (x, y) in the support of the data generating distribution and
f ∈ F are between 0 and some ℓ_∞ (for most loss functions, this is a consequence of having
bounded prediction functions)."

(Trivial.) Each summand Φ(y_i g(x_i)) ≥ 0; their sum is ≥ 0; division by n > 0 preserves
non-negativity. □

## Notes
- All four canonical surrogates (square, hinge, logistic, exponential) are non-negative.
- Pedagogical/elementary lemma — base case in Hoeffding-style chain bounds.
- The condition Φ ≥ 0 is also part of the "ℓ_∞-bounded loss" assumption used by Bach in 4.4.1.

## Prerequisites (Bach's dependency graph)

- [`empirical-phi-risk`](./empirical-phi-risk.md) — Empirical Φ-risk R̂_Φ_n(g) = (1/n) ∑ᵢ Φ(yᵢ · g(xᵢ))

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/RiskDecomposition.lean`
- **Theorem/def name:** `empiricalPhiRisk_nonneg`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

