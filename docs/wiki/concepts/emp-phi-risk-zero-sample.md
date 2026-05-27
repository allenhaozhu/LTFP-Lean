# Empirical Φ-risk vanishes on empty sample

**ID:** `emp-phi-risk-zero-sample`  
**Chapter:** Ch04 (Bach §4.4)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/emp-phi-risk-zero-sample/`](../../../tasks/emp-phi-risk-zero-sample/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Empirical Φ-risk vanishes on empty sample

**Concept ID:** `emp-phi-risk-zero-sample`
**Chapter:** Ch 4
**Section:** 4.4
**Pages:** 85 (definitional consequence)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
For any predictor g and any surrogate Φ, when n = 0 (empty training sample):
$$\hat R_\Phi(g) = \frac{1}{0}\sum_{i=1}^0 \Phi(y_i g(x_i)) := 0.$$

(By the standard convention that the empty sum is 0; the n = 0 case is degenerate but
appears as a base case in inductive arguments.)

## Proof (verbatim)
Bach does not state this as a separate proposition — it is the trivial base case of the
definition R̂_Φ(g) = (1/n) Σ_{i=1}^n Φ(y_i g(x_i)) with the standard empty-sum-equals-zero
convention. In Lean it is a definitional unfolding.

## Notes
- Pure definitional fact (empty sum = 0).
- Useful for base cases of induction on sample size n.
- No mathematical content beyond the convention.

## Prerequisites (Bach's dependency graph)

- [`empirical-phi-risk`](./empirical-phi-risk.md) — Empirical Φ-risk R̂_Φ_n(g) = (1/n) ∑ᵢ Φ(yᵢ · g(xᵢ))

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/RiskDecomposition.lean`
- **Theorem/def name:** `empiricalPhiRisk_zero_sample`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

