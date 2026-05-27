# Empirical Φ-risk R̂_Φ_n(g) = (1/n) ∑ᵢ Φ(yᵢ · g(xᵢ))

**ID:** `empirical-phi-risk`  
**Chapter:** Ch04 (Bach §4.4, p. 90)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/empirical-phi-risk/`](../../../tasks/empirical-phi-risk/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Empirical Φ-risk

**Concept ID:** `empirical-phi-risk`
**Chapter:** Ch 4
**Section:** 4.4 (also 4.1.1)
**Pages:** 73, 85-86, 90
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
For a real-valued score function g : X → R, a convex surrogate Φ : R → R, and i.i.d. data
{(x_i, y_i)}_{i=1}^n with y_i ∈ {−1, 1}, the empirical Φ-risk is

$$\hat R_\Phi(g) = \frac{1}{n}\sum_{i=1}^n \Phi\big(y_i \, g(x_i)\big).$$

This is the natural sample analog of the population Φ-risk R_Φ(g) = E[Φ(y g(x))].

Bach formulates the surrogate ERM problem as
$$\hat g_n \in \arg\min_{g \in F} \frac{1}{n}\sum_{i=1}^n \Phi(y_i g(x_i)),$$
"for empirical risk minimization, we then minimize with respect to the function g : X → R
the corresponding empirical risk (1/n) Σ_{i=1}^n Φ_{0-1}(y_i g(x_i))."

## Proof (verbatim)
(Definition — no proof.)

## Notes
- Sum over the training sample of Φ applied to the margin y_i g(x_i).
- Bach uses the overloaded notation R̂(g) for empirical Φ-risk when Φ is fixed (chapter 4 standard).
- For y_i ∈ {−1, 1} and Φ_square: equals (1/n) Σ (y_i − g(x_i))² (LDA/linear-regression view).
- Empirical Φ-risk vanishes on empty sample (n = 0); non-negative under Φ ≥ 0; …
  (these are the satellite lemmas in the chapter-4 ledger).

## Prerequisites (Bach's dependency graph)

- [`phi-hinge`](./phi-hinge.md) — Hinge surrogate Φ(u) = max(1-u, 0) — yields SVM

## Dependents (concepts that use this)

- [`emp-phi-risk-zero-sample`](./emp-phi-risk-zero-sample.md) — Empirical Φ-risk vanishes on empty sample
- [`empirical-phi-risk-nonneg`](./empirical-phi-risk-nonneg.md) — Empirical Φ-risk is nonneg under nonneg surrogate

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/RiskDecomposition.lean`
- **Theorem/def name:** `empiricalPhiRisk`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

