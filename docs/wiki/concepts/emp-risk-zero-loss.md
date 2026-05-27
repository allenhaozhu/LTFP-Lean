# Empirical risk = 0 when all losses are 0

**ID:** `emp-risk-zero-loss`  
**Chapter:** Ch02 (Bach §2.3.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `ERM`

## Statement

_See textbook excerpt below or [`tasks/emp-risk-zero-loss/`](../../../tasks/emp-risk-zero-loss/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Empirical risk = 0 when all losses are 0

**Concept ID:** `emp-risk-zero-loss`
**Chapter:** Ch 2
**Section:** 2.2.2 (Risks)
**Pages:** 27
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

From Definition 2.2 (p. 27):

>     R̂(f) = (1/n) Σ_{i=1}^n ℓ(yi, f(xi)).

If `ℓ(yi, f(xi)) = 0` for all `i ∈ {1, …, n}` (i.e., the predictor `f`
attains zero loss on every training point), then the sum is `0` and
therefore `R̂(f) = 0`.

This is the **"perfect training fit gives zero training error"** statement.

## Proof (verbatim)

Not stated explicitly by Bach; immediate from the average formula.

In Lean: `Finset.sum_eq_zero` (each summand is `0`) + `zero_div`.

## Notes

- Used implicitly in Bach's overfitting discussion (p. 32-34): a sufficiently
  rich model class can drive `R̂(f) → 0` (perfect training fit) while the
  population risk `R(f)` remains bounded away from `R∗`, the classical
  overfitting picture (Figure 2.1, p. 35).
- Trivial discharge in Lean — single `simp` after substituting the all-zero
  hypothesis.

## Prerequisites (Bach's dependency graph)

- [`empirical-risk`](./empirical-risk.md) — Empirical risk R̂_n(f)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch02_SupervisedLearning/ERM.lean`
- **Theorem/def name:** `empiricalRisk_zero_loss`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

