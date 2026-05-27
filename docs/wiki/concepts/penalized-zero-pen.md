# Penalized risk with zero penalty = empirical risk

**ID:** `penalized-zero-pen`  
**Chapter:** Ch04 (Bach §4.6.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `ERM`

## Statement

_See textbook excerpt below or [`tasks/penalized-zero-pen/`](../../../tasks/penalized-zero-pen/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Penalized risk with zero penalty = empirical risk

**Concept ID:** `penalized-zero-pen`
**Chapter:** Ch 4
**Section:** 4.6.1 / 4.5.5
**Pages:** 100, 103-104
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
When the regularization parameter is zero (λ = 0), or when the penalty Ω(θ) = 0 identically,
the penalized empirical risk reduces to the unpenalized one:
$$\hat R_0(\theta) = \hat R(\theta) + 0 \cdot \Omega(\theta) = \hat R(\theta).$$

## Proof (verbatim)
(Trivial by definition of R̂_λ(θ) = R̂(θ) + λ Ω(θ) in (4.17) and (4.19).)

## Notes
- Trivial unfolding.
- Useful as a base case when arguing about regularization paths.
- The "no regularization" limit recovers vanilla ERM.

## Prerequisites (Bach's dependency graph)

- [`penalized-empirical-risk`](./penalized-empirical-risk.md) — Penalized empirical risk for SRM (♦)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/ModelSelection.lean`
- **Theorem/def name:** `penalizedEmpiricalRisk_zero_pen`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

