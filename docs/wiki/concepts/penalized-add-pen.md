# Penalized risk additive in penalty

**ID:** `penalized-add-pen`  
**Chapter:** Ch04 (Bach §4.6.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/penalized-add-pen/`](../../../tasks/penalized-add-pen/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Penalized risk additive in penalty

**Concept ID:** `penalized-add-pen`
**Chapter:** Ch 4
**Section:** 4.6.1 / 4.5.5
**Pages:** 100, 103-104
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
The penalized risk is linear in the additive penalty:
$$\hat R_{\Omega_1 + \Omega_2}(\theta) = \hat R(\theta) + (\Omega_1(\theta) + \Omega_2(\theta)) = \hat R_{\Omega_1}(\theta) + \Omega_2(\theta).$$

Equivalently, with λ-weight notation:
$$\hat R(\theta) + \lambda_1 \Omega_1(\theta) + \lambda_2 \Omega_2(\theta) = \big(\hat R(\theta) + \lambda_1 \Omega_1(\theta)\big) + \lambda_2 \Omega_2(\theta).$$

## Proof (verbatim)
(Trivial by definition (4.17), (4.19).)

## Notes
- Trivial algebraic identity: addition is associative/commutative.
- Pedagogical / structural lemma.
- Useful when manipulating multi-penalty objective functions (e.g., elastic net).

## Prerequisites (Bach's dependency graph)

- [`penalized-empirical-risk`](./penalized-empirical-risk.md) — Penalized empirical risk for SRM (♦)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/ModelSelection.lean`
- **Theorem/def name:** `penalizedEmpiricalRisk_add_pen`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

