# Estimation error of fhat against itself = 0

**ID:** `estim-error-self-anchor`  
**Chapter:** Ch04 (Bach §4.4)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/estim-error-self-anchor/`](../../../tasks/estim-error-self-anchor/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Estimation error of fhat against itself = 0

**Concept ID:** `estim-error-self-anchor`
**Chapter:** Ch 4
**Section:** 4.4 (consequence of (4.10))
**Pages:** 85-86
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
When measuring the estimation error of a predictor f̂ against itself, the result is zero:
$$R(\hat f) - R(\hat f) = 0.$$

More generally, the estimation-error decomposition trivializes when the comparison
predictor equals f̂. This is the trivial self-anchor base case.

## Proof (verbatim)
Trivial reflexivity of subtraction.

In Bach's decomposition (4.10):
"R(f̂) − inf_{f ∈ F} R(f) = R(f̂) − R(g_F)" — replacing g_F by f̂ gives 0.

## Notes
- Trivial reflexivity lemma.
- Used as a base case in inductive estimation-error arguments.
- Lean: `theorem estim_self : R_hat - R_hat = 0 := sub_self _`.

## Prerequisites (Bach's dependency graph)

- [`estimation-error`](./estimation-error.md) — Estimation error: predictor risk − best-in-class risk

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/RiskDecomposition.lean`
- **Theorem/def name:** `estimationError_self_anchor`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

