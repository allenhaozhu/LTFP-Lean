# Operator-monotone / operator-concave functions on Hermitian CFC (L1)

**ID:** `operator-monotone-fn`  
**Chapter:** Ch01 (Bach §1.2.6, p. 19)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** pending  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Concentration`, `Lasso/Sparse`, `Matrix/LinAlg`

## Statement

Node L1 of the B6 decomposition (docs/wiki/B6_DECOMPOSITION_PLAN.md). Predicate `OperatorMonotoneOn` / `OperatorConcaveOn` on intervals, basic stability lemmas (composition, restriction, pointwise limit), Löwner integral representation, and canonical examples (`t ↦ t^p` for `p ∈ [0,1]` op-monotone+op-concave; `Real.log` op-monotone on positives). PR-shaped for Mathlib (`Mathlib/Analysis/CStarAlgebra/OperatorMonotone.lean`), gates `operator-jensen` → `lieb-concavity-joint` → matrix Bernstein.


## Bach's textbook treatment

_No book excerpt available._ See [`tasks/operator-monotone-fn/`](../../../tasks/operator-monotone-fn/) if a context kit has been built, or generate one with `python -m tools.context_kit`.

## Prerequisites (Bach's dependency graph)

- [`matrix-concentration`](./matrix-concentration.md) — Matrix Bernstein / matrix concentration (♦♦)

## Dependents (concepts that use this)

- [`lieb-concavity-joint`](./lieb-concavity-joint.md) — Lieb 1973 joint concavity of `(A,B) ↦ tr(K* A^p K B^q)` (L3)

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `TBD`
- **Theorem/def name:** `OperatorMonotoneOn`
- **Status:** pending
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- **No verified book excerpt** — verify before citing this concept by a textbook equation number; equation labels in synthesized notes can drift relative to the canonical Bach (2024) PDF.

