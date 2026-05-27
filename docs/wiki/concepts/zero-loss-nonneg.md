# Zero loss is nonneg

**ID:** `zero-loss-nonneg`  
**Chapter:** Ch02 (Bach §2.2.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/zero-loss-nonneg/`](../../../tasks/zero-loss-nonneg/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Zero loss is nonneg

**Concept ID:** `zero-loss-nonneg`
**Chapter:** Ch 2
**Section:** 2.2.1 (loss-function framing)
**Pages:** 25
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For the constant-zero loss `ℓ(y, z) = 0`, the nonnegativity statement
`ℓ(y, z) ≥ 0` reduces to the trivial fact `0 ≥ 0`.

This is consistent with Bach's framing that losses typically take values in
`R+` (§2.2.1, p. 25):

> We consider a loss function `ℓ : Y × Y → R` (often `R+`) [...]

## Proof (verbatim)

(Trivial — `0 ≤ 0` by reflexivity.)

In Lean: `le_refl 0` or `Eq.le rfl`.

## Notes

- Pairs with `zero-loss`; together they confirm the trivial loss is a member
  of the "nonneg-valued loss" subtype.
- Smoke-test lemma.

## Prerequisites (Bach's dependency graph)

- [`zero-loss`](./zero-loss.md) — Zero loss function

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch02_SupervisedLearning/Defs.lean`
- **Theorem/def name:** `zeroLoss_nonneg`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

