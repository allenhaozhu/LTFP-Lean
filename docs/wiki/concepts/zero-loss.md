# Zero loss function

**ID:** `zero-loss`  
**Chapter:** Ch02 (Bach §2.2.1)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/zero-loss/`](../../../tasks/zero-loss/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Zero loss function

**Concept ID:** `zero-loss`
**Chapter:** Ch 2
**Section:** 2.2.1
**Pages:** 25
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach does not introduce a "zero loss" as one of the canonical losses. The
`zero-loss` concept is a **library-internal trivial instance** — the constant
function `ℓ(y, z) = 0` for all `y, z` — used to populate the loss-function
typeclass interface with a guaranteed-existing example.

The closest textbook anchor is the loss-function definition itself (§2.2.1,
p. 25):

> We consider a loss function `ℓ : Y × Y → R` (often `R+`), where `ℓ(y, z)` is
> the loss of predicting `z` while the true label is `y`.

The zero function `λ y z, 0` is a (degenerate) member of this type.

## Proof (verbatim)

(Definition — no proof.) Bach never introduces or uses this loss; it is a
Lean-library convenience.

## Notes

- Degenerate: every prediction has zero loss, so every predictor is a Bayes
  predictor and `R∗ = 0`.
- Used in Lean as a **smoke-test instance** for the loss-function API
  (e.g., verifying that nonneg-loss machinery doesn't break on the trivial
  case).
- Pairs with `zero-loss-nonneg` (the trivial nonnegativity statement).

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

- [`zero-loss-nonneg`](./zero-loss-nonneg.md) — Zero loss is nonneg

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch02_SupervisedLearning/Defs.lean`
- **Theorem/def name:** `zeroLoss`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

