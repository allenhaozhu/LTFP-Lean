# Loss function ℓ : 𝒴 × 𝒴 → ℝ

**ID:** `loss-function`  
**Chapter:** Ch02 (Bach §2.2.1, p. 25)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/loss-function/`](../../../tasks/loss-function/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Loss function ℓ : 𝒴 × 𝒴 → ℝ

**Concept ID:** `loss-function`
**Chapter:** Ch 2
**Section:** 2.2.1 (Supervised Learning Problems and Loss Functions)
**Pages:** 25-26
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

From §2.2.1 (p. 25):

> We consider a loss function `ℓ : Y × Y → R` (often `R+`), where `ℓ(y, z)` is the loss
> of predicting `z` while the true label is `y`.

Bach immediately notes (p. 26):

> Some authors swap `y` and `z` in the definition of the loss.
> [...] The loss function only concerns the output space `Y` independent of the input space `X`.

Main examples Bach enumerates:
- **Binary classification** (`Y = {0,1}` or `{-1,1}`): 0–1 loss `ℓ(y, z) = 1_{y ≠ z}`.
- **Multicategory classification** (`Y = {1, …, k}`): also 0–1 loss `ℓ(y, z) = 1_{y ≠ z}`.
- **Regression** (`Y = R`): square loss `ℓ(y, z) = (y − z)²`; absolute loss `|y − z|` for robust estimation.
- **Structured prediction** (e.g. `Y = {0,1}^k`): Hamming loss `Σ_j 1_{y_j ≠ z_j}`.

## Proof (verbatim)

(Not a proposition — this is a definition.) No proof; Bach treats the loss
function as **given data** of the problem (p. 26):

> Throughout this textbook, we will assume that the loss function is given to us.

## Notes

- Convention: Bach writes `ℓ(y, z)` with truth `y` first and prediction `z` second. (Some
  authors reverse this — flagged ambiguity.)
- The codomain is **`R`** in full generality, but Bach notes "often `R+`" — i.e., the
  most common case is nonneg-valued losses. This is the basis for many later monotonicity
  / nonnegativity results.
- Lean target is the **type** `Y → Y → ℝ`; structural properties (nonnegativity,
  symmetry, vanishing-on-diagonal) are recorded per loss as separate lemmas.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

- [`empirical-risk`](./empirical-risk.md) — Empirical risk R̂_n(f)
- [`population-risk`](./population-risk.md) — Population risk R(f) = E[ℓ(f(x), y)]
- [`square-loss`](./square-loss.md) — Squared loss ℓ(z, y) = (z − y)²

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch02_SupervisedLearning/Defs.lean`
- **Theorem/def name:** `LossFunction`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

