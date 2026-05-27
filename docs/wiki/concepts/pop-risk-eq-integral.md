# populationRisk = ∫ ℓ ∂D (Mathlib bridge)

**ID:** `pop-risk-eq-integral`  
**Chapter:** Ch02 (Bach §2.2.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** `Ridge`

## Statement

_See textbook excerpt below or [`tasks/pop-risk-eq-integral/`](../../../tasks/pop-risk-eq-integral/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — populationRisk = ∫ ℓ dD (Mathlib bridge)

**Concept ID:** `pop-risk-eq-integral`
**Chapter:** Ch 2
**Section:** 2.2.2 (Risks)
**Pages:** 27
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Definition 2.1 (Expected risk), p. 27, gives the equation **directly**:

>     R(f) = E[ ℓ(y, f(x)) ] = ∫_{X × Y} ℓ(y, f(x)) dp(x, y).

This is the **definitional bridge** between Bach's `E[·]` notation and the
Mathlib `MeasureTheory.integral` (`∫ ·, ∂μ`). The Lean target records this
identity as a definitional unfolding lemma:

    populationRisk ℓ f D = ∫ (xy : X × Y), ℓ xy.2 (f xy.1) ∂D.

Equivalently, after Fubini / disintegration (Bach's preferred form, p. 28):

>     R(f) = E_{x' ∼ p_X}[ r(f(x') | x') ],   where r(z | x') = E[ℓ(y, z) | x = x'].

## Proof (verbatim)

> R(f) = E[ℓ(y, f(x))] = ∫_{X × Y} ℓ(y, f(x)) dp(x, y).  (Definition 2.1, p. 27)

The equality is the very statement of the definition; no separate proof.

## Notes

- This is **the** lemma that ties the Lean `populationRisk` definition to the
  Mathlib integration API. Every measure-theoretic property of population risk
  (linearity in `D`, monotonicity in `ℓ`, dominated-convergence-style limits)
  factors through this bridge.
- Discharge in Lean by `rfl` (after the population-risk definition unfolds to
  `∫`).
- Subtle measurability assumption: `ℓ` and `f` must be jointly measurable so
  that `ℓ ∘ (id × f)` is integrable; Bach silently assumes this (p. 25
  measurability disclaimer).

## Prerequisites (Bach's dependency graph)

- [`population-risk`](./population-risk.md) — Population risk R(f) = E[ℓ(f(x), y)]

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch02_SupervisedLearning/Defs.lean`
- **Theorem/def name:** `populationRisk_eq_integral`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

