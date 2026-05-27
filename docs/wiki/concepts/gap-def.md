# Bandit gap definitional

**ID:** `gap-def`  
**Chapter:** Ch11 (Bach §11.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Online/Bandits`

## Statement

_See textbook excerpt below or [`tasks/gap-def/`](../../../tasks/gap-def/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Gap definitional equality

**Concept ID:** `gap-def`
**Chapter:** Ch 11
**Section:** §11.3
**Pages:** 332 (book) / PDF p. 348
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

The definitional alias for `gap`. From Bach §11.3, p. 332:

$$\Delta^{(j)} = \max_i \mu^{(i)} - \mu^{(j)}.$$

Lean carrier `gap_def`: `gap μ_star μ a = μ_star - μ a` (definitional `rfl` lemma exposing the underlying subtraction).

## Proof (verbatim)

Bach defers; this is the definition itself. One-line Lean: `rfl`.

## Notes

- Pure cosmetic lemma; same content as `gap-eq-diff` but exposed as a `@[simp]` candidate for definitional unfolding.
- No mathematical content beyond unfolding the abstract `gap` constructor.

## Prerequisites (Bach's dependency graph)

- [`bandit-gap`](./bandit-gap.md) — Suboptimality gap of an arm

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch11_OnlineBandits/UCB.lean`
- **Theorem/def name:** `gap_def`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

