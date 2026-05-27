# Bandit gap = μ⋆ - μ a

**ID:** `gap-eq-diff`  
**Chapter:** Ch11 (Bach §11.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Online/Bandits`

## Statement

_See textbook excerpt below or [`tasks/gap-eq-diff/`](../../../tasks/gap-eq-diff/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Gap as difference: Δ(a) = µ⋆ − µ(a)

**Concept ID:** `gap-eq-diff`
**Chapter:** Ch 11
**Section:** §11.3
**Pages:** 332 (book) / PDF p. 348
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Definitional rewrite of `gap` (Bach §11.3, p. 332):

$$\Delta^{(j)} = \max_{i} \mu^{(i)} - \mu^{(j)}.$$

Lean carrier `gap_eq_diff`: `gap μ_star μ a = μ_star - μ a`.

## Proof (verbatim)

Definitional; no proof. Bach writes this as the defining equation. One-line Lean: `rfl` (after unfolding `gap`).

## Notes

- Cosmetic rewrite to expose `gap` as a subtraction; useful for `simp` lemmas and `linarith` invocations.
- Companion to `gap-def` (the abstract definitional alias).
- No content beyond definitional unfolding.

## Prerequisites (Bach's dependency graph)

- [`bandit-gap`](./bandit-gap.md) — Suboptimality gap of an arm

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch11_OnlineBandits/UCB.lean`
- **Theorem/def name:** `gap_eq_diff`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

