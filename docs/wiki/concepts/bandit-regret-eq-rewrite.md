# Bandit regret = T·μ⋆ − ∑t μ_{a_t}

**ID:** `bandit-regret-eq-rewrite`  
**Chapter:** Ch11 (Bach §F8b)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Online/Bandits`

## Statement

_See textbook excerpt below or [`tasks/bandit-regret-eq-rewrite/`](../../../tasks/bandit-regret-eq-rewrite/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Bandit regret rewrite: R_T = T·µ⋆ − Σ µ(a_t)

**Concept ID:** `bandit-regret-eq-rewrite`
**Chapter:** Ch 11
**Section:** §11.3 (foundation F8b)
**Pages:** 332 (book) / PDF p. 348
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

The Lean carrier `banditRegret_eq_T_mu_minus_sum` is just the definitional unfolding of `banditRegret` from §11.3, p. 332:

$$R_T \;=\; T \cdot \mu^\star \;-\; \sum_{t=1}^{T} \mu(a_t).$$

> "Our criterion is the expected regret … equal to $R_t = t \cdot \max_{i \in \{1,\dots,k\}} \mu^{(i)} - \sum_{s=1}^{t} \mathbb{E}[r_s]$."

The Lean rewrite makes the right-hand-side syntactically available for downstream `simp`/`linarith` use.

## Proof (verbatim)

Definitional unfolding; no proof in the book (this is the formula itself). One-line Lean: `rfl` or `unfold banditRegret; rfl`.

## Notes

- Cosmetic rewrite to expose the carrier as a $T\mu^\star - \sum_t \mu(a_t)$ shape.
- Used by `sum-gaps-rewrite` and `bandit-regret-eq-sum-gaps-strong` as the algebraic pivot.
- No probability content.

## Prerequisites (Bach's dependency graph)

- [`bandit-foundation`](./bandit-foundation.md) — Multi-armed bandit foundation: cumulative regret

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/Bandit.lean`
- **Theorem/def name:** `banditRegret_eq_T_mu_minus_sum`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

