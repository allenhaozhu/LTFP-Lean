# Bandit regret = sum of gaps (strong)

**ID:** `bandit-regret-eq-sum-gaps-strong`  
**Chapter:** Ch11 (Bach §11.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Online/Bandits`

## Statement

_See textbook excerpt below or [`tasks/bandit-regret-eq-sum-gaps-strong/`](../../../tasks/bandit-regret-eq-sum-gaps-strong/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Bandit regret = sum of gaps (strong, unconditional)

**Concept ID:** `bandit-regret-eq-sum-gaps-strong`
**Chapter:** Ch 11
**Section:** §11.3
**Pages:** 332 (book) / PDF p. 348
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Strong/unconditional version of `bandit-regret-sum-gaps`. From the algebraic chain:

$$R_T \;=\; T \mu^\star - \sum_{t=1}^{T} \mu(a_t) \;=\; \sum_{t=1}^{T} (\mu^\star - \mu(a_t)) \;=\; \sum_{t=1}^{T} \Delta(a_t).$$

Bach states the per-arm form (eq. (11.19)) "$R_t = \sum_{j=1}^{k} \Delta^{(j)} \mathbb{E}[n_t^{(j)}]$"; the Lean theorem `banditRegret_eq_sum_gaps_strong` gives the per-step trajectory form $R_T = \sum_t \Delta(a_t)$, which is the algebraic predecessor of Bach's per-arm form.

## Proof (verbatim)

Bach defers — the per-step form is the line he skips when going from "$t \mu^\star - \sum_s \mathbb{E}[r_s]$" directly to the per-arm sum (eq. (11.19), p. 332). Composing:

1. `banditRegret_eq_T_mu_minus_sum` (definitional unfolding).
2. `sum_gaps_eq_T_mu_minus_sum_actions` (algebraic identity).

gives the chain `R_T = T μ⋆ − Σ μ(a_t) = Σ (μ⋆ − μ(a_t)) = Σ gap(a_t)`. One-line Lean: `rw [banditRegret_eq_T_mu_minus_sum, ← sum_gaps_eq_T_mu_minus_sum_actions]`.

## Notes

- "Strong" because it does not require any constraint on $\mu^\star$ (works for any chosen baseline mean — Bach assumes $\mu^\star = \max_i \mu^{(i)}$, but the identity is purely algebraic).
- Direct corollary of `sum-gaps-rewrite` + `bandit-regret-eq-rewrite`.
- Used as the algebraic pivot in the UCB and explore-then-commit analyses.

## Prerequisites (Bach's dependency graph)

- [`bandit-gap`](./bandit-gap.md) — Suboptimality gap of an arm
- [`bandit-regret-sum-gaps`](./bandit-regret-sum-gaps.md) — Bandit regret = sum of per-step gaps

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch11_OnlineBandits/UCB.lean`
- **Theorem/def name:** `banditRegret_eq_sum_gaps_strong`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

