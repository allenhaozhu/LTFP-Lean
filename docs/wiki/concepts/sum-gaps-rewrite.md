# ∑ gap = T·μ⋆ − ∑ μ_a

**ID:** `sum-gaps-rewrite`  
**Chapter:** Ch11 (Bach §11.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/sum-gaps-rewrite/`](../../../tasks/sum-gaps-rewrite/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Σ gap = T·µ⋆ − Σ µ(a_t)

**Concept ID:** `sum-gaps-rewrite`
**Chapter:** Ch 11
**Section:** §11.3
**Pages:** 332-333 (book) / PDF pp. 348-349
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Algebraic identity used implicitly in the derivation of Bach's eq. (11.19), p. 332:

$$\sum_{t=1}^{T} \Delta(a_t) \;=\; \sum_{t=1}^{T} (\mu^\star - \mu(a_t)) \;=\; T \mu^\star - \sum_{t=1}^{T} \mu(a_t).$$

Lean carrier `sum_gaps_eq_T_mu_minus_sum_actions`.

## Proof (verbatim)

Bach defers — this is the algebraic step between "$R_t = t \mu^\star - \sum \mathbb{E}[r_s]$" and the per-arm form "$\sum_j \Delta^{(j)} \mathbb{E}[n_t^{(j)}]$" (eq. (11.19)). The intermediate per-step form is

$$\sum_{s=1}^{t} (\mu^\star - \mu(a_s)) = t \mu^\star - \sum_{s=1}^{t} \mu(a_s),$$

which uses $\sum_s c = T \cdot c$ (constant sum) and linearity of the finite sum. In Lean: `Finset.sum_sub_distrib` + `Finset.sum_const`.

## Notes

- One-step algebraic identity bridging `gap` and `banditRegret`.
- Direct prerequisite for `bandit-regret-eq-sum-gaps-strong`.
- No probability content.

## Prerequisites (Bach's dependency graph)

- [`bandit-gap`](./bandit-gap.md) — Suboptimality gap of an arm

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch11_OnlineBandits/UCB.lean`
- **Theorem/def name:** `sum_gaps_eq_T_mu_minus_sum_actions`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

