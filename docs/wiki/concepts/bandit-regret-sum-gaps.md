# Bandit regret = sum of per-step gaps

**ID:** `bandit-regret-sum-gaps`  
**Chapter:** Ch11 (Bach §11.3, p. 333)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Online/Bandits`

## Statement

_See textbook excerpt below or [`tasks/bandit-regret-sum-gaps/`](../../../tasks/bandit-regret-sum-gaps/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Bandit regret = sum of per-step gaps

**Concept ID:** `bandit-regret-sum-gaps`
**Chapter:** Ch 11
**Section:** §11.3 (eq. (11.19))
**Pages:** 332-333 (book) / PDF pp. 348-349
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

From §11.3, p. 332, eq. (11.19):

$$R_t = \sum_{j=1}^{k} \Delta^{(j)}\, \mathbb{E}[n_t^{(j)}].$$

> "Thus, the regret is a direct function of the number of times each arm is selected."

Lean carrier `banditRegret_eq_sum_gaps` rewrites the trajectory form into the per-step gap form:
$$\sum_{t=1}^{T} \Delta(a_t) \;=\; T \mu^\star - \sum_{t=1}^{T} \mu(a_t) \;=\; R_T.$$

## Proof (verbatim)

Bach gives the derivation at the bottom of p. 332 in two lines: substitute the rewards' expectations into $R_t = t \mu^\star - \sum_s \mathbb{E}[r_s]$ and group by arm index. Specifically:

> "Our criterion is the expected regret … equal to $R_t = t \cdot \max_i \mu^{(i)} - \sum_{s=1}^{t}\mathbb{E}[r_s]$."

Pulling the constant $\mu^\star = \max_i \mu^{(i)}$ inside the sum and using $\mathbb{E}[r_s] = \mu(a_s)$ (the action's mean):
$$R_t = \sum_{s=1}^{t} \big(\mu^\star - \mu(a_s)\big) = \sum_{s=1}^{t} \Delta(a_s).$$
Grouping by arm $j$ — i.e., counting how many times each arm appeared in the sum — gives $\sum_{j=1}^{k} \Delta^{(j)}\, n_t^{(j)}$, and taking expectations yields eq. (11.19).

The Lean form keeps the per-step (trajectory) presentation; the per-arm sum (eq. (11.19) verbatim) is downstream.

## Notes

- Algebraic identity, no probability content (the expectation step in Bach drops out because the Lean carrier uses deterministic per-arm means).
- Decomposed in `sum_gaps_eq_T_mu_minus_sum_actions` (`sum-gaps-rewrite`) which provides the per-step rewrite, then re-bundled in `banditRegret_eq_sum_gaps`.
- Prerequisite for the eq. (11.28) UCB regret bound: the UCB analysis bounds $\mathbb{E}[n_t^{(i)}]$ for suboptimal $i$, and this lemma is what converts the count bound into a regret bound.

## Prerequisites (Bach's dependency graph)

- [`bandit-gap`](./bandit-gap.md) — Suboptimality gap of an arm

## Dependents (concepts that use this)

- [`bandit-regret-eq-sum-gaps-strong`](./bandit-regret-eq-sum-gaps-strong.md) — Bandit regret = sum of gaps (strong)

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch11_OnlineBandits/UCB.lean`
- **Theorem/def name:** `banditRegret_eq_sum_gaps`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

