# Multi-armed bandit foundation: cumulative regret

**ID:** `bandit-foundation`  
**Chapter:** Ch11 (Bach §F8b)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Online/Bandits`

## Statement

Required prereq for Ch 11.

## Bach's textbook treatment

# Bach textbook excerpt — Multi-armed bandit foundation: cumulative regret

**Concept ID:** `bandit-foundation`
**Chapter:** Ch 11
**Section:** §11.3 (foundation F8b — algebraic anchor)
**Pages:** 331-332 (book) / PDF pp. 347-348
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

From §11.3, p. 331-332:

> "We consider $k$ potential arms, each associated with a mean $\mu^{(i)} \in \mathbb{R}$, $i \in \{1,\dots,k\}$. Every time we select arm $i$, we receive a reward sampled independent of all other rewards and the previous arm choices from a sub-Gaussian distribution with mean $\mu^{(i)}$, and sub-Gaussian parameter $\sigma$. At time $s$, we select arm $i_s$ based on the information $\mathcal{F}_{s-1}$ up to time $s-1$ (i.e., the rewards received before time $s-1$) and receive reward $r_s$."

> "Our criterion is the expected regret (adapted to the maximization of rewards), equal to
> $$R_t = t \cdot \max_{i \in \{1,\dots,k\}} \mu^{(i)} - \sum_{s=1}^{t} \mathbb{E}[r_s].$$"

> Aside (boxed warning, p. 332): "As opposed to online learning in section 11.1, here we are not dividing the regret by $t$."

The Lean anchor `banditRegret` is exactly the deterministic algebraic shell

$$R_T = T \cdot \mu^\star - \sum_{t=1}^{T} \mu_{i_t},$$

where `mu_star : ℝ` is the optimal mean and the `μ_{i_t}` values are read out of the action sequence as `μ ∘ a t`.

## Proof (verbatim)

Definition; no proof. Bach derives the gap form $R_t = \sum_j \Delta^{(j)} \mathbb{E}[n_t^{(j)}]$ (eq. (11.19)) in the next paragraph — that derivation is the carrier for `bandit-regret-sum-gaps`.

## Notes

- Bach's $\mathbb{E}[r_s]$ is replaced in the Lean anchor by a deterministic per-arm value $\mu(a_t)$ because the sub-Gaussian noise drops out under expectation (the expected reward of pulling arm $a_t$ is $\mu(a_t)$). This is the algebraic core; the probabilistic shell wraps it.
- Sign convention: rewards (not losses). $R_t \ge 0$ because $\mu^\star$ majorizes every $\mu^{(i)}$.
- Foundation for every Ch 11 bandit theorem (`bandit-gap`, `gap-nonneg`, `bandit-regret-sum-gaps`, `ucb-bonus`, etc.).

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

- [`bandit-gap`](./bandit-gap.md) — Suboptimality gap of an arm
- [`bandit-regret-const-action`](./bandit-regret-const-action.md) — Bandit regret with constant action
- [`bandit-regret-eq-rewrite`](./bandit-regret-eq-rewrite.md) — Bandit regret = T·μ⋆ − ∑t μ_{a_t}
- [`bandit-regret-smul`](./bandit-regret-smul.md) — Bandit regret rewriting in scaled mu_star
- [`bandit-regret-zero-horizon`](./bandit-regret-zero-horizon.md) — Bandit regret is zero on empty horizon
- [`explore-then-commit`](./explore-then-commit.md) — Explore-then-commit exploration phase predicate
- [`ucb-bonus`](./ucb-bonus.md) — UCB confidence bonus √(2 log t / n)

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/Bandit.lean`
- **Theorem/def name:** `banditRegret`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

