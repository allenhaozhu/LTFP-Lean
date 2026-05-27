# Suboptimality gap of an arm

**ID:** `bandit-gap`  
**Chapter:** Ch11 (Bach §11.3, p. 333)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Online/Bandits`

## Statement

_See textbook excerpt below or [`tasks/bandit-gap/`](../../../tasks/bandit-gap/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Bandit suboptimality gap Δ⁽ʲ⁾

**Concept ID:** `bandit-gap`
**Chapter:** Ch 11
**Section:** §11.3
**Pages:** 332-333 (book) / PDF pp. 348-349
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

From §11.3, p. 332 (immediately following the regret definition):

> "Denoting $\Delta^{(j)} = \max_{i \in \{1,\dots,k\}} \mu^{(i)} - \mu^{(j)} \ge 0$ as the difference between the mean of the best arm and the mean of arm $j$, and $n_t^{(j)}$ as the number of times that arm $j$ was selected in the first $t$ iterations, we can express the regret as
> $$R_t = \sum_{j=1}^{k} \Delta^{(j)} \mathbb{E}[n_t^{(j)}]. \tag{11.19}$$"

The Lean carrier `gap` packages the algebraic definition $\Delta(a) := \mu^\star - \mu(a)$.

## Proof (verbatim)

Definition; not a theorem. The eq. (11.19) decomposition that uses it is the carrier of `bandit-regret-sum-gaps`.

## Notes

- Bach's notation: superscript $(j)$ indexes the arm. The Lean signature `gap (μ_star : ℝ) (μ : α → ℝ) (a : α) : ℝ := μ_star - μ a` keeps the arm index abstract (`α`) so the definition applies whether arms are `Fin k` or richer.
- $\Delta^{(j)} \ge 0$ holds iff $\mu^\star = \max_i \mu^{(i)}$ — Bach's $\mu^\star$ is *by definition* the maximum, so the inequality is automatic. The Lean theorem `gap-nonneg` makes this hypothesis explicit via `μ_star ≥ μ a`.
- For the optimal arm $i^\star$, $\Delta^{(i^\star)} = 0$ (theorem `gap-optimal`).

## Prerequisites (Bach's dependency graph)

- [`bandit-foundation`](./bandit-foundation.md) — Multi-armed bandit foundation: cumulative regret

## Dependents (concepts that use this)

- [`bandit-regret-eq-sum-gaps-strong`](./bandit-regret-eq-sum-gaps-strong.md) — Bandit regret = sum of gaps (strong)
- [`bandit-regret-sum-gaps`](./bandit-regret-sum-gaps.md) — Bandit regret = sum of per-step gaps
- [`gap-antitone-mu`](./gap-antitone-mu.md) — Bandit gap antitone in arm value
- [`gap-def`](./gap-def.md) — Bandit gap definitional
- [`gap-eq-diff`](./gap-eq-diff.md) — Bandit gap = μ⋆ - μ a
- [`gap-mono-mu-star`](./gap-mono-mu-star.md) — Bandit gap monotone in optimal mean
- [`gap-nonneg`](./gap-nonneg.md) — Bandit gap nonneg under μ a ≤ μ⋆
- [`gap-optimal`](./gap-optimal.md) — Gap of optimal arm is zero
- [`sum-gaps-nonneg`](./sum-gaps-nonneg.md) — Sum of nonneg gaps is nonneg
- [`sum-gaps-rewrite`](./sum-gaps-rewrite.md) — ∑ gap = T·μ⋆ − ∑ μ_a

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch11_OnlineBandits/UCB.lean`
- **Theorem/def name:** `gap`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

