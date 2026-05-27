# Bandit regret with constant action

**ID:** `bandit-regret-const-action`  
**Chapter:** Ch11 (Bach §F8b)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Online/Bandits`

## Statement

_See textbook excerpt below or [`tasks/bandit-regret-const-action/`](../../../tasks/bandit-regret-const-action/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Bandit regret with constant action = T·Δ(a)

**Concept ID:** `bandit-regret-const-action`
**Chapter:** Ch 11
**Section:** §11.3 (foundation F8b)
**Pages:** 332 (book) / PDF p. 348
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Sanity corollary of Bach's regret definition (p. 332):

$$R_T = T \mu^\star - \sum_{t=1}^{T} \mu(a_t).$$

If we always play the same arm $a$, i.e. $a_t \equiv a$ for all $t$, then

$$R_T \;=\; T \mu^\star - T \mu(a) \;=\; T \cdot \Delta(a).$$

Bach uses this implicitly: the explore-then-commit analysis (p. 333) decomposes the regret into an "explore phase" cost of $m \sum_j \Delta^{(j)}$ — each arm pulled $m$ times contributes $m \Delta^{(j)}$, which is exactly the constant-action regret for $T = m$ rounds on arm $j$.

## Proof (verbatim)

Bach defers. Algebraic: substitute $\mu(a_t) = \mu(a)$ into the regret formula; the empty horizon collapses to $T \cdot \mu(a)$ via `Finset.sum_const`. One-line Lean:

```
unfold banditRegret; simp [Finset.sum_const, Fintype.card_fin]; ring
```

## Notes

- Sanity check for `banditRegret` on constant policies (e.g., "always pull arm 1").
- Useful baseline: the constant-best-arm policy has regret $0$ (since $\Delta(i^\star) = 0$), confirming consistency with `gap-optimal`.
- No probability content.

## Prerequisites (Bach's dependency graph)

- [`bandit-foundation`](./bandit-foundation.md) — Multi-armed bandit foundation: cumulative regret

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/Bandit.lean`
- **Theorem/def name:** `banditRegret_constant_action`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

