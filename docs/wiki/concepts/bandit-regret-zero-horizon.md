# Bandit regret is zero on empty horizon

**ID:** `bandit-regret-zero-horizon`  
**Chapter:** Ch11 (Bach §11.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Online/Bandits`

## Statement

_See textbook excerpt below or [`tasks/bandit-regret-zero-horizon/`](../../../tasks/bandit-regret-zero-horizon/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Bandit regret at horizon T=0 is zero

**Concept ID:** `bandit-regret-zero-horizon`
**Chapter:** Ch 11
**Section:** §11.3 (sanity corollary of `bandit-foundation`)
**Pages:** 331-332 (book) / PDF p. 348
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Sanity corollary of Bach's regret definition (p. 332):

$$R_t = t \cdot \mu^\star - \sum_{s=1}^{t} \mathbb{E}[r_s].$$

At $t = 0$ both terms vanish, so $R_0 = 0$. Bach does not call this out explicitly — it is the empty-horizon edge case of his eq. before (11.19).

## Proof (verbatim)

Bach defers. Algebraically: at $T = 0$, $T \cdot \mu^\star = 0$ and the empty sum $\sum_{s=1}^{0} \mu(a_s) = 0$, so the difference vanishes. In Lean this discharges by `simp [banditRegret]` (the empty `Fin 0` sum is `0`).

## Notes

- Pure algebraic sanity check; verifies the carrier definition handles the empty horizon correctly.
- One-line Lean proof: unfold `banditRegret`, `Finset.sum_empty` (or `Finset.univ_eq_empty` on `Fin 0`), `mul_zero`.
- No probability content; just confirms the formula's degenerate behavior.

## Prerequisites (Bach's dependency graph)

- [`bandit-foundation`](./bandit-foundation.md) — Multi-armed bandit foundation: cumulative regret

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch11_OnlineBandits/UCB.lean`
- **Theorem/def name:** `banditRegret_zero_horizon`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

