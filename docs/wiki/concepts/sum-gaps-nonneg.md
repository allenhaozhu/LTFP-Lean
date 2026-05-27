# Sum of nonneg gaps is nonneg

**ID:** `sum-gaps-nonneg`  
**Chapter:** Ch11 (Bach §11.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/sum-gaps-nonneg/`](../../../tasks/sum-gaps-nonneg/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Sum of gaps is nonnegative

**Concept ID:** `sum-gaps-nonneg`
**Chapter:** Ch 11
**Section:** §11.3
**Pages:** 332 (book) / PDF p. 348
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Corollary of `gap-nonneg` (Bach §11.3, p. 332): a finite sum of nonnegative gaps is nonnegative,

$$\sum_{t=1}^{T} \Delta(a_t) \;\ge\; 0,$$

provided every $\mu(a_t) \le \mu^\star$ (which Bach assumes throughout §11.3, where $\mu^\star = \max_i \mu^{(i)}$).

This is the sign certificate for the regret: combined with `bandit-regret-eq-sum-gaps-strong`, it yields $R_T \ge 0$.

## Proof (verbatim)

Bach defers. Algebraic: sum of nonneg terms is nonneg. One-line Lean: `Finset.sum_nonneg (fun t _ => gap_nonneg (h t))` where `h : ∀ t, μ (a t) ≤ μ_star`.

## Notes

- Sign certificate underwriting Bach's $R_t \ge 0$ throughout §11.3 (e.g., the UCB bound eq. (11.28), p. 338, is a *bound on a nonneg quantity*).
- Direct corollary of `gap-nonneg` applied pointwise + `Finset.sum_nonneg`.
- No probability content beyond the per-arm hypothesis $\mu(a) \le \mu^\star$.

## Prerequisites (Bach's dependency graph)

- [`bandit-gap`](./bandit-gap.md) — Suboptimality gap of an arm
- [`gap-nonneg`](./gap-nonneg.md) — Bandit gap nonneg under μ a ≤ μ⋆

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch11_OnlineBandits/UCB.lean`
- **Theorem/def name:** `sum_gaps_nonneg`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

