# Bandit gap nonneg under μ a ≤ μ⋆

**ID:** `gap-nonneg`  
**Chapter:** Ch11 (Bach §11.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Online/Bandits`

## Statement

_See textbook excerpt below or [`tasks/gap-nonneg/`](../../../tasks/gap-nonneg/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Bandit gap is nonnegative

**Concept ID:** `gap-nonneg`
**Chapter:** Ch 11
**Section:** §11.3
**Pages:** 332 (book) / PDF p. 348
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

From §11.3, p. 332:

> "Denoting $\Delta^{(j)} = \max_{i \in \{1,\dots,k\}} \mu^{(i)} - \mu^{(j)} \ge 0$ as the difference between the mean of the best arm and the mean of arm $j$, …"

Bach asserts the inequality $\Delta^{(j)} \ge 0$ as part of the definition (the max majorizes every coordinate).

Lean carrier `gap_nonneg`: given a hypothesis `h : μ a ≤ μ_star`, $\Delta(a) = \mu^\star - \mu(a) \ge 0$.

## Proof (verbatim)

Bach defers; this is the "$\ge 0$" annotation on his definition. Algebraically: $\mu^\star = \max_i \mu^{(i)} \ge \mu^{(j)}$, so $\mu^\star - \mu^{(j)} \ge 0$. The Lean version makes the upper-bound hypothesis explicit (since `μ_star` is taken as an abstract real, not literally `max`), so the discharge is `sub_nonneg.mpr h`.

## Notes

- One-line Lean proof: `unfold gap; exact sub_nonneg.mpr h` (or `linarith` from the hypothesis).
- Foundation for `sum-gaps-nonneg` (sum of nonneg terms is nonneg) which in turn underwrites the positivity of the UCB regret bound (11.28).
- Sign convention: positive gap means the arm is suboptimal.

## Prerequisites (Bach's dependency graph)

- [`bandit-gap`](./bandit-gap.md) — Suboptimality gap of an arm

## Dependents (concepts that use this)

- [`sum-gaps-nonneg`](./sum-gaps-nonneg.md) — Sum of nonneg gaps is nonneg

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch11_OnlineBandits/UCB.lean`
- **Theorem/def name:** `gap_nonneg`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

