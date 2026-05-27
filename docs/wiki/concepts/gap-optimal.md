# Gap of optimal arm is zero

**ID:** `gap-optimal`  
**Chapter:** Ch11 (Bach §11.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/gap-optimal/`](../../../tasks/gap-optimal/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Gap of the optimal arm is zero

**Concept ID:** `gap-optimal`
**Chapter:** Ch 11
**Section:** §11.3
**Pages:** 332 (book) / PDF p. 348
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

From §11.3, p. 332 (parenthetical aside in the explore-then-commit analysis):

> "by only imposing that an arm $j$ is selected if $\hat\mu_{mk}^{(j)} > \hat\mu_{mk}^{(i^\star)}$ (noting that $\Delta^{(i^\star)} = 0$):"

Algebraic statement: if $\mu(a) = \mu^\star$ then $\Delta(a) = \mu^\star - \mu(a) = 0$.

Lean carrier `gap_optimal`: `μ a = μ_star → gap μ_star μ a = 0`.

## Proof (verbatim)

Bach defers (parenthetical on p. 332). Algebraically: $\Delta^{(i^\star)} = \mu^\star - \mu^{(i^\star)} = \mu^\star - \mu^\star = 0$. One-line Lean: substitute `μ a = μ_star` into `gap = μ_star - μ a` to get `μ_star - μ_star = 0`.

## Notes

- One-line proof: `unfold gap; rw [h, sub_self]`.
- Critical for the regret decomposition: $R_t = \sum_{j \neq i^\star} \Delta^{(j)} \mathbb{E}[n_t^{(j)}]$ (i.e., the optimal arm contributes zero), which is the form used in Bach's eq. (11.28) UCB bound on p. 338.
- Companion to `gap-nonneg` (the other defining sanity property of the gap function).

## Prerequisites (Bach's dependency graph)

- [`bandit-gap`](./bandit-gap.md) — Suboptimality gap of an arm

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch11_OnlineBandits/UCB.lean`
- **Theorem/def name:** `gap_optimal`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

