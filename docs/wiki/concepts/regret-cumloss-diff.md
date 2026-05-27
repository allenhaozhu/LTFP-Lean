# Regret as difference of cumulative losses

**ID:** `regret-cumloss-diff`  
**Chapter:** Ch11 (Bach §F8a)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Online/Bandits`

## Statement

_See textbook excerpt below or [`tasks/regret-cumloss-diff/`](../../../tasks/regret-cumloss-diff/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Regret as difference of cumulative losses

**Concept ID:** `regret-cumloss-diff`
**Chapter:** Ch 11
**Section:** §11.1 (foundation F8a)
**Pages:** 315 (book) / PDF p. 331
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach (eq. (11.1), p. 315):

$$R_T(\theta^\star) \;=\; \frac{1}{t}\sum_{s=1}^{t} F_s(\theta_{s-1}) - \inf_{\theta \in C} \frac{1}{t}\sum_{s=1}^{t} F_s(\theta).$$

The Lean theorem `regret_eq_cumLoss_diff` rewrites the unnormalized regret as a difference of cumulative losses against a *fixed* comparator $\theta^\star$ (i.e., dropping the infimum and exposing the algebraic shell):

$$R_T(\theta^\star) \;=\; \left(\sum_{t=0}^{T-1} F_t(\theta_t)\right) - L_T(\theta^\star).$$

## Proof (verbatim)

Bach defers — this is the unfolding of his eq. (11.1) when the infimum is attained at a specific $\theta^\star$. In Lean it is `rfl` (definitional equality after unfolding `regret` and `cumLoss`).

## Notes

- Defunctionalizes: regret = trajectory cumulative loss − comparator cumulative loss.
- Used as a cosmetic rewrite to expose `cumLoss` as the right-hand side, which is then a target for `cum-loss-zero-horizon`, `cum-loss-const`, and `cum-loss-zero-fs` sanity checks.
- Foundation lemma; no probability or convexity content.

## Prerequisites (Bach's dependency graph)

- [`cum-loss`](./cum-loss.md) — OCO cumulative loss L_T(x) = ∑_t f_t(x)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/OnlineConvex.lean`
- **Theorem/def name:** `regret_eq_cumLoss_diff`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

