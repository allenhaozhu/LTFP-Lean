# OCO cumulative loss vanishes on empty horizon

**ID:** `cum-loss-zero-horizon`  
**Chapter:** Ch11 (Bach §F8a)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/cum-loss-zero-horizon/`](../../../tasks/cum-loss-zero-horizon/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — OCO cumulative loss at horizon T=0 is zero

**Concept ID:** `cum-loss-zero-horizon`
**Chapter:** Ch 11
**Section:** §11.1 (foundation F8a)
**Pages:** 315 (book) / PDF p. 331
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Sanity corollary of the cumulative loss definition (eq. (11.1), p. 315):

$$L_T(x) = \sum_{t=1}^{T} F_t(x).$$

At $T = 0$ this is the empty sum, hence $L_0(x) = 0$ for every $x$. Bach does not state this — it is a degenerate edge case of his definition.

## Proof (verbatim)

Bach defers. The empty sum `∑ t : Fin 0, fs t x` reduces to `0` by `Finset.sum_empty`. One-line Lean: `unfold cumLoss; simp`.

## Notes

- Purely sanity; confirms `cumLoss` handles the empty horizon correctly.
- Mirror of `bandit-regret-zero-horizon` on the OCO side.
- Used downstream as a base case if any inductive argument over the horizon needs $T = 0$.

## Prerequisites (Bach's dependency graph)

- [`cum-loss`](./cum-loss.md) — OCO cumulative loss L_T(x) = ∑_t f_t(x)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/OnlineConvex.lean`
- **Theorem/def name:** `cumLoss_zero_horizon`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

