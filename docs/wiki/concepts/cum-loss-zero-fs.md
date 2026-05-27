# OCO cumulative loss with all-zero loss functions = 0

**ID:** `cum-loss-zero-fs`  
**Chapter:** Ch11 (Bach §F8a)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/cum-loss-zero-fs/`](../../../tasks/cum-loss-zero-fs/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — OCO cumulative loss with all-zero losses is zero

**Concept ID:** `cum-loss-zero-fs`
**Chapter:** Ch 11
**Section:** §11.1 (foundation F8a)
**Pages:** 315 (book) / PDF p. 331
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Sanity corollary of `cum-loss` (Bach §11.1, p. 315):

$$L_T(x) = \sum_{t=1}^{T} F_t(x).$$

If every $F_t \equiv 0$, then $L_T(x) = 0$ for all $x$. Bach does not state this — it is the degenerate edge case where the adversary has no power.

## Proof (verbatim)

Bach defers. Algebraic: $\sum_t 0 = 0$. One-line Lean: `unfold cumLoss; simp`.

## Notes

- Sanity check; the cumulative loss carrier is trivially zero when every per-round loss vanishes.
- Companion to `cum-loss-const` (constant losses) and `cum-loss-zero-horizon` (empty horizon).
- No probability or convexity content.

## Prerequisites (Bach's dependency graph)

- [`cum-loss`](./cum-loss.md) — OCO cumulative loss L_T(x) = ∑_t f_t(x)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/OnlineConvex.lean`
- **Theorem/def name:** `cumLoss_zero_fs`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

