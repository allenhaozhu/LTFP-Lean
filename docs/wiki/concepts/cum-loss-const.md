# OCO cumulative loss with constant function = T·c

**ID:** `cum-loss-const`  
**Chapter:** Ch11 (Bach §F8a)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/cum-loss-const/`](../../../tasks/cum-loss-const/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — OCO cumulative loss with constant function = T·c

**Concept ID:** `cum-loss-const`
**Chapter:** Ch 11
**Section:** §11.1 (foundation F8a)
**Pages:** 315 (book) / PDF p. 331
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Sanity corollary of `cum-loss` (Bach §11.1, p. 315):

$$L_T(x) = \sum_{t=1}^{T} F_t(x).$$

If $F_t(x) \equiv c$ (constant in both $t$ and $x$), then $L_T(x) = T \cdot c$ for every $x$. Bach does not state this — it is the degenerate edge case where the adversary plays a constant loss every round.

## Proof (verbatim)

Bach defers. Algebraic: $\sum_{t=1}^{T} c = T \cdot c$. One-line Lean:

```
unfold cumLoss
rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
```

## Notes

- Sanity check on `cumLoss` for the constant-loss adversary.
- Companion to `cum-loss-zero-fs` (zero losses ⇒ zero cumulative loss, the special case $c = 0$).
- No probability or convexity content.

## Prerequisites (Bach's dependency graph)

- [`cum-loss`](./cum-loss.md) — OCO cumulative loss L_T(x) = ∑_t f_t(x)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/OnlineConvex.lean`
- **Theorem/def name:** `cumLoss_const`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

