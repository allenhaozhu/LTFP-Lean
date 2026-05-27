# OCO cumulative loss L_T(x) = ∑_t f_t(x)

**ID:** `cum-loss`  
**Chapter:** Ch11 (Bach §F8a)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/cum-loss/`](../../../tasks/cum-loss/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — OCO cumulative loss L_T(x)

**Concept ID:** `cum-loss`
**Chapter:** Ch 11
**Section:** §11.1 (foundation F8a — algebraic shell)
**Pages:** 315 (book) / PDF p. 331
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach writes the regret (eq. (11.1), p. 315) as a difference of two sums over $s = 1,\dots,t$:

$$\underbrace{\frac{1}{t}\sum_{s=1}^{t} F_s(\theta_{s-1})}_{\text{cumulative loss along trajectory}} \;-\; \inf_{\theta \in C} \underbrace{\frac{1}{t}\sum_{s=1}^{t} F_s(\theta)}_{\text{cumulative loss of fixed action}}.$$

The Lean carrier `cumLoss fs x := ∑ t, fs t x` packages the right-hand summand — the cumulative loss of a fixed action $x$ across the horizon.

## Proof (verbatim)

Definition; not a theorem. Bach uses this quantity implicitly throughout §11.1 (in the proof of Proposition 11.1, p. 316-317).

## Notes

- The OCO normalization in Bach is $1/t$ (normalized regret, p. 315 boxed warning). The Lean `cumLoss` is the unnormalized $\sum_t f_t(x)$, matching the convention used for `regret` (so that `regret = cumLoss-along-trajectory - cumLoss-of-comparator`).
- Used as the building block for `regret-cumloss-diff` (the algebraic identity reshuffling), `cum-loss-zero-horizon`, `cum-loss-zero-fs`, and `cum-loss-const`.

## Prerequisites (Bach's dependency graph)

- [`online-convex-foundation`](./online-convex-foundation.md) — Online-convex foundation: regret definition

## Dependents (concepts that use this)

- [`cum-loss-const`](./cum-loss-const.md) — OCO cumulative loss with constant function = T·c
- [`cum-loss-zero-fs`](./cum-loss-zero-fs.md) — OCO cumulative loss with all-zero loss functions = 0
- [`cum-loss-zero-horizon`](./cum-loss-zero-horizon.md) — OCO cumulative loss vanishes on empty horizon
- [`regret-cumloss-diff`](./regret-cumloss-diff.md) — Regret as difference of cumulative losses

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/OnlineConvex.lean`
- **Theorem/def name:** `cumLoss`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

