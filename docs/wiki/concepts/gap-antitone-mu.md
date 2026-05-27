# Bandit gap antitone in arm value

**ID:** `gap-antitone-mu`  
**Chapter:** Ch11 (Bach §11.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Online/Bandits`

## Statement

_See textbook excerpt below or [`tasks/gap-antitone-mu/`](../../../tasks/gap-antitone-mu/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Gap antitone in arm value µ(a)

**Concept ID:** `gap-antitone-mu`
**Chapter:** Ch 11
**Section:** §11.3
**Pages:** 332 (book) / PDF p. 348
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Antitone sanity property of `gap` (Bach §11.3, p. 332):

If $\mu(a) \le \mu'(a)$ (the arm's own mean increases), then for fixed $\mu^\star$,

$$\Delta(a; \mu) = \mu^\star - \mu(a) \;\ge\; \mu^\star - \mu'(a) = \Delta(a; \mu').$$

Intuition: as the arm gets better, its gap to the optimum shrinks.

Bach does not state this — automatic from the definition.

## Proof (verbatim)

Bach defers. Algebraic: subtracting a larger value gives a smaller result. One-line Lean: `unfold gap; linarith` (or `exact sub_le_sub_left h _`).

## Notes

- Sanity property; says the gap function is antitone (decreasing) in the arm's own mean.
- Companion to `gap-mono-mu-star` (monotone in the baseline best-arm mean).
- Defining quality of `gap`: as $\mu(a) \to \mu^\star$, $\Delta(a) \to 0$ (limit case = `gap-optimal`).

## Prerequisites (Bach's dependency graph)

- [`bandit-gap`](./bandit-gap.md) — Suboptimality gap of an arm

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch11_OnlineBandits/UCB.lean`
- **Theorem/def name:** `gap_antitone_mu`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

