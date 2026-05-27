# Bandit gap monotone in optimal mean

**ID:** `gap-mono-mu-star`  
**Chapter:** Ch11 (Bach §11.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Online/Bandits`

## Statement

_See textbook excerpt below or [`tasks/gap-mono-mu-star/`](../../../tasks/gap-mono-mu-star/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Gap monotone in µ⋆

**Concept ID:** `gap-mono-mu-star`
**Chapter:** Ch 11
**Section:** §11.3
**Pages:** 332 (book) / PDF p. 348
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Monotonicity sanity property of `gap` (Bach §11.3, p. 332):

If $\mu^\star \le \mu^{\star\prime}$ (i.e., we increase the baseline best-arm mean), then for every fixed $\mu$ and arm $a$,

$$\Delta(a; \mu^\star) = \mu^\star - \mu(a) \;\le\; \mu^{\star\prime} - \mu(a) = \Delta(a; \mu^{\star\prime}).$$

Bach does not state this — it is automatic from the definition $\Delta = \mu^\star - \mu(a)$ and the fact that subtraction by a fixed value is monotone in its first argument.

## Proof (verbatim)

Bach defers. Algebraic: subtracting a fixed quantity preserves the ordering. One-line Lean: `unfold gap; linarith` (or `exact sub_le_sub_right h _`).

## Notes

- Sanity property; says the gap function is monotone in the baseline best-arm mean.
- Companion to `gap-antitone-mu` (antitone in the arm's own mean).
- No mathematical content beyond definitional unfolding + ordered-field reasoning.

## Prerequisites (Bach's dependency graph)

- [`bandit-gap`](./bandit-gap.md) — Suboptimality gap of an arm

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch11_OnlineBandits/UCB.lean`
- **Theorem/def name:** `gap_mono_mu_star`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

