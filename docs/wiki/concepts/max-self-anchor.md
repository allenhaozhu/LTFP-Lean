# max R R = R (anchor)

**ID:** `max-self-anchor`  
**Chapter:** Ch15 (Bach §15.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/max-self-anchor/`](../../../tasks/max-self-anchor/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — max R R = R (anchor)

**Concept ID:** `max-self-anchor`
**Chapter:** Ch 15
**Section:** §15.1.2 (Eq. 15.4) — degenerate maximum
**Pages:** 429-430 (book) / 445-446 (PDF)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Carrier `LTFP.Ch15_LowerBounds.Statistical.max_self_anchor`. Algebraic
identity:

> For any `R`,
>
>     max(R, R)  =  R.

Boundary instance of Bach's Eq. (15.4) maximum: when all distinguished
parameters give the same testing-error probability, the maximum
collapses.

## Proof (verbatim)

Bach §15.1.2 (p. 429-430), Eq. (15.4):

> "Then, because we take the supremum over a smaller set,
>
>     sup_{θ* ∈ Θ} P_{θ*}( δ(θ*, A(D))² ≥ A )
>       ≥ max_{j ∈ {1,…,M}} P_{θ_j}( δ(θ*, A(D))² ≥ A ).      (15.4)"

When `M = 2` and the two probabilities coincide, `max(R, R) = R`.

## Notes

- **Bach's technique in one line:** `max R R = R` (Lean: `max_self R`).
- Used as a boundary / symmetry anchor; mirrors `sup_singleton` at the
  M = 2 level.

## Prerequisites (Bach's dependency graph)

- [`testing-error-nonneg`](./testing-error-nonneg.md) — Statistical lower-bound anchor: testing error nonneg

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch15_LowerBounds/Statistical.lean`
- **Theorem/def name:** `max_self_anchor`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

