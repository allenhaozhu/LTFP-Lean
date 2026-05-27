# Min ≤ average for two-point risks

**ID:** `min-le-average`  
**Chapter:** Ch15 (Bach §15.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/min-le-average/`](../../../tasks/min-le-average/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Min ≤ average for two-point risks

**Concept ID:** `min-le-average`
**Chapter:** Ch 15
**Section:** §15.1.2 (Eq. 15.4-15.5) — bound from below
**Pages:** 429-431 (book) / 445-447 (PDF)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Carrier `LTFP.Ch15_LowerBounds.Statistical.min_le_average`. Algebraic
sandwich lower bound:

> For real `R₁, R₂`,
>
>     min(R₁, R₂)  ≤  (R₁ + R₂) / 2.

Dual / complementary to `(R₁ + R₂)/2 ≤ max(R₁, R₂)` (the
`le-cam-average` anchor); together they sandwich the average between
min and max.

## Proof (verbatim)

Bach §15.1.2 (p. 430), Eq. (15.5):

> "inf_A sup_{θ* ∈ Θ} E_{θ*}[ δ(θ*, A(D))² ]
>    ≥ A · inf_h max_{j ∈ {1,…,M}} P_{θ_j}( h(D) ≠ j )
>    ≥ A · inf_h (1/M) ∑_{j=1}^M P_{θ_j}( h(D) ≠ j ),     (15.5)"

Bach uses the upper sandwich `(1/M)∑ ≤ max_j`. The lower sandwich
`min_j ≤ (1/M)∑` is the symmetric algebraic fact; while Bach doesn't
use it directly in §15.1, downstream chaining (e.g., when combining
several Eq. 15.5 applications) wants both directions.

## Notes

- **Bach's technique in one line:** `min(R₁,R₂) ≤ avg ≤ max(R₁,R₂)` is
  the standard min-mean-max sandwich.
- Pairs with `le-cam-average` to give the full sandwich
  (`min-le-avg-le-max` is the combined anchor).
- Lean proof: case split on which is smaller, then `linarith`.

## Prerequisites (Bach's dependency graph)

- [`le-cam-average`](./le-cam-average.md) — Le Cam-style average ≤ max two-point inequality

## Dependents (concepts that use this)

- [`min-le-avg-le-max`](./min-le-avg-le-max.md) — Min ≤ average ≤ max sandwich

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch15_LowerBounds/Statistical.lean`
- **Theorem/def name:** `min_le_average`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

