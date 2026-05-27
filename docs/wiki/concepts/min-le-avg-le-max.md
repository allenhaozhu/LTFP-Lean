# Min ≤ average ≤ max sandwich

**ID:** `min-le-avg-le-max`  
**Chapter:** Ch15 (Bach §15.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/min-le-avg-le-max/`](../../../tasks/min-le-avg-le-max/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Min ≤ average ≤ max sandwich

**Concept ID:** `min-le-avg-le-max`
**Chapter:** Ch 15
**Section:** §15.1.2 (Eq. 15.4-15.5) — combined sandwich
**Pages:** 429-431 (book) / 445-447 (PDF)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Carrier `LTFP.Ch15_LowerBounds.Statistical.min_le_avg_le_max`. The
combined min-average-max sandwich for two reals:

> For real `R₁, R₂`,
>
>     min(R₁, R₂)  ≤  (R₁ + R₂) / 2  ≤  max(R₁, R₂).

Combination of `min-le-average` and `le-cam-average` into one statement.

## Proof (verbatim)

Bach §15.1.2 (p. 430), Eq. (15.5):

> "inf_A sup_{θ* ∈ Θ} E_{θ*}[ δ(θ*, A(D))² ]
>    ≥ A · inf_h max_{j ∈ {1,…,M}} P_{θ_j}( h(D) ≠ j )
>    ≥ A · inf_h (1/M) ∑_{j=1}^M P_{θ_j}( h(D) ≠ j ),     (15.5)"

The Le Cam-style upper sandwich `(1/M)∑ ≤ max` is Bach's; the lower
sandwich `min ≤ (1/M)∑` is the symmetric algebraic fact. Combined for
downstream registry users who want both directions in one cite.

## Notes

- **Bach's technique in one line:** standard min-mean-max ordering for
  finite real collections — `linarith`-shaped proof.
- Combines `min-le-average` and `le-cam-average`.
- Used when downstream registry chains need to bound both sides of
  the average in one step.

## Prerequisites (Bach's dependency graph)

- [`le-cam-average`](./le-cam-average.md) — Le Cam-style average ≤ max two-point inequality
- [`min-le-average`](./min-le-average.md) — Min ≤ average for two-point risks

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch15_LowerBounds/Statistical.lean`
- **Theorem/def name:** `min_le_avg_le_max`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

