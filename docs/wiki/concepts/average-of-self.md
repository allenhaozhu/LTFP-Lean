# Average of identical risks = the risk

**ID:** `average-of-self`  
**Chapter:** Ch15 (Bach §15.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/average-of-self/`](../../../tasks/average-of-self/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Average of identical risks = the risk

**Concept ID:** `average-of-self`
**Chapter:** Ch 15
**Section:** §15.1.2 (Eq. 15.5) — M-point average chain, degenerate case
**Pages:** 430-431 (book) / 446-447 (PDF)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Carrier `LTFP.Ch15_LowerBounds.Statistical.average_of_self`. Trivial
two-point average identity:

> For any `R`,
>
>     (R + R) / 2  =  R.

Boundary / degenerate case of Bach's `(1/M) ∑_j R_j` average in
Eq. (15.5) when all risks coincide.

## Proof (verbatim)

Bach §15.1.2 (p. 430), Eq. (15.5):

> "inf_A sup_{θ* ∈ Θ} E_{θ*}[ δ(θ*, A(D))² ]
>    ≥ A · inf_h (1/M) ∑_{j=1}^M P_{θ_j}( h(D) ≠ j ),     (15.5)"

When all `P_{θ_j}(h(D) ≠ j)` coincide (e.g., a symmetric configuration),
the average equals each summand.

## Notes

- **Bach's technique in one line:** `(R + R)/2 = R` is `by ring`.
- Used as a sanity / boundary anchor; the registry uses it to make
  sure the symmetric-configuration case reduces cleanly.

## Prerequisites (Bach's dependency graph)

- [`le-cam-average`](./le-cam-average.md) — Le Cam-style average ≤ max two-point inequality

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch15_LowerBounds/Statistical.lean`
- **Theorem/def name:** `average_of_self`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

