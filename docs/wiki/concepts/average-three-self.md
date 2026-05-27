# Average of three identical risks = R

**ID:** `average-three-self`  
**Chapter:** Ch15 (Bach §15.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/average-three-self/`](../../../tasks/average-three-self/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Average of three identical risks = R

**Concept ID:** `average-three-self`
**Chapter:** Ch 15
**Section:** §15.1.2 (Eq. 15.5) — M = 3 degenerate
**Pages:** 430-431 (book) / 446-447 (PDF)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Carrier `LTFP.Ch15_LowerBounds.Statistical.average_three_self`. Trivial
average identity at M = 3:

> For any `R`,
>
>     (R + R + R) / 3  =  R.

Boundary case of `(1/M) ∑_{j=1}^M R_j` for M = 3 with identical risks.

## Proof (verbatim)

Bach §15.1.2 (p. 430), Eq. (15.5):

> "inf_A sup_{θ* ∈ Θ} E_{θ*}[ δ(θ*, A(D))² ]
>    ≥ A · inf_h (1/M) ∑_{j=1}^M P_{θ_j}( h(D) ≠ j ),     (15.5)"

At M = 3 with all probabilities equal, the average equals each summand.

## Notes

- **Bach's technique in one line:** `(R+R+R)/3 = R` is `by ring`.
- Boundary anchor mirroring `average-of-self` (M = 2) at M = 3.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch15_LowerBounds/Statistical.lean`
- **Theorem/def name:** `average_three_self`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

