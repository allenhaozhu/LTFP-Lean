# max R R = average R R

**ID:** `max-eq-avg-equal`  
**Chapter:** Ch15 (Bach §15.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/max-eq-avg-equal/`](../../../tasks/max-eq-avg-equal/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — max R R = average R R

**Concept ID:** `max-eq-avg-equal`
**Chapter:** Ch 15
**Section:** §15.1.2 (Eq. 15.5) — degenerate case
**Pages:** 430-431 (book) / 446-447 (PDF)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Carrier `LTFP.Ch15_LowerBounds.Statistical.max_eq_average_when_equal`.
Algebraic identity when the two risks coincide:

> For any `R`,
>
>     max(R, R)  =  (R + R) / 2.

This is the degenerate-case equality `max R R = R = (R + R)/2`.

## Proof (verbatim)

Bach §15.1.2 (p. 430), Eq. (15.5):

> "inf_A sup_{θ* ∈ Θ} E_{θ*}[ δ(θ*, A(D))² ]
>    ≥ A · inf_h max_{j ∈ {1,…,M}} P_{θ_j}( h(D) ≠ j )
>    ≥ A · inf_h (1/M) ∑_{j=1}^M P_{θ_j}( h(D) ≠ j ),     (15.5)"

The two inequalities become equalities exactly when all per-hypothesis
risks coincide — this anchor captures that boundary.

## Notes

- **Bach's technique in one line:** `max R R = R = (R+R)/2` is `by ring`
  after unfolding `max_self`.
- Establishes that the Le Cam-style upper bound is *tight* on
  symmetric configurations, which Bach exploits in the volume / packing
  arguments (§15.1.5).

## Prerequisites (Bach's dependency graph)

- [`le-cam-average`](./le-cam-average.md) — Le Cam-style average ≤ max two-point inequality

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch15_LowerBounds/Statistical.lean`
- **Theorem/def name:** `max_eq_average_when_equal`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

