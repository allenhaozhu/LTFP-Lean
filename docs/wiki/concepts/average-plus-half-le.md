# (R₁+R₂)/2 + R₃/2 ≤ max(R₁,R₂) + R₃/2

**ID:** `average-plus-half-le`  
**Chapter:** Ch15 (Bach §15.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/average-plus-half-le/`](../../../tasks/average-plus-half-le/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — (R₁+R₂)/2 + R₃/2 ≤ max(R₁,R₂) + R₃/2

**Concept ID:** `average-plus-half-le`
**Chapter:** Ch 15
**Section:** §15.1.2 / §15.1.4 (composite Le Cam / 3-point bounds)
**Pages:** 430-434 (book) / 446-450 (PDF)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Carrier `LTFP.Ch15_LowerBounds.Statistical.average_plus_half_le`.
Composite algebraic anchor: replacing the average of `R₁, R₂` by their
maximum in a sum.

> For real `R₁, R₂, R₃`,
>
>     (R₁ + R₂)/2 + R₃/2  ≤  max(R₁, R₂) + R₃/2.

## Proof (verbatim)

The base inequality is Bach's `(R₁+R₂)/2 ≤ max(R₁,R₂)` (Eq. 15.5,
captured in `le-cam-average`). Adding `R₃/2` to both sides preserves
the inequality. Bach uses this composite form when partial sums of the
`(1/M) ∑_j` average in Eq. 15.5 are bounded by maximums over subsets.

Bach §15.1.2 (p. 430), Eq. (15.5):

> "inf_A sup_{θ* ∈ Θ} E_{θ*}[ δ(θ*, A(D))² ]
>    ≥ A · inf_h max_{j ∈ {1,…,M}} P_{θ_j}( h(D) ≠ j )
>    ≥ A · inf_h (1/M) ∑_{j=1}^M P_{θ_j}( h(D) ≠ j ),     (15.5)"

## Notes

- **Bach's technique in one line:** `avg(R₁,R₂) ≤ max(R₁,R₂)` plus an
  invariant additive term — `by linarith`.
- This composite is useful when a third hypothesis is held aside and
  averaged separately from a max-bounded pair.

## Prerequisites (Bach's dependency graph)

- [`le-cam-average`](./le-cam-average.md) — Le Cam-style average ≤ max two-point inequality

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch15_LowerBounds/Statistical.lean`
- **Theorem/def name:** `average_plus_half_le`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

