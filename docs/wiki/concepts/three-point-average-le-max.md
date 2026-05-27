# Three-point Le Cam: average ≤ max

**ID:** `three-point-average-le-max`  
**Chapter:** Ch15 (Bach §15.1.4)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Le Cam`

## Statement

_See textbook excerpt below or [`tasks/three-point-average-le-max/`](../../../tasks/three-point-average-le-max/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Three-point Le Cam: average ≤ max

**Concept ID:** `three-point-average-le-max`
**Chapter:** Ch 15
**Section:** §15.1.2 (Eq. 15.5) — M-point generalization, instantiated at M=3
**Pages:** 430-431 (book) / 446-447 (PDF)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Carrier `LTFP.Ch15_LowerBounds.Statistical.threePoint_average_le_max`.
Three-point instance of Bach's M-hypothesis chain (Eq. 15.5):

> For real risks `R₁, R₂, R₃`,
>
>     (R₁ + R₂ + R₃)/3  ≤  max(R₁, max(R₂, R₃)).

This is the M = 3 case of `(1/M) ∑_j P_{θ_j}(h(D) ≠ j) ≤ max_j P_{θ_j}(h(D) ≠ j)`
used by Bach to land the Fano-amenable form on the right-hand side of
Eq. 15.5.

## Proof (verbatim)

Bach §15.1.2 (p. 430), Eq. (15.5) — same passage as `le-cam-average`:

> "inf_A sup_{θ* ∈ Θ} E_{θ*}[ δ(θ*, A(D))² ]
>    ≥ A · inf_h max_{j ∈ {1,…,M}} P_{θ_j}( h(D) ≠ j )
>    ≥ A · inf_h (1/M) ∑_{j=1}^M P_{θ_j}( h(D) ≠ j ),     (15.5)"

The chain `max ≥ avg` holds for any M. Project anchor specializes to
M = 3 because some downstream applications (e.g., ternary classification
lower bounds) want a numerical bound with three distinguished
parameters.

## Notes

- **Bach's technique in one line:** `max_j R_j ≥ (1/M) ∑_j R_j`
  trivially; here M = 3.
- Specialization is convenient for the 3-arm bandit lower bound
  application (Ch 11) which uses ternary parameters.
- The Lean proof reduces by `linarith` after expanding `max`.

## Prerequisites (Bach's dependency graph)

- [`le-cam-average`](./le-cam-average.md) — Le Cam-style average ≤ max two-point inequality

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch15_LowerBounds/Statistical.lean`
- **Theorem/def name:** `threePoint_average_le_max`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

