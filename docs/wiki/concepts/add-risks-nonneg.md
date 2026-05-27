# Sum of nonneg risks is nonneg

**ID:** `add-risks-nonneg`  
**Chapter:** Ch15 (Bach §15.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/add-risks-nonneg/`](../../../tasks/add-risks-nonneg/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Sum of nonneg risks is nonneg

**Concept ID:** `add-risks-nonneg`
**Chapter:** Ch 15
**Section:** §15.1 — preservation of nonneg under addition
**Pages:** 428-431 (book) / 444-447 (PDF)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Carrier `LTFP.Ch15_LowerBounds.Statistical.add_risks_nonneg`. Trivial
preservation lemma: nonneg testing errors add to nonneg quantities.

> If `R₁ ≥ 0` and `R₂ ≥ 0`, then `R₁ + R₂ ≥ 0`.

## Proof (verbatim)

Bach §15.1.2 (p. 430), forming the sum `∑_{j=1}^M P_{θ_j}(h(D) ≠ j)`
inside Eq. (15.5):

> "inf_A sup_{θ* ∈ Θ} E_{θ*}[ δ(θ*, A(D))² ]
>    ≥ A · inf_h (1/M) ∑_{j=1}^M P_{θ_j}( h(D) ≠ j )"

Each summand is a probability hence ≥ 0; the sum is ≥ 0 by linearity.

## Notes

- **Bach's technique in one line:** the sum of two nonneg reals is
  nonneg — `add_nonneg` in Lean.
- Used as a structural lemma when chaining Fano applications across
  multiple hypothesis sub-tests.

## Prerequisites (Bach's dependency graph)

- [`testing-error-nonneg`](./testing-error-nonneg.md) — Statistical lower-bound anchor: testing error nonneg

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch15_LowerBounds/Statistical.lean`
- **Theorem/def name:** `add_risks_nonneg`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

