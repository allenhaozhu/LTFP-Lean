# E[0] = 0

**ID:** `expectation-zero-fn`  
**Chapter:** Ch05 (Bach §F9)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/expectation-zero-fn/`](../../../tasks/expectation-zero-fn/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — E[0] = 0

**Concept ID:** `expectation-zero-fn`
**Chapter:** Ch 5
**Section:** §5.4 / Foundation F9 (boundary case of expectation-const)
**Pages:** 134-138 (book)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For any measure $\mu$ (in particular any probability measure),
$$\mathbb{E}[0] = \int 0 \, d\mu = 0.$$
Special case of `expectation-const` with $c = 0$.

## Proof (verbatim)

Special case of `expectation-const` (or directly: the integral of the zero
function is zero for any measure).

## Notes

- Mathlib: `MeasureTheory.integral_zero`.
- Holds even without `IsProbabilityMeasure` (unlike `expectation-const` which
  needs the measure to have unit total mass).
- Used as a base case / identity element in expectation rewrites.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/MeasureProb.lean`
- **Theorem/def name:** `expectation_zero_fn`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

