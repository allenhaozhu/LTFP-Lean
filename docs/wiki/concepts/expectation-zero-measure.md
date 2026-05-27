# Expectation under zero measure is zero

**ID:** `expectation-zero-measure`  
**Chapter:** Ch05 (Bach §F9)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/expectation-zero-measure/`](../../../tasks/expectation-zero-measure/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Expectation under zero measure is zero

**Concept ID:** `expectation-zero-measure`
**Chapter:** Ch 5
**Section:** Foundation F9 (boundary case)
**Pages:** N/A (technical lemma, not in Bach's prose)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For any measurable function $X$ and the zero measure $\mu = 0$:
$$\int X \, d 0 = 0.$$

Bach does not state this — it is a measure-theoretic boundary case used only
to discharge degenerate cases in Lean proofs (e.g., when generalizing a result
to arbitrary measures and then specializing back to probability measures).

## Proof (verbatim)

By definition of integration with respect to the zero measure; every simple
function integrates to $0$, hence so does every limit of simple functions.

## Notes

- Mathlib: `MeasureTheory.integral_zero_measure`.
- Pure boundary lemma; not used in Bach's analytic proofs but required for the
  Lean type-level abstraction.
- Allows stating SGD lemmas for arbitrary measures and specialising to
  probability measures (or empirical distributions) without case-splits.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/MeasureProb.lean`
- **Theorem/def name:** `expectation_zero_measure`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

