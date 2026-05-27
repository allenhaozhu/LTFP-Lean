# populationRisk under zero measure = 0

**ID:** `pop-risk-zero-measure`  
**Chapter:** Ch02 (Bach §2.2.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/pop-risk-zero-measure/`](../../../tasks/pop-risk-zero-measure/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — populationRisk under zero measure = 0

**Concept ID:** `pop-risk-zero-measure`
**Chapter:** Ch 2
**Section:** 2.2.2 (degenerate boundary case)
**Pages:** 27
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

From Definition 2.1 (p. 27):

>     R(f) = ∫_{X × Y} ℓ(y, f(x)) dp(x, y).

If the distribution `p` is the **zero measure** (degenerate boundary case),
the integral collapses to zero:

    populationRisk ℓ f (0 : Measure (X × Y)) = ∫ _ ∂0 = 0.

Bach does not discuss this case (it is not a probability measure), but the
Lean library tracks it as a sanity-check lemma — the formal `MeasureTheory.integral`
extends to all `Measure`, and the zero measure gives zero integral.

## Proof (verbatim)

(Not in Bach.) In Lean / Mathlib:
`MeasureTheory.integral_zero_measure : ∫ x, f x ∂(0 : Measure α) = 0`.

## Notes

- Boundary-case lemma; not used in Bach's analysis (he only considers
  probability measures).
- Useful in Lean to confirm `populationRisk` is well-defined on the full
  `Measure` type, not just `ProbabilityMeasure`.
- One-line discharge via `MeasureTheory.integral_zero_measure`.

## Prerequisites (Bach's dependency graph)

- [`population-risk`](./population-risk.md) — Population risk R(f) = E[ℓ(f(x), y)]

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch02_SupervisedLearning/Defs.lean`
- **Theorem/def name:** `populationRisk_zero_measure`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

