# Expectation of nonneg function is nonneg

**ID:** `expectation-nonneg`  
**Chapter:** Ch05 (Bach §F9)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/expectation-nonneg/`](../../../tasks/expectation-nonneg/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Expectation of nonneg function is nonneg

**Concept ID:** `expectation-nonneg`
**Chapter:** Ch 5
**Section:** §5.4 / Foundation F9 (expectation prerequisite)
**Pages:** 134-138 (book)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For a measurable function $X \ge 0$ a.s. and any measure $\mu$,
$$\mathbb{E}[X] = \int X \, d\mu \ge 0.$$

Bach treats this monotone property of the integral as background. It surfaces
indirectly when he writes (PDF p. 153) bounds like
$\mathbb{E}\|\theta_t - \theta_*\|_2^2 \ge 0$ to drop nonnegative terms from
inequality chains.

## Proof (verbatim)

Standard measure-theoretic property; Bach does not give a proof.

## Notes

- Mathlib: `MeasureTheory.integral_nonneg`.
- Crucial step in deriving `abs-expectation-le-exp-abs` (Jensen / triangle for
  expectation) since $|X| \ge 0$ implies $\mathbb{E}[|X|] \ge 0$.
- Combined with `expectation-mono` for one-sided bounds like
  `expectation-ge-const` and `expectation-le-const`.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

- [`abs-expectation-le-exp-abs`](./abs-expectation-le-exp-abs.md) — Triangle inequality for expectation |E[X]| ≤ E[|X|]
- [`pop-risk-nonneg`](./pop-risk-nonneg.md) — populationRisk of nonneg loss is nonneg

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/MeasureProb.lean`
- **Theorem/def name:** `expectation_nonneg`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

