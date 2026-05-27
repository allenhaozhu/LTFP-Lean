# E[c] = c under probability measure

**ID:** `expectation-const`  
**Chapter:** Ch05 (Bach §F9)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/expectation-const/`](../../../tasks/expectation-const/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — E[c] = c under probability measure

**Concept ID:** `expectation-const`
**Chapter:** Ch 5
**Section:** §5.4 / Foundation F9 (expectation prerequisite)
**Pages:** 117-118, 134-138 (book); foundation lemma for Proposition 5.7
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For a probability measure $\mu$ on $\mathbb{R}^d$ and constant $c$,
$$\int_{\mathbb{R}^d} c \, d\mu = c.$$
Equivalently, $\mathbb{E}[c] = c$.

Bach uses this implicitly throughout the SGD chapter (e.g. when taking
expectations of $\|\theta_{t-1} - \theta_*\|_2^2$ telescoping sums in the
proof of Proposition 5.7), citing it as a standard property of probability
measures without proof.

## Proof (verbatim)

Bach defers to standard measure-theoretic probability: by definition,
$\int c\, d\mu = c \cdot \mu(\mathbb{R}^d) = c \cdot 1 = c$ for a probability
measure $\mu$.

## Notes

- Mathlib: `MeasureTheory.integral_const` / `ProbabilityTheory.expectation_const`.
- Lean form: `∫ _, c ∂μ = c` when `IsProbabilityMeasure μ`.
- A building block for `expectation-le-const` and `expectation-ge-const`,
  which then combine into `expectation-in-interval` and `abs-expectation-bounded`.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

- [`expectation-ge-const`](./expectation-ge-const.md) — Lower bound: m ≤ X ⇒ m ≤ E[X]
- [`expectation-le-const`](./expectation-le-const.md) — Expectation bounded by a sup constant

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/MeasureProb.lean`
- **Theorem/def name:** `expectation_const`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

