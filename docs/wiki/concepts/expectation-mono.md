# Expectation is monotone

**ID:** `expectation-mono`  
**Chapter:** Ch05 (Bach §F9)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/expectation-mono/`](../../../tasks/expectation-mono/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Expectation is monotone

**Concept ID:** `expectation-mono`
**Chapter:** Ch 5
**Section:** §5.4 / Foundation F9 (expectation prerequisite)
**Pages:** 134-138 (book)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

If $X \le Y$ almost surely (and both are integrable), then $\mathbb{E}[X] \le \mathbb{E}[Y]$.

Bach uses monotonicity of expectation whenever he applies an a.s. pointwise
bound under the integral sign — for example, applying the bounded-estimator
hypothesis (H-2) $\|g_t(\theta_{t-1})\|_2^2 \le B^2$ a.s. yields
$\mathbb{E}\|g_t(\theta_{t-1})\|_2^2 \le B^2$ (PDF p. 153).

## Proof (verbatim)

Standard property of the integral via $Y - X \ge 0 \Rightarrow \mathbb{E}[Y-X] \ge 0$
combined with linearity. Bach treats as background.

## Notes

- Mathlib: `MeasureTheory.integral_mono` (and a.e. variants).
- Fundamental ingredient for all "constant-bound" expectation lemmas
  (`expectation-le-const`, `expectation-ge-const`, `expectation-in-interval`,
  `abs-expectation-bounded`).
- Combined with `expectation-const` gives "if $X \le c$ a.s. then $\mathbb{E}[X] \le c$."

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

- [`expectation-ge-const`](./expectation-ge-const.md) — Lower bound: m ≤ X ⇒ m ≤ E[X]
- [`expectation-le-const`](./expectation-le-const.md) — Expectation bounded by a sup constant

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/MeasureProb.lean`
- **Theorem/def name:** `expectation_mono`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

