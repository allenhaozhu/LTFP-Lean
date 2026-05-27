# Triangle inequality for expectation |E[X]| ≤ E[|X|]

**ID:** `abs-expectation-le-exp-abs`  
**Chapter:** Ch05 (Bach §F9)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/abs-expectation-le-exp-abs/`](../../../tasks/abs-expectation-le-exp-abs/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Triangle inequality for expectation |E[X]| ≤ E[|X|]

**Concept ID:** `abs-expectation-le-exp-abs`
**Chapter:** Ch 5
**Section:** §5.4 / Foundation F9 (Jensen-type expectation inequality)
**Pages:** 117-118 (Jensen reference), 134-138 (SGD application)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For any integrable random variable $X$,
$$|\mathbb{E}[X]| \le \mathbb{E}[|X|].$$
This is the triangle / Jensen inequality for expectations (apply
**Proposition 5.1 (Jensen's inequality)** with the convex function $|\cdot|$).

Bach states Proposition 5.1 (PDF p. 134): "If $F:\mathbb{R}^d\to\mathbb{R}$ is
convex and $\mu$ is a probability measure on $\mathbb{R}^d$, then
$F(\int \theta\, d\mu) \le \int F(\theta)\, d\mu$" (eq. 5.8). The special case
$F = |\cdot|$ gives the desired inequality.

## Proof (verbatim)

Bach defers Jensen's inequality to standard references; the special case for
absolute value is immediate by the convexity of $x \mapsto |x|$ on $\mathbb{R}$
applied to Proposition 5.1.

## Notes

- Mathlib: `MeasureTheory.abs_integral_le_integral_abs`.
- Prerequisite for `abs-expectation-bounded`: combine with
  `expectation-le-const` to obtain "$|X|\le B$ a.s. $\Rightarrow |\mathbb{E}[X]|\le B$."
- Bach warns about the direction of Jensen's inequality (PDF p. 134).

## Prerequisites (Bach's dependency graph)

- [`expectation-nonneg`](./expectation-nonneg.md) — Expectation of nonneg function is nonneg

## Dependents (concepts that use this)

- [`abs-expectation-bounded`](./abs-expectation-bounded.md) — Bounded RV: |X| ≤ B ⇒ |E[X]| ≤ B

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/MeasureProb.lean`
- **Theorem/def name:** `abs_expectation_le_expectation_abs`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

