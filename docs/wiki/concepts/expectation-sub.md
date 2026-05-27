# E[X - Y] = E[X] - E[Y]

**ID:** `expectation-sub`  
**Chapter:** Ch05 (Bach §F9)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/expectation-sub/`](../../../tasks/expectation-sub/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — E[X - Y] = E[X] - E[Y]

**Concept ID:** `expectation-sub`
**Chapter:** Ch 5
**Section:** §5.4 / Foundation F9 (expectation prerequisite)
**Pages:** 134-138 (book)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For integrable $X, Y$:
$$\mathbb{E}[X - Y] = \mathbb{E}[X] - \mathbb{E}[Y].$$
A consequence of `expectation-add` and `expectation-neg`.

Used in Proposition 5.7's proof when isolating the Lyapunov decrement
$\mathbb{E}\|\theta_{t-1}-\theta_*\|_2^2 - \mathbb{E}\|\theta_t - \theta_*\|_2^2$
to telescope across iterations (PDF p. 153).

## Proof (verbatim)

$X - Y = X + (-Y)$, then apply `expectation-add` and `expectation-neg`.

## Notes

- Mathlib: `MeasureTheory.integral_sub`.
- Trivial corollary; included as a foundation lemma to align rewrites where
  the canonical form is subtraction rather than addition of negation.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/MeasureProb.lean`
- **Theorem/def name:** `expectation_sub`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

