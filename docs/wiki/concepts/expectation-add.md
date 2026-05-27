# E[X + Y] = E[X] + E[Y]

**ID:** `expectation-add`  
**Chapter:** Ch05 (Bach §F9)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/expectation-add/`](../../../tasks/expectation-add/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — E[X + Y] = E[X] + E[Y]

**Concept ID:** `expectation-add`
**Chapter:** Ch 5
**Section:** §5.4 / Foundation F9 (expectation prerequisite)
**Pages:** 134-138 (book)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Linearity of expectation: for integrable random variables $X, Y$,
$$\mathbb{E}[X + Y] = \mathbb{E}[X] + \mathbb{E}[Y].$$

Bach uses additivity extensively in the SGD proof — most directly when
expanding $\mathbb{E}\|\theta_t - \theta_*\|_2^2$ into three pieces:
$\mathbb{E}\|\theta_{t-1}-\theta_*\|_2^2 - 2\gamma_t \mathbb{E}[g_t(\theta_{t-1})^\top(\theta_{t-1}-\theta_*)] + \gamma_t^2 \mathbb{E}\|g_t(\theta_{t-1})\|_2^2$
(PDF p. 153, proof of Proposition 5.7).

## Proof (verbatim)

Standard property of the Lebesgue integral; Bach defers to background.

## Notes

- Mathlib: `MeasureTheory.integral_add`.
- The "horizontal" half of linearity; pairs with `expectation-smul` for full
  $\mathbb{R}$-linearity.
- Used in the Lyapunov-function telescoping step that sums (5.25) over $t$
  in the proof of Proposition 5.7.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/MeasureProb.lean`
- **Theorem/def name:** `expectation_add`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

