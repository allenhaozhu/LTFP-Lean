# E[c·X] = c·E[X] (linearity in scalar)

**ID:** `expectation-smul`  
**Chapter:** Ch05 (Bach §F9)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/expectation-smul/`](../../../tasks/expectation-smul/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — E[c·X] = c·E[X] (linearity in scalar)

**Concept ID:** `expectation-smul`
**Chapter:** Ch 5
**Section:** §5.4 / Foundation F9 (expectation prerequisite)
**Pages:** 134-138 (book); used implicitly in SGD proofs
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For scalar $c \in \mathbb{R}$ and integrable random variable $X$,
$$\mathbb{E}[c \cdot X] = c \cdot \mathbb{E}[X].$$

Bach uses this property silently throughout Section 5.4 — most prominently
when pulling step-size factors $\gamma_t$ outside expectations in the proof
of Proposition 5.7 (PDF pp. 152-153).

## Proof (verbatim)

Standard property of the Lebesgue / Bochner integral; Bach treats it as
background and does not prove it.

## Notes

- Mathlib: `MeasureTheory.integral_smul`, `MeasureTheory.integral_const_mul`.
- Half of the linearity of expectation; pairs with `expectation-add` for full
  $\mathbb{R}$-linearity.
- Required to derive
  $\mathbb{E}[\gamma_t g_t(\theta_{t-1})^\top(\theta_{t-1}-\theta_*)] = \gamma_t \cdot \mathbb{E}[g_t(\theta_{t-1})^\top(\theta_{t-1}-\theta_*)]$
  in Bach's proof of Proposition 5.7.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/MeasureProb.lean`
- **Theorem/def name:** `expectation_smul`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

