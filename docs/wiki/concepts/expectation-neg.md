# E[-X] = -E[X]

**ID:** `expectation-neg`  
**Chapter:** Ch05 (Bach §F9)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/expectation-neg/`](../../../tasks/expectation-neg/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — E[-X] = -E[X]

**Concept ID:** `expectation-neg`
**Chapter:** Ch 5
**Section:** §5.4 / Foundation F9 (expectation prerequisite)
**Pages:** 134-138 (book)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For integrable $X$: $\mathbb{E}[-X] = -\mathbb{E}[X]$. Special case of
`expectation-smul` with scalar $-1$.

Used silently throughout the SGD chapter: any sign flip in a Lyapunov
inequality (e.g. when isolating $-\gamma_t F'(\theta_{t-1})^\top(\theta_{t-1}-\theta_*)$
in the proof of Proposition 5.7) implicitly invokes this property.

## Proof (verbatim)

Special case of `expectation-smul` (linearity in scalar) with $c = -1$.

## Notes

- Mathlib: `MeasureTheory.integral_neg`.
- Trivial corollary; included as a foundation rewrite lemma for canonical
  Lean tactic forms.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/MeasureProb.lean`
- **Theorem/def name:** `expectation_neg`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

