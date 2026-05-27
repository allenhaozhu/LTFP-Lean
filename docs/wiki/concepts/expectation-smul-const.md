# E[c·0] = 0

**ID:** `expectation-smul-const`  
**Chapter:** Ch05 (Bach §F9)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/expectation-smul-const/`](../../../tasks/expectation-smul-const/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — E[c·0] = 0

**Concept ID:** `expectation-smul-const`
**Chapter:** Ch 5
**Section:** §5.4 / Foundation F9 (composition of expectation-smul with expectation-zero-fn)
**Pages:** 134-138 (book)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For any scalar $c$, $\mathbb{E}[c \cdot 0] = c \cdot \mathbb{E}[0] = c \cdot 0 = 0$.
Composition of `expectation-smul` with `expectation-zero-fn`.

## Proof (verbatim)

Chain: by `expectation-smul`, $\mathbb{E}[c\cdot 0] = c\cdot\mathbb{E}[0]$;
by `expectation-zero-fn`, $\mathbb{E}[0] = 0$; hence the product is $0$.

## Notes

- Trivial composite; included as a one-shot rewrite to keep Lean proofs concise
  when scalar-multiplying degenerate (zero) random variables.
- No direct Mathlib equivalent — derived by composition.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/MeasureProb.lean`
- **Theorem/def name:** `expectation_smul_const`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

