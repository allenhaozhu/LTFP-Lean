# |0| = 0

**ID:** `abs-zero-eq-zero`  
**Chapter:** Ch01 (Bach §F10)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/abs-zero-eq-zero/`](../../../tasks/abs-zero-eq-zero/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — |0| = 0

**Concept ID:** `abs-zero-eq-zero`
**Chapter:** Ch 1
**Section:** F10 (foundational alias)
**Pages:** n/a (Bach uses implicitly; not stated as a named proposition)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach does not state this as a named proposition. It is a standard real-analysis
prerequisite that Bach uses implicitly. The Mathlib-equivalent statement is:

```
|0| = 0
```

(Mathlib lemma: `abs_zero`.)

## Proof (verbatim)

Bach gives no proof; he treats this as a standard real-analysis fact. Bach defers to
the standard literature for the underlying real-analysis machinery (he mentions
Boucheron–Lugosi–Massart (2013) and Vershynin (2018) as general references in §1.2).

## Notes

- Standard absolute-value normalization used implicitly throughout.
- This is an "F10 alias" concept — registered for traceability in the LTFP-Lean
  concept graph but not corresponding to a named Bach theorem.
- Lean target: forward the corresponding Mathlib lemma (`abs_zero`).

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/MathlibAliases.lean`
- **Theorem/def name:** `abs_zero_eq_zero`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

