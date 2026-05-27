# Sup of single-element risk = element

**ID:** `sup-singleton`  
**Chapter:** Ch15 (Bach §15.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/sup-singleton/`](../../../tasks/sup-singleton/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Sup of single-element risk = element

**Concept ID:** `sup-singleton`
**Chapter:** Ch 15
**Section:** §15.1 / §15.1.1
**Pages:** 428-429 (book) / 444-445 (PDF)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Carrier `LTFP.Ch15_LowerBounds.Statistical.sup_singleton_anchor`.
Trivial algebraic anchor used in the M = 1 degenerate case of Bach's
minimax construction:

>     max(R, R)  =  R.

This is the boundary case of `sup_{θ* ∈ Θ} E_{θ*}[δ²]` when Θ collapses
to a single point.

## Proof (verbatim)

Bach §15.1.1 (p. 428-429), introducing the minimax formulation:

> "The goal is to find an algorithm so `sup_{θ* ∈ Θ} E_{θ*}[ δ(θ*, A(D))² ]`
> is as small as possible, and the lower bound on testing error is thus
>
>     inf_A sup_{θ* ∈ Θ} E_{θ*}[ δ(θ*, A(D))² ].                  (15.1)"

When `|Θ| = 1`, the supremum is the unique element. Bach does not
spell this out, but it is implicit in the M-point analysis (M ≥ 2 is
the nontrivial regime; M = 1 reduces to the trivial single-distribution
testing problem).

## Notes

- **Bach's technique in one line:** `max R R = R` (Lean: `max_self _`).
- Provided as an algebraic anchor for completeness of the registry;
  downstream users who treat the singleton case as a special boundary
  cite it.

## Prerequisites (Bach's dependency graph)

- [`testing-error-nonneg`](./testing-error-nonneg.md) — Statistical lower-bound anchor: testing error nonneg

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch15_LowerBounds/Statistical.lean`
- **Theorem/def name:** `sup_singleton_anchor`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

