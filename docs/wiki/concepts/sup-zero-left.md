# max(0, R) = R when R ≥ 0

**ID:** `sup-zero-left`  
**Chapter:** Ch15 (Bach §15.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/sup-zero-left/`](../../../tasks/sup-zero-left/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — max(0, R) = R when R ≥ 0

**Concept ID:** `sup-zero-left`
**Chapter:** Ch 15
**Section:** §15.1 (testing error nonneg + max identity)
**Pages:** 429-431 (book) / 445-447 (PDF)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Carrier `LTFP.Ch15_LowerBounds.Statistical.sup_zero_left`. Algebraic
anchor: nonneg testing error R satisfies `max(0, R) = R`.

> For any `R ≥ 0`,
>
>     max(0, R)  =  R.

Used silently in Bach's lower-bound chain whenever an `inf` over the
algorithm class is taken — the lower bound on the inf is at most 0
trivially (since a constant algorithm achieves some finite error), so
`max(0, lower bound) = lower bound` when the bound is nonneg.

## Proof (verbatim)

Bach §15.1.2 (p. 429-430), discussing the lower-bound chain after
Eq. (15.2):

> "Since by Markov's inequality,
>   E_{θ*}[δ(θ*, A(D))²] · 𝟙{δ(θ*,A(D))² > A} ≥ A · P_{θ*}(δ(θ*,A(D))² > A),
> up to multiplicative constants, it is sufficient to lower-bound
>
>     inf_A sup_{θ* ∈ Θ} P_{θ*}( δ(θ*, A(D))² > A )                (15.2)
>
> for some arbitrary A > 0."

Throughout this construction, the lower bound stays in [0, 1] (it is a
probability) and the testing error stays in [0, ∞) (it is an
expectation of a nonneg quantity), so the `max(0, ·)` step is trivial.

## Notes

- **Bach's technique in one line:** `R ≥ 0 ⇒ max(0, R) = R`, a Lean
  one-liner via `max_eq_right`.
- Used to keep the registry strict about nonnegativity invariants
  flowing through the Fano chain.

## Prerequisites (Bach's dependency graph)

- [`testing-error-nonneg`](./testing-error-nonneg.md) — Statistical lower-bound anchor: testing error nonneg

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch15_LowerBounds/Statistical.lean`
- **Theorem/def name:** `sup_zero_left`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

