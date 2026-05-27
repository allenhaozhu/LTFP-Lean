# Statistical lower-bound anchor: testing error nonneg

**ID:** `testing-error-nonneg`  
**Chapter:** Ch15 (Bach §15.1, p. 428)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/testing-error-nonneg/`](../../../tasks/testing-error-nonneg/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Statistical lower-bound anchor: testing error nonneg

**Concept ID:** `testing-error-nonneg`
**Chapter:** Ch 15
**Section:** §15.1 / §15.1.1 (Minimax Lower Bounds)
**Pages:** 428-429 (book) / 444-445 (PDF)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Carrier `LTFP.Ch15_LowerBounds.Statistical.testing_error_nonneg`. The
testing error of an algorithm A under hypothesis θ* is a (squared)
distance expectation and therefore nonneg:

> `E_{θ*}[ δ(θ*, A(D))² ]  ≥  0`.

In the Lean reduction, this collapses to: `∀ p ≥ 0, 0 ≤ p`, which is
the trivial nonnegativity preserved through Bach's minimax-error
construction.

## Proof (verbatim)

Bach §15.1.1 (p. 429), introducing the testing error:

> "We consider an estimator A(D) of θ ∈ Θ, with some squared distance
> δ² between two elements of Θ, so δ(θ, θ')² measures the performance
> of θ' when the true estimator is θ.
>
> The testing error of A when the data D come from θ* is defined as
>
>     E_{θ*}[ δ(θ*, A(D))² ].
>
> The goal is to find an algorithm so `sup_{θ* ∈ Θ} E_{θ*}[ δ(θ*, A(D))² ]`
> is as small as possible, and the lower bound on testing error is thus
>
>     inf_A sup_{θ* ∈ Θ} E_{θ*}[ δ(θ*, A(D))² ].                  (15.1)
>
> This is often referred to as 'minimax' lower bounds."

The nonnegativity is implicit — `δ² ≥ 0` pointwise, and expectation
preserves nonnegativity. Bach uses this without comment whenever he
writes "the lower bound on testing error is greater than…" (e.g.
Eq. 15.10 on p. 437).

## Notes

- This is the **foundation anchor** of §15.1: every downstream theorem
  (`twoPoint_sup_lower_bound`, `leCam_average_le_max`,
  `average_le_sup`, etc.) treats testing error as a nonneg real.
- **Bach's technique in one line:** `δ²` is a squared (semi)distance,
  hence nonneg, hence its expectation is nonneg.
- The Lean reduction `theorem testing_error_nonneg (p : ℝ) (h : 0 ≤ p) : 0 ≤ p`
  is the *type-level* anchor — it captures that, downstream, every
  bound chain enters the registry as a nonneg real.
- Used in: Cor 15.1 proof (p. 434), Eq. 15.10 (p. 437), and every
  example in §15.1.5.

## Prerequisites (Bach's dependency graph)

- [`infotheory-foundation`](./infotheory-foundation.md) — Information-theory foundation: KL divergence wrapper

## Dependents (concepts that use this)

- [`add-risks-nonneg`](./add-risks-nonneg.md) — Sum of nonneg risks is nonneg
- [`max-self-anchor`](./max-self-anchor.md) — max R R = R (anchor)
- [`risk-half-le-one`](./risk-half-le-one.md) — Risk ≤ 1/2 implies risk ≤ 1
- [`sup-singleton`](./sup-singleton.md) — Sup of single-element risk = element
- [`sup-zero-left`](./sup-zero-left.md) — max(0, R) = R when R ≥ 0
- [`testing-error-diff-bound`](./testing-error-diff-bound.md) — Testing error difference ≤ 1
- [`testing-error-le-one`](./testing-error-le-one.md) — Testing error rate is at most 1
- [`two-point-sup-lb`](./two-point-sup-lb.md) — Two-point lower-bound template (sup ≥ min)
- [`two-testing-errors-le-two`](./two-testing-errors-le-two.md) — Sum of two testing errors ≤ 2

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch15_LowerBounds/Statistical.lean`
- **Theorem/def name:** `testing_error_nonneg`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

