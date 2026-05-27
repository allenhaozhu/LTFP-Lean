# Universal consistency of a learning algorithm

**ID:** `consistency`  
**Chapter:** Ch02 (Bach §2.4.2, p. 36)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/consistency/`](../../../tasks/consistency/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Universal consistency of a learning algorithm

**Concept ID:** `consistency`
**Chapter:** Ch 2
**Section:** 2.4.1 (Measures of Performance) and 2.4.2 (Notions of Consistency over Classes of Problems)
**Pages:** 36-37
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

**Consistency in expectation, §2.4.1 (p. 36):**

> Expected error: we measure performance as
>
>     E[ R_p( A(D_n(p)) ) ],
>
> where the expectation is with respect to the training data. Algorithm `A` is called
> consistent in expectation for distribution `p`, if
>
>     E[ R_p( A(D_n(p)) ) ] − R∗_p
>
> goes to zero when `n` tends to infinity. In this book, we will primarily use this
> notion of consistency.

**PAC consistency (alternative formulation), p. 36:**

> Probably approximately correct (PAC) learning: for a given `δ ∈ (0,1)` and `ε > 0`:
>
>     P( R_p(A(D_n(p))) − R∗_p ≤ ε ) ≥ 1 − δ.
>
> The notion of PAC consistency corresponds, for any `ε > 0`, to have such an
> inequality for each `n` and a sequence `δ_n` that tends to zero.

**Universal consistency, §2.4.2 (p. 36):**

> An algorithm is called universally consistent (in expectation) if for all
> probability distributions `p = p_{(x,y)}` on `(x, y)`, algorithm `A` is consistent
> in expectation for the distribution `p`.

Bach warns (p. 37):

> Be careful with the order of quantifiers: the convergence speed of the excess risk
> toward zero will depend on `p`. See the "no free lunch" theorem in section 2.5 that
> highlights that having a uniform rate over all distributions is hopeless.

## Proof (verbatim)

(Definitions — no proof.) Bach immediately develops the **uniform consistency over
a class `P` of distributions** as the more useful notion:

>     sup_{p ∈ P} { E[R_p(A(D_n(p)))] − R∗_p }
>
> is as small as possible. The so-called minimax risk is equal to
>
>     inf_A sup_{p ∈ P} { E[R_p(A(D_n(p)))] − R∗_p }.

## Notes

- Three nested notions: **consistency for `p`** ⊂ **universal consistency** ⊂
  **uniform/minimax consistency over `P`**.
- Bach's preferred notion in the book is **consistency in expectation** (not PAC);
  Lean target follows this convention.
- The order-of-quantifiers warning is load-bearing: universal consistency does NOT
  imply a uniform rate over all `p`. The no-free-lunch theorem (§2.5,
  `no-free-lunch` concept) is the formal obstruction.
- Lean target: algebraic-anchor form is a `tendsto` predicate on the excess-risk
  sequence — `Filter.Tendsto (fun n => excessRisk (A (sample n))) atTop (𝓝 0)`.

## Prerequisites (Bach's dependency graph)

- [`bayes-predictor`](./bayes-predictor.md) — Bayes predictor f⋆ — minimizer of population risk
- [`population-risk`](./population-risk.md) — Population risk R(f) = E[ℓ(f(x), y)]

## Dependents (concepts that use this)

- [`no-free-lunch`](./no-free-lunch.md) — No-Free-Lunch theorem (♦)

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch02_SupervisedLearning/Consistency.lean`
- **Theorem/def name:** `UniversallyConsistent`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

