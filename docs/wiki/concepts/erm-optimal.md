# ERM optimality property

**ID:** `erm-optimal`  
**Chapter:** Ch02 (Bach §2.3.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `ERM`

## Statement

_See textbook excerpt below or [`tasks/erm-optimal/`](../../../tasks/erm-optimal/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — ERM optimality property

**Concept ID:** `erm-optimal`
**Chapter:** Ch 2
**Section:** 2.3.2 (Empirical Risk Minimization)
**Pages:** 32-34
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

The defining property of ERM, §2.3.2 (p. 32):

> This class of learning methods aims at minimizing the empirical risk with
> respect to `θ ∈ Θ`:
>
>     R̂(f_θ) = (1/n) Σ_{i=1}^n ℓ(yi, f_θ(xi)).
>
> This defines an estimator
>
>     θ̂ ∈ arg min_{θ ∈ Θ} R̂(f_θ).

Spelled out as an inequality, the **ERM optimality property** is:

>     R̂(f_{θ̂}) ≤ R̂(f_θ)  for all `θ ∈ Θ`.

Bach uses this immediately in the risk decomposition on p. 34:

>     R(f_{θ̂}) − R(f_{θ'}) = [R(f_{θ̂}) − R̂(f_{θ̂})] + [R̂(f_{θ̂}) − R̂(f_{θ'})]
>                                                    + [R̂(f_{θ'}) − R(f_{θ'})]
>                         ≤ 2 sup_θ |R̂(f_θ) − R(f_θ)| + (empirical optimization error).

The middle bracket `R̂(f_{θ̂}) − R̂(f_{θ'}) ≤ 0` is exactly the ERM optimality
property; it is what permits the bound `R(f_{θ̂}) − R(f_{θ'}) ≤ 2 sup_θ |...|`.

## Proof (verbatim)

Not proved; this is the definitional property of ERM. Bach reasons "since
`θ̂` is an empirical risk minimizer over `Θ`, `R̂(f_{θ̂}) ≤ R̂(f_{θ'})` for
any `θ' ∈ Θ`" (p. 34, implicit).

In Lean: definitional unfolding of `IsERM` (or `Function.argmin_le` /
`Set.argmin_mem` from Mathlib).

## Notes

- Foundational for the risk-decomposition bound (Bach p. 34) and for every
  generalization bound in chapters 4, 7, 9.
- The bound is **tight**: every element of `arg min` saturates the inequality
  (R̂ value matches the min). For an inexact minimizer, the inequality is
  loose by the empirical optimization error `R̂(f_{θ̂}) − inf_θ R̂(f_θ)`.
- One-line discharge in Lean via the chosen `IsERM` predicate.

## Prerequisites (Bach's dependency graph)

- [`erm-def`](./erm-def.md) — Empirical risk minimizer over a hypothesis class

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch02_SupervisedLearning/ERM.lean`
- **Theorem/def name:** `ERM.optimal`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

