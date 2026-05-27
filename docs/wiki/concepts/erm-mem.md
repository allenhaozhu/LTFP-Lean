# ERM is in the hypothesis class

**ID:** `erm-mem`  
**Chapter:** Ch02 (Bach §2.3.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `ERM`

## Statement

_See textbook excerpt below or [`tasks/erm-mem/`](../../../tasks/erm-mem/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — ERM is in the hypothesis class

**Concept ID:** `erm-mem`
**Chapter:** Ch 2
**Section:** 2.3.2 (Empirical Risk Minimization)
**Pages:** 32
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

From the definition of ERM, §2.3.2 (p. 32):

> This defines an estimator
>
>     θ̂ ∈ arg min_{θ ∈ Θ} R̂(f_θ),
>
> and thus a prediction function `f_{θ̂} : X → Y`.

The "membership" claim is the **trivial** observation that any element of the
arg-min set `{θ : θ ∈ Θ, ∀ θ', R̂(f_θ) ≤ R̂(f_{θ'})}` is in particular in `Θ`
itself, i.e., `θ̂ ∈ Θ`. Equivalently in the function-space view, the prediction
function `f_{θ̂}` belongs to the parameterized hypothesis class
`{f_θ : θ ∈ Θ}`.

## Proof (verbatim)

Not proved; trivially built into the `arg min` over `Θ` notation.

In Lean: definitional unfolding of `Set.argmin` / `Function.argmin` —
`Set.argmin _ _` returns an element of the set or `None` if empty; the
membership claim is the `isSome` / definedness witness.

## Notes

- Two equivalent formulations:
  - **Parameter form:** `θ̂ ∈ Θ`. Trivially true.
  - **Function form:** `f_{θ̂} ∈ F`, where `F = {f_θ : θ ∈ Θ}` is the
    hypothesis class. Equally trivial.
- The Lean lemma is foundational for `erm-optimal`: the optimality bound
  `R̂(f_{θ̂}) ≤ R̂(f)` only ranges over `f ∈ F`, so the ERM's own membership
  in `F` is the consistency-with-optimality check.
- Discharged in Lean by definitional unfolding of `IsERM` predicate.

## Prerequisites (Bach's dependency graph)

- [`erm-def`](./erm-def.md) — Empirical risk minimizer over a hypothesis class

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch02_SupervisedLearning/ERM.lean`
- **Theorem/def name:** `ERM.mem`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

