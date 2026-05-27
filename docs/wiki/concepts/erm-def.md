# Empirical risk minimizer over a hypothesis class

**ID:** `erm-def`  
**Chapter:** Ch02 (Bach §2.3.2, p. 33)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `ERM`

## Statement

_See textbook excerpt below or [`tasks/erm-def/`](../../../tasks/erm-def/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Empirical risk minimizer over a hypothesis class

**Concept ID:** `erm-def`
**Chapter:** Ch 2
**Section:** 2.3.2 (Empirical Risk Minimization)
**Pages:** 32-33
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

From §2.3.2 (p. 32):

> Consider a parameterized family of prediction functions (often referred to as
> models) `f_θ : X → Y` for `θ ∈ Θ` (typically a subset of a vector space). This
> class of learning methods aims at minimizing the empirical risk with respect to
> `θ ∈ Θ`:
>
>     R̂(f_θ) = (1/n) Σ_{i=1}^n ℓ(yi, f_θ(xi)).
>
> This defines an estimator
>
>     θ̂ ∈ arg min_{θ ∈ Θ} R̂(f_θ),
>
> and thus a prediction function `f_{θ̂} : X → Y`.

The most classical example Bach gives (p. 32-33) is **linear least-squares
regression**:

>     min_{θ} (1/n) Σ (yi − θᵀ φ(xi))².

## Proof (verbatim)

(Definition — no proof.) Bach's surrounding commentary lists pros and cons (p. 33):

> Pros: (1) can be relatively easy to optimize [...], (2) can be applied in any
> dimension if a suitable feature vector is available.
> Cons: (1) can be relatively hard to optimize when [...] not convex (e.g., neural
> networks); (2) need a suitable feature vector for linear methods; (3) the dependence
> on parameters can be complex; (4) need some capacity control to avoid overfitting;
> (5) require to parameterize functions with values in `{0, 1}` (see chapter 4).

## Notes

- ERM is defined as an **`arg min`** — the set of all empirical-risk minimizers. Any
  selection from this set is an "ERM estimator".
- For Lean, the carrier facts are (i) ERM `∈` hypothesis class (`erm-mem`),
  (ii) ERM optimality `R̂(erm) ≤ R̂(f)` for all `f` in the class (`erm-optimal`).
- Existence of an ERM (a measurable selection) is a nontrivial measure-theoretic
  fact when `Θ` is infinite; Bach silently assumes it (cf. p. 25 measurability
  disclaimer). Lean target uses `Finset` / nonempty-set machinery to dodge this.
- The empirical optimization error `R̂(f_{θ̂}) − inf_{θ} R̂(f_θ)` (p. 34) is zero for
  exact ERM but positive for inexact optimizers (chapter 5).

## Prerequisites (Bach's dependency graph)

- [`empirical-risk`](./empirical-risk.md) — Empirical risk R̂_n(f)

## Dependents (concepts that use this)

- [`erm-mem`](./erm-mem.md) — ERM is in the hypothesis class
- [`erm-optimal`](./erm-optimal.md) — ERM optimality property

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch02_SupervisedLearning/ERM.lean`
- **Theorem/def name:** `ERM`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

