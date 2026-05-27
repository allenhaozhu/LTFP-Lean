# Bayes risk equals the infimum of population risk

**ID:** `bayes-risk-minimum`  
**Chapter:** Ch02 (Bach §2.2.3, p. 28)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Bayes-risk`

## Statement

_See textbook excerpt below or [`tasks/bayes-risk-minimum/`](../../../tasks/bayes-risk-minimum/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Bayes risk equals the infimum of population risk

**Concept ID:** `bayes-risk-minimum`
**Chapter:** Ch 2
**Section:** 2.2.3 (Bayes Risk and Bayes Predictor)
**Pages:** 28-29
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Within Proposition 2.1 (p. 28), Bach defines:

> The Bayes risk `R∗` is the risk of all Bayes predictors and is equal to
>
>     R∗ = E_{x' ∼ p}[ inf_{z ∈ Y} E[ℓ(y, z) | x = x'] ].

The minimality claim is captured in the **excess-risk identity** Bach writes at
the start of the proof (p. 29):

>     R(f) − R∗ = R(f) − R(f∗) = ∫_X [ r(f(x') | x') − min_{z ∈ Y} r(z | x') ] dp(x').

Because each pointwise bracket `r(f(x') | x') − min_{z} r(z | x') ≥ 0`, the integral
is nonnegative; hence `R∗ ≤ R(f)` for every measurable `f`, i.e., `R∗ = inf_f R(f)`
(over the predictor class allowed in the problem).

**Definition 2.3 (Excess risk), p. 29:**

> The excess risk of a function `f : X → Y` is equal to `R(f) − R∗` (it is always
> nonnegative).

## Proof (verbatim, p. 29)

> Proof. We have `R(f) − R∗ = R(f) − R(f∗) = ∫_X [r(f(x') | x') − min_{z ∈ Y} r(z | x')] dp(x')`,
> which shows the proposition.

(Bach defers full measure-theoretic justification — measurable selectors, the
exchange of `inf` and `E` — to Christmann & Steinwart (2008), as noted on p. 25
in the measurability disclaimer.)

## Notes

- The "infimum" form `R∗ = inf_f R(f)` is **derived**, not the definition; Bach
  defines `R∗` directly as the integrated pointwise infimum.
- Pointwise key inequality: for each `x'`, `r(f(x') | x') ≥ inf_z r(z | x')`. The
  whole proposition is monotonicity of the integral applied to this pointwise
  inequality.
- For Lean, the cleanest carrier statement is the **inequality** `R∗ ≤ R(f)` for all
  measurable `f` — captured in the dual lemma `bayes-risk-le-population-risk`.

## Prerequisites (Bach's dependency graph)

- [`bayes-predictor`](./bayes-predictor.md) — Bayes predictor f⋆ — minimizer of population risk

## Dependents (concepts that use this)

- [`approximation-error`](./approximation-error.md) — Approximation error: best-in-class − Bayes risk
- [`bayes-risk-le-population-risk`](./bayes-risk-le-population-risk.md) — Bayes risk ≤ any specific population risk
- [`bayes-risk-nonneg`](./bayes-risk-nonneg.md) — Bayes risk is nonneg under nonneg loss

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch02_SupervisedLearning/Defs.lean`
- **Theorem/def name:** `bayesRisk_isLeast`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

