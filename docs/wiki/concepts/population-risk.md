# Population risk R(f) = E[ℓ(f(x), y)]

**ID:** `population-risk`  
**Chapter:** Ch02 (Bach §2.2.2, p. 27)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/population-risk/`](../../../tasks/population-risk/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Population risk R(f) = E[ℓ(f(x), y)]

**Concept ID:** `population-risk`
**Chapter:** Ch 2
**Section:** 2.2.2 (Risks)
**Pages:** 27-28
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

**Definition 2.1 (Expected risk), p. 27:**

> Given a prediction function `f : X → Y`, a loss function `ℓ : Y × Y → R`, and a
> probability distribution `p` on `X × Y`, the expected risk of `f` is defined as
>
>     R(f) = E[ ℓ(y, f(x)) ] = ∫_{X × Y} ℓ(y, f(x)) dp(x, y).

Bach adds (p. 27):

> The risk depends on the distribution `p` on `(x, y)`. We sometimes use the notation
> `R_p(f)` to make it explicit. The expected risk is our main performance criterion in
> this textbook.

Naming: Bach uses the names **expected risk**, **generalization error**, and **testing
error** interchangeably (p. 27, opening sentence of §2.2.2).

For the classical losses Bach gives the canonical specializations (p. 27-28):
- 0–1 loss: `R(f) = P(f(x) ≠ y)` (error rate).
- Square loss: `R(f) = E[(y − f(x))²]` ("mean squared error", p. 28).

## Proof (verbatim)

(Definition — no proof.)

## Notes

- Bach uses the convention `ℓ(y, f(x))` (truth first, prediction second); our Lean
  code mirrors this with `ℓ : Y → Y → ℝ` applied as `ℓ y (f x)`.
- The integral form is the **Mathlib bridge** statement — population risk *is* the
  Lebesgue integral of the loss-composed-with-prediction against the joint measure.
- When `f` depends on (random) training data, `R(f)` is random; treated as a function
  on functions, `R` itself is deterministic (Bach's warning box, p. 27).

## Prerequisites (Bach's dependency graph)

- [`loss-function`](./loss-function.md) — Loss function ℓ : 𝒴 × 𝒴 → ℝ

## Dependents (concepts that use this)

- [`approximation-error`](./approximation-error.md) — Approximation error: best-in-class − Bayes risk
- [`bayes-predictor`](./bayes-predictor.md) — Bayes predictor f⋆ — minimizer of population risk
- [`bayes-risk-le-population-risk`](./bayes-risk-le-population-risk.md) — Bayes risk ≤ any specific population risk
- [`consistency`](./consistency.md) — Universal consistency of a learning algorithm
- [`estimation-error`](./estimation-error.md) — Estimation error: predictor risk − best-in-class risk
- [`local-averaging`](./local-averaging.md) — Local averaging predictors (k-NN, partition, kernel)
- [`pop-risk-eq-integral`](./pop-risk-eq-integral.md) — populationRisk = ∫ ℓ ∂D (Mathlib bridge)
- [`pop-risk-nonneg`](./pop-risk-nonneg.md) — populationRisk of nonneg loss is nonneg
- [`pop-risk-zero-measure`](./pop-risk-zero-measure.md) — populationRisk under zero measure = 0

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch02_SupervisedLearning/Defs.lean`
- **Theorem/def name:** `populationRisk`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

