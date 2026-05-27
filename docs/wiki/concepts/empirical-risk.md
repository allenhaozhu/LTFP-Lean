# Empirical risk R̂_n(f)

**ID:** `empirical-risk`  
**Chapter:** Ch02 (Bach §2.3.2, p. 32)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `ERM`

## Statement

_See textbook excerpt below or [`tasks/empirical-risk/`](../../../tasks/empirical-risk/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Empirical risk R̂_n(f)

**Concept ID:** `empirical-risk`
**Chapter:** Ch 2
**Section:** 2.2.2 (Risks; definition appears here despite the ID's tag of §2.3.2)
**Pages:** 27 (definition) and 32 (use within ERM)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

**Definition 2.2 (Empirical risk), p. 27:**

> Given a prediction function `f : X → Y`, a loss function `ℓ : Y × Y → R`, and data
> `(xi, yi) ∈ X × Y, i = 1, …, n`, the empirical risk of `f` is defined as
>
>     R̂(f) = (1/n) Σ_{i=1}^n ℓ(yi, f(xi)).

Bach adds (p. 27):

> Note that `R̂` is a random function on functions (and is often applied to random
> functions, with dependent randomness as both will depend on the training data).

The notation `R̂_n` (subscript `n`) is also used when the dependence on the sample
size matters; the value is the average loss over the training set.

For the classical losses:
- 0–1 loss: `R̂(f) = (proportion of mistakes on the training data)` (p. 27).
- Square loss: `R̂(f) = (1/n) Σ (yi − f(xi))²` (training MSE).

## Proof (verbatim)

(Definition — no proof.)

## Notes

- The empirical risk is a **sample-average estimator** of `R(f) = E[ℓ(y, f(x))]`.
- Bach intentionally suppresses the sample-size subscript in display formulas; in
  formalization we make it explicit as `R̂_n` or `empiricalRisk ℓ s f` where `s` is
  the training sample.
- For the empty sample (`n = 0`), the empirical risk is conventionally `0`
  (averaging over an empty list). This convention is encoded in
  `empirical-risk-zero-sample`.
- Bach uses the equality form (1/n)·Σ; the Mathlib-natural form is `∫ d(uniform on sample)`
  or `(Finset.sum / n)`, both equivalent.

## Prerequisites (Bach's dependency graph)

- [`loss-function`](./loss-function.md) — Loss function ℓ : 𝒴 × 𝒴 → ℝ

## Dependents (concepts that use this)

- [`emp-risk-mono-pointwise`](./emp-risk-mono-pointwise.md) — Empirical risk is pointwise-monotone
- [`emp-risk-nonneg`](./emp-risk-nonneg.md) — Empirical risk of nonneg loss is nonneg
- [`emp-risk-zero-loss`](./emp-risk-zero-loss.md) — Empirical risk = 0 when all losses are 0
- [`empirical-risk-zero-sample`](./empirical-risk-zero-sample.md) — Empirical risk on empty sample = 0
- [`erm-def`](./erm-def.md) — Empirical risk minimizer over a hypothesis class
- [`ols-closed-form`](./ols-closed-form.md) — OLS closed form: β̂ = (XᵀX)⁻¹Xᵀy
- [`penalized-empirical-risk`](./penalized-empirical-risk.md) — Penalized empirical risk for SRM (♦)

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch02_SupervisedLearning/ERM.lean`
- **Theorem/def name:** `empiricalRisk`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

