# Bayes risk ≤ any specific population risk

**ID:** `bayes-risk-le-population-risk`  
**Chapter:** Ch02 (Bach §2.2.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Bayes-risk`

## Statement

_See textbook excerpt below or [`tasks/bayes-risk-le-population-risk/`](../../../tasks/bayes-risk-le-population-risk/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Bayes risk ≤ any specific population risk

**Concept ID:** `bayes-risk-le-population-risk`
**Chapter:** Ch 2
**Section:** 2.2.3 (Bayes Risk and Bayes Predictor)
**Pages:** 28-29
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Proposition 2.1 (p. 28), together with the proof on p. 29, gives the
inequality

>     R∗ ≤ R(f)   for all measurable `f : X → Y`,

i.e., the Bayes risk lower-bounds the population risk of every predictor.

This is the **definitional content of "Bayes risk is the optimum"**.

## Proof (verbatim, p. 29)

> Proof. We have
>
>     R(f) − R∗ = R(f) − R(f∗) = ∫_X [r(f(x') | x') − min_{z ∈ Y} r(z | x')] dp(x'),
>
> which shows the proposition.

The integrand `r(f(x') | x') − min_z r(z | x') ≥ 0` pointwise, so the integral
is `≥ 0`, hence `R(f) ≥ R∗`.

## Notes

- Reformulation of Proposition 2.1 as an inequality between numbers (rather
  than a statement about argmin / inf).
- The proof in Lean follows the same monotonicity-of-integral pattern:
  ```
  apply MeasureTheory.integral_mono_of_nonneg
  intro x'
  exact le_csInf hℓ_bounded (fun _ => le_refl _)
  ```
- Together with `pop-risk-nonneg` and `excess-risk-nonneg`, this completes
  the basic order-theoretic structure of the risk landscape.
- **Caveat:** the proof requires either (a) the `arg min`'s existence and
  measurability (Bach's assumption), or (b) the inf-form `R∗ = ∫ inf_z r(z|·)`
  to be well-defined; either way Bach's measurability disclaimer (p. 25)
  applies.

## Prerequisites (Bach's dependency graph)

- [`bayes-risk-minimum`](./bayes-risk-minimum.md) — Bayes risk equals the infimum of population risk
- [`population-risk`](./population-risk.md) — Population risk R(f) = E[ℓ(f(x), y)]

## Dependents (concepts that use this)

- [`excess-risk-nonneg`](./excess-risk-nonneg.md) — Excess risk is nonneg under nonneg loss

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch02_SupervisedLearning/Defs.lean`
- **Theorem/def name:** `bayesRisk_le_populationRisk`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

