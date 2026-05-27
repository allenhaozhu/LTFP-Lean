# Bayes predictor f⋆ — minimizer of population risk

**ID:** `bayes-predictor`  
**Chapter:** Ch02 (Bach §2.2.3, p. 28)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Bayes-risk`

## Statement

_See textbook excerpt below or [`tasks/bayes-predictor/`](../../../tasks/bayes-predictor/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Bayes predictor f⋆

**Concept ID:** `bayes-predictor`
**Chapter:** Ch 2
**Section:** 2.2.3 (Bayes Risk and Bayes Predictor)
**Pages:** 28-29
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach first defines the **conditional risk** (p. 28):

>     r(z | x') = E[ℓ(y, z) | x = x'],
>
> which leads to `R(f) = ∫_X r(f(x') | x') dp(x')`.

**Proposition 2.1 (Bayes predictor and Bayes risk), p. 28:**

> The expected risk is minimized at a Bayes predictor `f∗ : X → Y`, satisfying
> for all `x' ∈ X`,
>
>     f∗(x') ∈ arg min_{z ∈ Y} E[ℓ(y, z) | x = x'] = arg min_{z ∈ Y} r(z | x').   (2.1)

(The display also defines the Bayes risk — see `bayes-risk-minimum`.)

## Proof (verbatim, p. 28-29)

> Proof. We have
>
>     R(f) − R∗ = R(f) − R(f∗) = ∫_X [r(f(x') | x') − min_{z ∈ Y} r(z | x')] dp(x'),
>
> which shows the proposition.

Bach immediately comments:

> Note that (1) the Bayes predictor is not always unique, but that all lead to the
> same Bayes risk (e.g., in binary classification when `P(y = 1 | x) = 1/2`); and
> (2) that the Bayes risk is usually nonzero (unless the dependence between `x` and
> `y` is deterministic).

**Closed-form examples Bach derives:**
- Binary 0–1 loss with `η(x') = P(y = 1 | x = x')`: `f∗(x') = sign(η(x') − 1/2)` (p. 29).
- Square loss: `f∗(x') = E[y | x = x']` — the conditional expectation (p. 30).

## Notes

- The Bayes predictor is **pointwise-defined** as an argmin of the conditional risk.
  Nonuniqueness on a measure-zero set is harmless because all minimizers attain the
  same Bayes risk.
- The proof reduces optimization over functions to pointwise optimization in `z ∈ Y`;
  this decoupling fails as soon as `f` is restricted to a class (p. 28 warning box).
- Lean target chooses an algebraic anchor (constant-function pointwise-argmin) rather
  than the full measure-theoretic existence statement, since the latter requires
  a measurable-selection theorem.

## Prerequisites (Bach's dependency graph)

- [`population-risk`](./population-risk.md) — Population risk R(f) = E[ℓ(f(x), y)]

## Dependents (concepts that use this)

- [`bayes-risk-minimum`](./bayes-risk-minimum.md) — Bayes risk equals the infimum of population risk
- [`consistency`](./consistency.md) — Universal consistency of a learning algorithm

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch02_SupervisedLearning/Defs.lean`
- **Theorem/def name:** `bayesPredictor`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

