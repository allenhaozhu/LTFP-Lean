# Approximation error: best-in-class − Bayes risk

**ID:** `approximation-error`  
**Chapter:** Ch04 (Bach §4.3, p. 84)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Bayes-risk`

## Statement

_See textbook excerpt below or [`tasks/approximation-error/`](../../../tasks/approximation-error/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Approximation error

**Concept ID:** `approximation-error`
**Chapter:** Ch 4
**Section:** 4.3
**Pages:** 84-85
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
The approximation error is the deterministic best-in-class excess risk over the Bayes risk:

$$\text{approximation error} = \inf_{f \in F} R(f) - R^*,$$

where R^* = inf_{g measurable} R(g) is the Bayes risk. "The approximation error inf_{f∈F} R(f) − R^*
is deterministic and depends on the underlying distribution and class F of functions: the
larger the class, the smaller the approximation error.

Bounding the approximation error requires assumptions on the Bayes predictor (sometimes also
called the 'target function') f_*, and hence on the testing distribution."

## Proof (verbatim)
(Definition + decomposition — no proof.)

Bach derives a further sub-decomposition for parameterized linear classes F = {f_θ : θ ∈ Θ}
with Θ ⊂ R^d:

$$\inf_{\theta\in\Theta} R(f_\theta) - R^* = \Big(\inf_{\theta\in\Theta} R(f_\theta) - \inf_{\theta'\in\mathbb R^d} R(f_{\theta'})\Big) + \Big(\inf_{\theta'\in\mathbb R^d} R(f_{\theta'}) - R^*\Big),$$

where the second term is "the incompressible approximation error coming from the chosen set
of models f_θ. For flexible models such as kernel methods (chapter 7) or neural networks
(chapter 9), this incompressible error can be made as small as desired."

The first term is bounded under Lipschitz losses by a "distance" between θ_* and Θ:
inf_{‖θ‖₂ ≤ D} R(f_θ) − inf_{θ ∈ R^d} R(f_θ) ≤ G E[‖ϕ(x)‖₂] (‖θ_*‖₂ − D)_+,
which is zero when ‖θ_*‖₂ ≤ D (well-specified model).

## Notes
- Purely population-level quantity — no randomness.
- Independent of any specific estimator f̂; depends only on (F, p).
- Decomposes the chapter's overall excess-risk story into deterministic (approximation) +
  random (estimation) parts.
- For G-Lipschitz loss + linear F: upper bound G · E[‖ϕ‖₂] · dist(θ_*, Θ).

## Prerequisites (Bach's dependency graph)

- [`bayes-risk-minimum`](./bayes-risk-minimum.md) — Bayes risk equals the infimum of population risk
- [`population-risk`](./population-risk.md) — Population risk R(f) = E[ℓ(f(x), y)]

## Dependents (concepts that use this)

- [`approx-error-indep-fhat`](./approx-error-indep-fhat.md) — Approximation error independent of specific predictor
- [`excess-risk-decomposition`](./excess-risk-decomposition.md) — Excess risk = approximation + estimation
- [`excess-risk-eq-approx-when-optimal`](./excess-risk-eq-approx-when-optimal.md) — Optimal predictor in H ⇒ excess risk = approximation error

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/RiskDecomposition.lean`
- **Theorem/def name:** `approximationError`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

