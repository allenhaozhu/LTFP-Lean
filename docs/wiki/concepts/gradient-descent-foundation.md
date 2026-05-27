# Gradient descent foundation: gdStep update map

**ID:** `gradient-descent-foundation`  
**Chapter:** Ch05 (Bach §F2)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** partial  
**Vendored status:** new  
**Topic tags:** `Gradient-descent`

## Statement

Wraps Mathlib.Analysis.Calculus.Gradient — required prereq for Ch 5/9/12.

## Bach's textbook treatment

# Bach textbook excerpt — Gradient descent foundation: gdStep update map

**Concept ID:** `gradient-descent-foundation`
**Chapter:** Ch 5
**Section:** 5.2 (Algorithm 5.1)
**Pages:** 111-112 (book), PDF pp. 127-128
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

**Algorithm 5.1 (Gradient descent).** Pick $\theta_0\in\mathbb{R}^d$ and for $t\ge 1$, let
$$\theta_t = \theta_{t-1} - \gamma_t F'(\theta_{t-1}),\qquad (5.2)$$
for a well (potentially adaptively) chosen step-size sequence $(\gamma_t)_{t\ge 1}$.

The Lean foundation `gdStep : (Rd → Rd) → ℝ → Rd → Rd` (or equivalent type)
captures a single application of this update: `gdStep ∇f γ θ = θ - γ • ∇f θ`.

## Proof (verbatim)

Definition — no proof required. Bach motivates the algorithm by noting that
the gradient $F'(\theta)$ is the direction of steepest ascent, so $-\gamma F'$
is the natural descent step; the smoothness analysis (Section 5.2.3) then
justifies the step-size choice $\gamma=1/L$.

## Notes

- The step-size sequence may be constant, decaying, or chosen by line search
  (Bach references Armijo 1966 and Goldstein 1962).
- For machine-learning objectives $F(\theta)=\tfrac{1}{n}\sum_i \ell(y_i,f_\theta(x_i)) + \Omega(\theta)$,
  one gradient evaluation costs $O(nd)$ for linear predictors.
- The foundation lemma `gdStep` abstracts the oracle $F'$ as an arbitrary
  function `g : Rd → Rd`, decoupling the update map from any specific objective.

## Prerequisites (Bach's dependency graph)

- [`convex-foundation`](./convex-foundation.md) — Convex analysis foundation: L-smooth alias + Mathlib re-exports

## Dependents (concepts that use this)

- [`gd-descent-lemma`](./gd-descent-lemma.md) — GD descent lemma: f(x − η ∇f(x)) ≤ f(x) − η(1 − Lη/2) ‖∇f(x)‖²
- [`gd-iterate`](./gd-iterate.md) — Multi-step gradient-descent iterate
- [`gd-step-eq`](./gd-step-eq.md) — GD update increment formula (definitional)
- [`gd-step-zero-step`](./gd-step-zero-step.md) — GD step with zero step is no-op (any function)
- [`implicit-bias-full-rank`](./implicit-bias-full-rank.md) — Implicit bias of GD = OLS (full-rank case)
- [`stochastic-gd-foundation`](./stochastic-gd-foundation.md) — Stochastic gradient descent foundation: sgdStep

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = partial`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/GradientDescent.lean`
- **Theorem/def name:** `gdStep`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

