# Stochastic gradient descent foundation: sgdStep

**ID:** `stochastic-gd-foundation`  
**Chapter:** Ch05 (Bach §F3)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** partial  
**Vendored status:** new  
**Topic tags:** `Gradient-descent`, `SGD`

## Statement

Required prereq for Ch 5/11/12.

## Bach's textbook treatment

# Bach textbook excerpt — Stochastic gradient descent foundation: sgdStep

**Concept ID:** `stochastic-gd-foundation`
**Chapter:** Ch 5
**Section:** 5.4 (Algorithm 5.2)
**Pages:** 134-135 (book), PDF pp. 150-151
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

**Algorithm 5.2 (Stochastic gradient descent).** Choose a step-size sequence
$(\gamma_t)_{t\ge 0}$, pick $\theta_0\in\mathbb{R}^d$, and for $t\ge 1$, let
$$\theta_t = \theta_{t-1} - \gamma_t g_t(\theta_{t-1}),$$
where $g_t(\theta_{t-1})$ satisfies the unbiasedness condition (5.24):
$$\mathbb{E}[g_t(\theta_{t-1})\,|\,\theta_{t-1}] = F'(\theta_{t-1}).$$

The Lean foundation `sgdStep : (Rd → Rd) → ℝ → Rd → Rd` is the algebraic
update map `sgdStep g γ θ = θ - γ • g θ`, with the stochastic estimator `g`
plugged in as a parameter; the probabilistic content (the unbiasedness
hypothesis H-1) lives outside the update definition.

## Proof (verbatim)

Definition — no proof required. Bach emphasizes that the estimator $g_t$
may be much faster to compute than the full gradient, "in particular by
accessing fewer observations."

## Notes

- Bach lists two canonical estimator constructions: (i) sampling an index
  $i(t)\in\{1,\ldots,n\}$ and using $\nabla_\theta\ell(y_{i(t)},f_\theta(x_{i(t)}))$
  for empirical-risk minimization; (ii) drawing a fresh sample $(x_t,y_t)$ for
  expected-risk minimization (only valid for single-pass SGD).
- The two SGD assumptions used throughout: **(H-1)** unbiased gradient and
  **(H-2)** bounded estimator $\|g_t(\theta_{t-1})\|_2^2 \le B^2$ a.s.
- The Lean `sgdStep` is structurally identical to `gdStep`; the difference is
  *semantic* (which function plays the role of `g`), so the foundation can
  share rewrite lemmas across deterministic and stochastic settings.

## Prerequisites (Bach's dependency graph)

- [`gradient-descent-foundation`](./gradient-descent-foundation.md) — Gradient descent foundation: gdStep update map

## Dependents (concepts that use this)

- [`sgd-add-g`](./sgd-add-g.md) — SGD with sum-of-estimators algebraic rewrite
- [`sgd-iterate`](./sgd-iterate.md) — Multi-step SGD iterate
- [`sgd-step-eq`](./sgd-step-eq.md) — SGD update increment formula (definitional)
- [`sgd-step-zero-step`](./sgd-step-zero-step.md) — SGD step with zero step is no-op (any estimator)

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = partial`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/StochasticGD.lean`
- **Theorem/def name:** `sgdStep`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

