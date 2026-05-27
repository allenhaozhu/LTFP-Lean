# Multi-step gradient-descent iterate

**ID:** `gd-iterate`  
**Chapter:** Ch05 (Bach §5.2, p. 111)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/gd-iterate/`](../../../tasks/gd-iterate/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Multi-step gradient-descent iterate

**Concept ID:** `gd-iterate`
**Chapter:** Ch 5
**Section:** 5.2 (Algorithm 5.1, recursion form)
**Pages:** 111-112 (book), PDF pp. 127-128
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Following equation (5.2), Bach defines the GD iterate as the recursion
$\theta_t = \theta_{t-1} - \gamma_t F'(\theta_{t-1})$ for $t\ge 1$, starting from
some chosen $\theta_0\in\mathbb{R}^d$. In Lean we materialize this as a
recursive function `gdIterate : ℕ → Rd` with `gdIterate 0 = θ₀` and
`gdIterate (t+1) = gdStep ∇f γ (gdIterate t)` (for the constant-step-size
specialization, or `γ : ℕ → ℝ` for the general case).

## Proof (verbatim)

Definitional. Bach derives the closed-form unrolling
$\theta_t - \eta_* = (I - \gamma H)^t(\theta_0 - \eta_*)$ for the
ordinary-least-squares case in Section 5.2.1 (PDF p. 129) as a worked example,
showing the linear-recursion structure of GD on a quadratic objective.

## Notes

- This is the iterated form used in every convergence proof in Section 5.2:
  Proposition 5.3 (smooth strongly convex), Proposition 5.5 (smooth convex),
  Proposition 5.6 (subgradient method).
- For variable step size, the Lean definition takes `γ : ℕ → ℝ`; for the
  constant-step case the recursion specializes to `θ_t = gdStep^t θ₀`.
- Bach uses the convention $\theta_0$ for the initial point and reserves
  $\eta_*$ for the (empirical-risk) minimizer, $\theta_*$ for the
  expected-risk minimizer.

## Prerequisites (Bach's dependency graph)

- [`gradient-descent-foundation`](./gradient-descent-foundation.md) — Gradient descent foundation: gdStep update map

## Dependents (concepts that use this)

- [`gd-descent-lemma`](./gd-descent-lemma.md) — GD descent lemma: f(x − η ∇f(x)) ≤ f(x) − η(1 − Lη/2) ‖∇f(x)‖²
- [`gd-iterate-fixed-critical`](./gd-iterate-fixed-critical.md) — GD fixed at critical point (∇f = 0)
- [`gd-iterate-succ`](./gd-iterate-succ.md) — GD one-step closed form: x_{t+1} = x_t - γ ∇f(x_t)
- [`gd-iterate-zero-step`](./gd-iterate-zero-step.md) — GD with zero step size is a no-op

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch05_Optimization/GD.lean`
- **Theorem/def name:** `gdIterate`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

