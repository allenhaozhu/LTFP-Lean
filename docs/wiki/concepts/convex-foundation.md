# Convex analysis foundation: L-smooth alias + Mathlib re-exports

**ID:** `convex-foundation`  
**Chapter:** Ch05 (Bach §F1)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** `Convex`

## Statement

Wraps Mathlib.Analysis.Convex.* — required prereq for Ch 4/5/7/8/11/13.

## Bach's textbook treatment

# Bach textbook excerpt — Convex analysis foundation: L-smooth alias + Mathlib re-exports

**Concept ID:** `convex-foundation`
**Chapter:** Ch 5
**Section:** 5.2.2 / 5.2.3 (Definition 5.3)
**Pages:** 116-120 (book), PDF pp. 132-136
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach introduces convexity and smoothness as the two foundational analytic
properties used throughout Chapter 5.

**Definition 5.1 (Convex function).** A differentiable function $F:\mathbb{R}^d\to\mathbb{R}$
is convex iff
$$F(\eta) \ge F(\theta) + F'(\theta)^\top(\eta - \theta),\qquad \forall\eta,\theta\in\mathbb{R}^d.\quad(5.6)$$
Geometrically, "the function $F$ [is] above its tangent at $\theta$."

**Definition 5.3 (Smoothness).** A differentiable function $F$ is $L$-smooth iff
$$|F(\eta) - F(\theta) - F'(\theta)^\top(\eta - \theta)| \le \tfrac{L}{2}\|\theta - \eta\|_2^2,\qquad \forall\theta,\eta\in\mathbb{R}^d.\quad(5.10)$$
Bach notes this is equivalent to the gradient being $L$-Lipschitz w.r.t. the
$\ell_2$-norm: $\|F'(\theta) - F'(\eta)\|_2 \le L\|\theta - \eta\|_2$. For
twice-differentiable $F$, equivalent to $-LI \preceq F''(\theta) \preceq LI$.

## Proof (verbatim)

These are definitions; Bach provides supporting equivalences as exercises (the
equivalence to Lipschitz-gradient is "proof left as an exercise"). The
twice-differentiable characterization is attributed to Nesterov (2018).

## Notes

- The Lean `IsLSmooth` predicate is a thin alias around the inequality (5.10).
- When `F` is both convex and `L`-smooth, the quadratic upper bound
  $F(\eta)\le F(\theta) + F'(\theta)^\top(\eta-\theta) + \tfrac{L}{2}\|\eta-\theta\|_2^2$
  is tight at the anchor point $\theta$.
- Mathlib provides `ConvexOn` and `LipschitzWith` for the gradient; the
  foundation re-exports these and packages the absolute-value bound in (5.10).
- Ambiguity flag: Bach states (5.10) with absolute value, which gives both an
  upper and a lower quadratic bound; Mathlib's `LipschitzWith ∘ gradient`
  formulation is the standard equivalent form.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

- [`gradient-descent-foundation`](./gradient-descent-foundation.md) — Gradient descent foundation: gdStep update map
- [`is-l-smooth-const-any`](./is-l-smooth-const-any.md) — Constant is L-smooth for any L
- [`is-l-smooth-mono`](./is-l-smooth-mono.md) — L-smoothness monotone in L
- [`is-l-smooth-zero`](./is-l-smooth-zero.md) — Function with zero gradient is 0-smooth
- [`mu-strongly-convex`](./mu-strongly-convex.md) — μ-strongly-convex predicate
- [`online-convex-foundation`](./online-convex-foundation.md) — Online-convex foundation: regret definition
- [`phi-exponential`](./phi-exponential.md) — Exponential surrogate Φ(u) = exp(-u) — yields AdaBoost
- [`phi-hinge`](./phi-hinge.md) — Hinge surrogate Φ(u) = max(1-u, 0) — yields SVM
- [`phi-logistic`](./phi-logistic.md) — Logistic surrogate Φ(u) = log(1 + exp(-u))
- [`phi-square`](./phi-square.md) — Square surrogate Φ(u) = (u-1)²
- [`subgradient`](./subgradient.md) — Subgradient predicate IsSubgradient

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/Convex.lean`
- **Theorem/def name:** `IsLSmooth`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

