# μ-strongly-convex predicate

**ID:** `mu-strongly-convex`  
**Chapter:** Ch05 (Bach §F1)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** `Convex`

## Statement

_See textbook excerpt below or [`tasks/mu-strongly-convex/`](../../../tasks/mu-strongly-convex/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — μ-strongly-convex predicate

**Concept ID:** `mu-strongly-convex`
**Chapter:** Ch 5
**Section:** 5.2.3 (Definition 5.2)
**Pages:** 119-120 (book), PDF pp. 135-136
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

**Definition 5.2 (Strong convexity).** A differentiable function $F$ is
$\mu$-strongly-convex, with $\mu \ge 0$, iff
$$F(\eta) \ge F(\theta) + F'(\theta)^\top(\eta - \theta) + \tfrac{\mu}{2}\|\eta - \theta\|_2^2,\qquad \forall\eta,\theta\in\mathbb{R}^d.\quad(5.9)$$

Geometrically, $F$ lies strictly above its tangent and the gap is at least
quadratic in the distance from the anchor.

For twice-differentiable $F$, equivalent to $F''(\theta) \succeq \mu I$
(all eigenvalues of every Hessian are $\ge \mu$); Bach cites Nesterov (2018).
Nonsmooth functions can also be strongly convex.

## Proof (verbatim)

Definition. Bach offers the equivalent characterisation (Exercise 5.5):
"function $F$ is $\mu$-strongly-convex if and only if function $F - \tfrac{\mu}{2}\|\cdot\|_2^2$
is convex" (proof left as exercise).

## Notes

- The Lean predicate `IsMuStronglyConvex F μ` is the inequality (5.9).
- Used jointly with $L$-smoothness in Proposition 5.3 to get exponential
  convergence with condition number $\kappa = L/\mu$.
- Special case $\mu = 0$ recovers ordinary convexity (5.6).
- Mathlib has `StrongConvexOn`; the foundation re-exports / aliases this.

## Prerequisites (Bach's dependency graph)

- [`convex-foundation`](./convex-foundation.md) — Convex analysis foundation: L-smooth alias + Mathlib re-exports

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/Convex.lean`
- **Theorem/def name:** `IsMuStronglyConvex`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

