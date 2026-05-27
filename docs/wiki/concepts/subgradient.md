# Subgradient predicate IsSubgradient

**ID:** `subgradient`  
**Chapter:** Ch05 (Bach §5.3, p. 130)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** `Sub-Gaussian`

## Statement

_See textbook excerpt below or [`tasks/subgradient/`](../../../tasks/subgradient/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Subgradient predicate IsSubgradient

**Concept ID:** `subgradient`
**Chapter:** Ch 5
**Section:** 5.3 (Subgradient method)
**Pages:** 130-131 (book), PDF pp. 146-147
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach defines the subdifferential of a convex function $F$ at $\theta$ as
$$\partial F(\theta) = \{\,z\in\mathbb{R}^d \;:\; \forall\eta\in\mathbb{R}^d,\; F(\eta) \ge F(\theta) + z^\top(\eta - \theta)\,\}.$$
A *subgradient* is any element of this set. The Lean predicate
`IsSubgradient (F : Rd → ℝ) (θ z : Rd) : Prop` captures this membership
condition.

## Proof (verbatim)

Definitional. Bach notes two structural facts (no proof, cited to Rockafellar 1997):
- For a convex function on $\mathbb{R}^d$, $\partial F(\theta)$ is a nonempty
  convex set at every point.
- When $F$ is differentiable, $\partial F(\theta) = \{F'(\theta)\}$.
- Example: $\theta\mapsto|\theta|$ has $\partial F(0) = [-1,1]$.

## Notes

- Mathlib provides `Convex.subgradient` and the corresponding `HasSubgradient`
  / `IsSubgradient` predicates; this concept re-exports / aliases the relevant
  Mathlib definition.
- The subgradient method (Algorithm in §5.3) replaces $F'(\theta_{t-1})$ by any
  $z_t \in \partial F(\theta_{t-1})$ in the GD update.
- Bach warns: the subgradient method is "not a descent method anymore"; the
  function values may increase along iterations.
- Used in Proposition 5.6 (convergence of subgradient method), where only
  $F(\eta_*) \ge F(\theta) + z^\top(\eta_* - \theta)$ (one half of the defining
  inequality) is needed.

## Prerequisites (Bach's dependency graph)

- [`convex-foundation`](./convex-foundation.md) — Convex analysis foundation: L-smooth alias + Mathlib re-exports

## Dependents (concepts that use this)

- [`subgradient-add-const`](./subgradient-add-const.md) — Subgradient is invariant under additive constants

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch05_Optimization/Subgradient.lean`
- **Theorem/def name:** `IsSubgradient`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

