# GD update increment formula (definitional)

**ID:** `gd-step-eq`  
**Chapter:** Ch05 (Bach §F2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Gradient-descent`

## Statement

_See textbook excerpt below or [`tasks/gd-step-eq/`](../../../tasks/gd-step-eq/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — GD update increment formula (definitional)

**Concept ID:** `gd-step-eq`
**Chapter:** Ch 5
**Section:** 5.2 (Algorithm 5.1, definitional rewrite)
**Pages:** 111-112 (book), PDF pp. 127-128
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Definitional rewrite of the GD update map: for $g : \mathbb{R}^d \to \mathbb{R}^d$,
step size $\gamma \in \mathbb{R}$, and point $\theta \in \mathbb{R}^d$,
$$\text{gdStep}(g, \gamma, \theta) = \theta - \gamma \cdot g(\theta).$$
This is simply equation (5.2) with `g` substituted for $F'$.

## Proof (verbatim)

By definition (`rfl` in Lean). The lemma exists to expose the increment form
to the simp / rw tactic machinery.

## Notes

- Foundation-level definitional rewrite; called `gdStep_eq` in Lean.
- Used at the start of nearly every GD analysis to expand the update map.
- Compounds with `gd-iterate-succ` (closed form for the iterated version).

## Prerequisites (Bach's dependency graph)

- [`gradient-descent-foundation`](./gradient-descent-foundation.md) — Gradient descent foundation: gdStep update map

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/GradientDescent.lean`
- **Theorem/def name:** `gdStep_eq`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

