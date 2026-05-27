# GD step with zero step is no-op (any function)

**ID:** `gd-step-zero-step`  
**Chapter:** Ch05 (Bach §F2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Gradient-descent`

## Statement

_See textbook excerpt below or [`tasks/gd-step-zero-step/`](../../../tasks/gd-step-zero-step/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — GD step with zero step is no-op (any function)

**Concept ID:** `gd-step-zero-step`
**Chapter:** Ch 5
**Section:** 5.2 (Algorithm 5.1, $\gamma = 0$ instance)
**Pages:** 111-112 (book), PDF pp. 127-128
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For any function $g : \mathbb{R}^d \to \mathbb{R}^d$ and any point $\theta$,
the single-step update with step size $0$ leaves $\theta$ unchanged:
$$\text{gdStep}(g, 0, \theta) = \theta - 0 \cdot g(\theta) = \theta.$$
Bach does not isolate this as a numbered statement; it is an immediate
consequence of (5.2).

## Proof (verbatim)

Algebraic: $0 \cdot g(\theta) = 0$ in any module / vector space, hence
$\theta - 0 \cdot g(\theta) = \theta$.

## Notes

- This is the single-step (foundation-level) version of `gd-iterate-zero-step`.
- Holds for *any* `g`, not only true gradients — the result is purely
  algebraic, independent of whether `g = ∇F` or `g` is something else.
- Lean form: `gdStep g 0 θ = θ`; trivial proof by `simp`.
- Used as the inductive step (rewrite) in proving `gd-iterate-zero-step`.

## Prerequisites (Bach's dependency graph)

- [`gradient-descent-foundation`](./gradient-descent-foundation.md) — Gradient descent foundation: gdStep update map

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/GradientDescent.lean`
- **Theorem/def name:** `gdStep_zero_step`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

