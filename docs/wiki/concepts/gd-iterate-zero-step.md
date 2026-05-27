# GD with zero step size is a no-op

**ID:** `gd-iterate-zero-step`  
**Chapter:** Ch05 (Bach §5.2.1, p. 112)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Gradient-descent`

## Statement

_See textbook excerpt below or [`tasks/gd-iterate-zero-step/`](../../../tasks/gd-iterate-zero-step/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — GD with zero step size is a no-op

**Concept ID:** `gd-iterate-zero-step`
**Chapter:** Ch 5
**Section:** 5.2.1 (consequence of Algorithm 5.1)
**Pages:** 111-112 (book), PDF pp. 127-128
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Substituting $\gamma_t = 0$ into (5.2) yields $\theta_t = \theta_{t-1}$ for all
$t$, hence $\theta_t = \theta_0$ for every $t \ge 0$. Bach does not state this
as a separate proposition (it is an immediate algebraic consequence) but uses
the observation when noting that "all step sizes strictly less than $2/L$ will
lead to exponential convergence" and characterising the boundary case.

## Proof (verbatim)

Immediate from (5.2): $\theta_t = \theta_{t-1} - 0\cdot F'(\theta_{t-1}) = \theta_{t-1}$,
so by induction $\theta_t = \theta_0$.

## Notes

- Sanity-check lemma for the Lean `gdIterate` definition; useful as a corner-case
  baseline before stating non-trivial convergence rates.
- The Lean form is `∀ t, gdIterate f 0 θ₀ t = θ₀` (constant step size 0).
- No analogue in Mathlib because the iterate itself is bespoke to this project.
- Dual to `gd-iterate-fixed-critical`: zero step ⇒ frozen; zero gradient ⇒ frozen.

## Prerequisites (Bach's dependency graph)

- [`gd-iterate`](./gd-iterate.md) — Multi-step gradient-descent iterate

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch05_Optimization/GD.lean`
- **Theorem/def name:** `gdIterate_zero_step`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

