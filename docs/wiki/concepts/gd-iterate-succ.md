# GD one-step closed form: x_{t+1} = x_t - γ ∇f(x_t)

**ID:** `gd-iterate-succ`  
**Chapter:** Ch05 (Bach §5.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Gradient-descent`

## Statement

_See textbook excerpt below or [`tasks/gd-iterate-succ/`](../../../tasks/gd-iterate-succ/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — GD one-step closed form: x_{t+1} = x_t - γ ∇f(x_t)

**Concept ID:** `gd-iterate-succ`
**Chapter:** Ch 5
**Section:** 5.2 (Algorithm 5.1, successor unfolding)
**Pages:** 111-112 (book), PDF pp. 127-128
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

The successor of the GD iterate is the GD step applied to the current iterate:
for the recursion $\theta_t = \theta_{t-1} - \gamma_t F'(\theta_{t-1})$ (eq. 5.2),
$$\theta_{t+1} = \theta_t - \gamma_{t+1} F'(\theta_t).$$
In Lean: `gdIterate ∇f γ θ₀ (t+1) = gdStep ∇f γ (gdIterate ∇f γ θ₀ t)`.

This is the definitional unfolding of the recursive definition.

## Proof (verbatim)

By definition of `gdIterate` (`rfl` in Lean): the recursion step is exactly
the application of `gdStep` to the previous iterate.

## Notes

- Foundation rewrite lemma; the analogue at the iterate level of `gd-step-eq`.
- Used in every inductive proof on $t$ involving the GD iterate.
- For constant step size $\gamma$, this becomes
  $\theta_{t+1} = \theta_t - \gamma F'(\theta_t)$ directly.

## Prerequisites (Bach's dependency graph)

- [`gd-iterate`](./gd-iterate.md) — Multi-step gradient-descent iterate

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch05_Optimization/GD.lean`
- **Theorem/def name:** `gdIterate_succ`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

