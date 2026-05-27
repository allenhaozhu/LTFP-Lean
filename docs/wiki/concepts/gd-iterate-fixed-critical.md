# GD fixed at critical point (∇f = 0)

**ID:** `gd-iterate-fixed-critical`  
**Chapter:** Ch05 (Bach §5.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Gradient-descent`

## Statement

_See textbook excerpt below or [`tasks/gd-iterate-fixed-critical/`](../../../tasks/gd-iterate-fixed-critical/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — GD fixed at critical point (∇f = 0)

**Concept ID:** `gd-iterate-fixed-critical`
**Chapter:** Ch 5
**Section:** 5.2.2 (Proposition 5.2 + consequence for Algorithm 5.1)
**Pages:** 118-119 (book), PDF pp. 134-135
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

If $\nabla F(\theta_0) = 0$, then the GD iterate is constant: $\theta_t = \theta_0$
for all $t \ge 0$. Bach states the related global characterisation:

**Proposition 5.2.** "Assume that $F:\mathbb{R}^d\to\mathbb{R}$ is convex and
differentiable. Then $\eta_*\in\mathbb{R}^d$ is a global minimizer of $F$ if and
only if $F'(\eta_*) = 0$" (PDF p. 134).

For our concept: if we start GD exactly at a critical point, every step subtracts
$\gamma_t \cdot 0 = 0$, so the iterate is fixed.

## Proof (verbatim)

Induction on $t$: base case $t=0$ holds by definition; for the step, if
$\theta_{t-1} = \theta_0$ and $F'(\theta_0) = 0$, then
$\theta_t = \theta_{t-1} - \gamma_t F'(\theta_{t-1}) = \theta_0 - \gamma_t \cdot 0 = \theta_0$.

## Notes

- Sanity-check fixed-point lemma; useful as a base case before stating
  convergence theorems.
- Lean form: `∇f θ₀ = 0 → ∀ t, gdIterate ∇f γ θ₀ t = θ₀`.
- For convex $F$, by Proposition 5.2 the critical point is the global minimum
  $\eta_*$, so starting at $\eta_*$ keeps GD at $\eta_*$ (consistency check).
- Dual to `gd-iterate-zero-step`: zero gradient ⇒ frozen; zero step ⇒ frozen.

## Prerequisites (Bach's dependency graph)

- [`gd-iterate`](./gd-iterate.md) — Multi-step gradient-descent iterate

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch05_Optimization/GD.lean`
- **Theorem/def name:** `gdIterate_fixed_at_critical`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

