# GD descent lemma: f(x − η ∇f(x)) ≤ f(x) − η(1 − Lη/2) ‖∇f(x)‖²

**ID:** `gd-descent-lemma`  
**Chapter:** Ch05 (Bach §5.1, p. 109)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** B  
**Mathlib status:** partial  
**Vendored status:** new  
**Topic tags:** `Gradient-descent`

## Statement

_See textbook excerpt below or [`tasks/gd-descent-lemma/`](../../../tasks/gd-descent-lemma/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — GD descent lemma: f(x − η ∇f(x)) ≤ f(x) − η(1 − Lη/2) ‖∇f(x)‖²

**Concept ID:** `gd-descent-lemma`
**Chapter:** Ch 5
**Section:** 5.2.3 (proof of Proposition 5.3, descent inequality)
**Pages:** 122-123 (book), PDF pp. 138-139
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For an $L$-smooth function $F$, step size $\eta > 0$, and any point $x$:
$$F(x - \eta \nabla F(x)) \le F(x) - \eta\!\left(1 - \tfrac{L\eta}{2}\right)\|\nabla F(x)\|_2^2.$$

This is the *descent lemma*. In Bach's proof of Proposition 5.3 (PDF p. 138), he
applies smoothness (5.10) to the pair $(\theta_{t-1}, \theta_t = \theta_{t-1} - \nabla F(\theta_{t-1})/L)$
and obtains the special case $\eta = 1/L$:
$$F(\theta_t) \le F(\theta_{t-1}) - \tfrac{1}{L}\|\nabla F(\theta_{t-1})\|_2^2 + \tfrac{L}{2}\cdot \tfrac{1}{L^2}\|\nabla F(\theta_{t-1})\|_2^2 = F(\theta_{t-1}) - \tfrac{1}{2L}\|\nabla F(\theta_{t-1})\|_2^2.$$
For our concept's general form (arbitrary $\eta$), the same algebra gives the
coefficient $\eta(1 - L\eta/2)$, which is positive precisely when $\eta < 2/L$.

## Proof (verbatim)

Apply the $L$-smooth upper quadratic inequality (5.10):
$F(y) \le F(x) + \nabla F(x)^\top(y-x) + \tfrac{L}{2}\|y-x\|_2^2$
with $y = x - \eta\nabla F(x)$. Then $y - x = -\eta\nabla F(x)$, so
$\nabla F(x)^\top(y-x) = -\eta\|\nabla F(x)\|_2^2$ and $\|y-x\|_2^2 = \eta^2\|\nabla F(x)\|_2^2$.
Substituting gives the claim.

## Notes

- Lean target name: `gd_descent_quadratic`.
- For $\eta \in (0, 2/L)$, the coefficient $\eta(1 - L\eta/2) > 0$, so a strict
  decrease in $F$ is obtained whenever $\nabla F(x) \neq 0$.
- The optimal $\eta$ maximising the coefficient is $\eta = 1/L$, giving
  the canonical descent $F(\theta_t) \le F(\theta_{t-1}) - \tfrac{1}{2L}\|\nabla F(\theta_{t-1})\|_2^2$
  used throughout §5.2.3 and §5.2.6 (nonconvex case, PDF p. 145).
- Bach uses this in both convex / strongly-convex analyses and the nonconvex
  stationary-point bound $\min_s \|\nabla F(\theta_s)\|_2^2 = O(1/t)$.

## Prerequisites (Bach's dependency graph)

- [`gd-iterate`](./gd-iterate.md) — Multi-step gradient-descent iterate
- [`gradient-descent-foundation`](./gradient-descent-foundation.md) — Gradient descent foundation: gdStep update map

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = partial`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch05_Optimization/GD.lean`
- **Theorem/def name:** `gd_descent_quadratic`
- **Status:** B
- **Primary closing commit:** `b135564` (theorem `gd_descent_lemma_of_quadratic_bound`)
- **Audit class:** **B**
- **Audit notes:** Takes the quadratic upper bound `f(y) ≤ f(x) + ⟨∇f(x), y-x⟩ + (L/2)‖y-x‖²` as HYPOTHESIS — the substantive Taylor step. **A-class successor `gd_descent_lemma_of_lipschitz_gradient_diff` (`6701362`) discharges this hypothesis from `LipschitzWith L ∇f` alone via `lSmooth_quadratic_upper_bound`.**

## Audit history (if any)

- commit `b135564` — theorem `gd_descent_lemma_of_quadratic_bound` — classified **B** in PROGRESS.md §10 (Takes the quadratic upper bound `f(y) ≤ f(x) + ⟨∇f(x), y-x⟩ + (L/2)‖y-x‖²` as HYPOTHESIS — the substantive Taylor step. **A-class successor `gd_descent_lemma_of_lipschitz_gradient_diff` (`6701362`) discharges this hypothesis from `LipschitzWith L ∇f` alone via `lSmooth_quadratic_upper_bound`.**)
- commit `8f08045` — theorem `gd_descent_lemma_of_lipschitz_gradient` — classified **B** in PROGRESS.md §10 (Adds `LipschitzWith L ∇f` to signature but **keeps Taylor-bridge as named hypothesis** — does NOT discharge from `LipschitzWith` (Stage-3 of the residual-batch confirmed this is the open gap: Mathlib's mean-value gives `L`, not `L/2`). **A-class successor `gd_descent_lemma_of_lipschitz_gradient_diff` (`6701362`) closes this gap via the auxiliary-function Taylor argument; this abstract theorem retained as template only.**)

## Notes / open questions

- Carrier is **parametric** — at least one substantive hypothesis is passed through, not discharged.
- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

