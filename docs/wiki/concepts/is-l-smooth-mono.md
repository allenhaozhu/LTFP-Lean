# L-smoothness monotone in L

**ID:** `is-l-smooth-mono`  
**Chapter:** Ch05 (Bach §F1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/is-l-smooth-mono/`](../../../tasks/is-l-smooth-mono/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — L-smoothness monotone in L

**Concept ID:** `is-l-smooth-mono`
**Chapter:** Ch 5
**Section:** 5.2.3 (consequence of Definition 5.3)
**Pages:** 120 (book), PDF p. 136
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

If $F$ is $L$-smooth and $L \le L'$, then $F$ is $L'$-smooth: the inequality
$|F(\eta) - F(\theta) - F'(\theta)^\top(\eta - \theta)| \le \tfrac{L}{2}\|\theta - \eta\|_2^2 \le \tfrac{L'}{2}\|\theta - \eta\|_2^2$
holds by transitivity.

Bach implicitly uses this fact when he writes "Choosing the step size only
requires an upper bound $L$ on the smoothness constant (if it is overestimated,
the convergence rate only degrades slightly)" (PDF p. 139), since the proof of
Proposition 5.3 transparently goes through with any valid upper bound.

## Proof (verbatim)

Immediate: $\tfrac{L}{2}\|\theta-\eta\|_2^2 \le \tfrac{L'}{2}\|\theta-\eta\|_2^2$
when $L \le L'$, by nonnegativity of $\|\theta - \eta\|_2^2$.

## Notes

- Lean form: `IsLSmooth L F → L ≤ L' → IsLSmooth L' F`.
- Mathlib analogue: `LipschitzWith.mono` for Lipschitz constants of the gradient.
- Used to align smoothness constants across composition lemmas where multiple
  smoothness witnesses arise.

## Prerequisites (Bach's dependency graph)

- [`convex-foundation`](./convex-foundation.md) — Convex analysis foundation: L-smooth alias + Mathlib re-exports

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/Convex.lean`
- **Theorem/def name:** `IsLSmooth.mono`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

