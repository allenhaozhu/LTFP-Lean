# Function with zero gradient is 0-smooth

**ID:** `is-l-smooth-zero`  
**Chapter:** Ch05 (Bach §F1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/is-l-smooth-zero/`](../../../tasks/is-l-smooth-zero/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Function with zero gradient is 0-smooth

**Concept ID:** `is-l-smooth-zero`
**Chapter:** Ch 5
**Section:** 5.2.3 (corollary of Definition 5.3)
**Pages:** 120 (book), PDF p. 136
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

If $F'(\theta) \equiv 0$ on $\mathbb{R}^d$ (i.e. $F$ has identically zero
gradient, so $F$ is constant) then $F$ is $0$-smooth: the inequality
$|F(\eta) - F(\theta) - F'(\theta)^\top(\eta - \theta)| \le \tfrac{0}{2}\|\theta - \eta\|_2^2 = 0$
holds because the left side equals $|F(\eta) - F(\theta)| = 0$ (constant $F$).

Bach treats $0$-smoothness as the degenerate boundary case of Definition 5.3
and does not give it a separate proposition.

## Proof (verbatim)

Algebraic: substitute $F' \equiv 0$ and the constancy of $F$ into (5.10);
both sides are zero.

## Notes

- Boundary lemma used to validate the `IsLSmooth` predicate and to set up
  pathological / trivial corner cases in tests.
- Mathlib's `LipschitzWith 0` for the gradient captures the same content
  (a 0-Lipschitz function is constant).
- Compounds with `is-l-smooth-mono` to obtain `IsLSmooth 0 F → IsLSmooth L F`
  for any $L \ge 0$.

## Prerequisites (Bach's dependency graph)

- [`convex-foundation`](./convex-foundation.md) — Convex analysis foundation: L-smooth alias + Mathlib re-exports

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/Convex.lean`
- **Theorem/def name:** `isLSmooth_zero`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

