# Constant is L-smooth for any L

**ID:** `is-l-smooth-const-any`  
**Chapter:** Ch05 (Bach §F1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/is-l-smooth-const-any/`](../../../tasks/is-l-smooth-const-any/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Constant is L-smooth for any L

**Concept ID:** `is-l-smooth-const-any`
**Chapter:** Ch 5
**Section:** 5.2.3 (degenerate case of Definition 5.3)
**Pages:** 120 (book), PDF p. 136
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

A constant function $F(\theta) \equiv c$ has gradient $F'(\theta) \equiv 0$,
and the smoothness inequality (5.10) becomes $|c - c - 0| = 0 \le \tfrac{L}{2}\|\theta-\eta\|_2^2$
which holds for any $L \ge 0$. Hence every constant is $L$-smooth for every
$L \ge 0$.

## Proof (verbatim)

Algebraic: both sides of (5.10) are zero (constant $\Rightarrow$ zero
difference) or nonneg (RHS), and $0 \le \tfrac{L}{2}\|\theta-\eta\|_2^2$ when
$L \ge 0$.

## Notes

- Boundary / sanity-check lemma. Confirms the smoothness predicate is
  populated by trivial examples (constants, zero map) before stating
  nontrivial instances (linear, quadratic, logistic loss, …).
- Lean form: `∀ L ≥ 0, IsLSmooth L (fun _ => c)`.
- Compounds with `is-l-smooth-zero` (zero-gradient ⇒ 0-smooth) and
  `is-l-smooth-mono` to populate corner cases for tests.

## Prerequisites (Bach's dependency graph)

- [`convex-foundation`](./convex-foundation.md) — Convex analysis foundation: L-smooth alias + Mathlib re-exports

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/Convex.lean`
- **Theorem/def name:** `isLSmooth_const_any`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

