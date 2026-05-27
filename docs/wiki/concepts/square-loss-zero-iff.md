# squareLoss z y = 0 ↔ z = y

**ID:** `square-loss-zero-iff`  
**Chapter:** Ch02 (Bach §2.2.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/square-loss-zero-iff/`](../../../tasks/square-loss-zero-iff/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — squareLoss z y = 0 ↔ z = y

**Concept ID:** `square-loss-zero-iff`
**Chapter:** Ch 2
**Section:** 2.2.1 / 2.2.2
**Pages:** 26-30
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For the square loss `ℓ(y, z) = (y − z)²`, the equivalence `(z − y)² = 0 ↔ z = y`
is the standard "square equals zero iff the base is zero" identity over the
reals.

Bach uses this fact implicitly throughout §2.2.3 (p. 28-30) when deriving the
Bayes risk for regression: `R∗ = E[var(y | x)] = 0` if and only if `y` is a
deterministic function of `x`, i.e., the Bayes predictor `f∗(x) = E[y | x]`
satisfies `f∗(x) = y` almost surely.

## Proof (verbatim)

Bach does not prove this; it is the elementary algebraic equivalence
`x² = 0 ↔ x = 0` over `R`, followed by `z − y = 0 ↔ z = y`.

In Mathlib: `sq_eq_zero_iff` + `sub_eq_zero` — two rewrites.

## Notes

- Bach's footnote on p. 30 ("[Bayes risk equals expected conditional variance]")
  implicitly invokes this: `var(y|x) = 0 ↔ y` is `σ(x)`-measurable, i.e., a
  deterministic function of `x`.
- Together with `square-loss-self` (which is the `←` direction at `z = y`), this
  characterizes when the squared error vanishes.
- Pure algebra; one-line in Lean.

## Prerequisites (Bach's dependency graph)

- [`square-loss`](./square-loss.md) — Squared loss ℓ(z, y) = (z − y)²

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch02_SupervisedLearning/Defs.lean`
- **Theorem/def name:** `squareLoss_eq_zero_iff`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

