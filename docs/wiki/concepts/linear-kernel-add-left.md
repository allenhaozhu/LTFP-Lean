# Linear kernel additivity in left arg

**ID:** `linear-kernel-add-left`  
**Chapter:** Ch07 (Bach §F4a)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Kernel`

## Statement

_See textbook excerpt below or [`tasks/linear-kernel-add-left/`](../../../tasks/linear-kernel-add-left/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Linear kernel additivity in left arg

**Concept ID:** `linear-kernel-add-left`
**Chapter:** Ch 7
**Section:** §7.3.1 / Foundation F4a (derived corollary)
**Pages:** 186 (book) / PDF p. 202
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For the linear kernel $k(x, y) = x^\top y$ on $\mathbb{R}^d$ and any $x_1, x_2, y \in \mathbb{R}^d$,

$$k(x_1 + x_2, y) = k(x_1, y) + k(x_2, y).$$

## Proof (verbatim)

Not stated separately; immediate from the bilinearity of the Euclidean inner product: $\langle x_1 + x_2, y\rangle = \langle x_1, y\rangle + \langle x_2, y\rangle$. (Sketch.)

## Notes

- Lean form `linearKernel_add_left` in `LTFP/Foundations/Kernel.lean`.
- One of the elementary bilinearity lemmas that Bach assumes when manipulating expressions like $\alpha^\top K \alpha$ (p. 182).
- Combined with `linear-kernel-add-right` and `linear-kernel-zero-left/right`, characterizes bilinearity.

## Prerequisites (Bach's dependency graph)

- [`linear-kernel`](./linear-kernel.md) — Linear kernel k(x,y) = ⟨x, y⟩ on ℝᵈ

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/Kernel.lean`
- **Theorem/def name:** `linearKernel_add_left`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

