# Linear kernel additivity in right arg

**ID:** `linear-kernel-add-right`  
**Chapter:** Ch07 (Bach §F4a)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Kernel`

## Statement

_See textbook excerpt below or [`tasks/linear-kernel-add-right/`](../../../tasks/linear-kernel-add-right/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Linear kernel additivity in right arg

**Concept ID:** `linear-kernel-add-right`
**Chapter:** Ch 7
**Section:** §7.3.1 / Foundation F4a (derived corollary)
**Pages:** 186 (book) / PDF p. 202
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For the linear kernel $k(x, y) = x^\top y$ on $\mathbb{R}^d$ and any $x, y_1, y_2 \in \mathbb{R}^d$,

$$k(x, y_1 + y_2) = k(x, y_1) + k(x, y_2).$$

## Proof (verbatim)

Not stated separately; immediate from bilinearity of the inner product: $\langle x, y_1 + y_2\rangle = \langle x, y_1\rangle + \langle x, y_2\rangle$. (Sketch.)

## Notes

- Lean form `linearKernel_add_right` in `LTFP/Foundations/Kernel.lean`.
- Companion to `linear-kernel-add-left`.
- These bilinearity lemmas underlie the linearity of the kernel expansion in the coefficients (`kernel-expansion-add`, `kernel-expansion-smul`).

## Prerequisites (Bach's dependency graph)

- [`linear-kernel`](./linear-kernel.md) — Linear kernel k(x,y) = ⟨x, y⟩ on ℝᵈ

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/Kernel.lean`
- **Theorem/def name:** `linearKernel_add_right`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

