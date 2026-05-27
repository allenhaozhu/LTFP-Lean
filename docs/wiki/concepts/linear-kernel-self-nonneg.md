# Linear kernel self-eval is nonneg

**ID:** `linear-kernel-self-nonneg`  
**Chapter:** Ch07 (Bach §F4a)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Kernel`

## Statement

_See textbook excerpt below or [`tasks/linear-kernel-self-nonneg/`](../../../tasks/linear-kernel-self-nonneg/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Linear kernel self-evaluation is nonneg

**Concept ID:** `linear-kernel-self-nonneg`
**Chapter:** Ch 7
**Section:** §7.3.1 / Foundation F4a (derived corollary)
**Pages:** 183, 186 (book) / PDF pp. 199, 202
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For the linear kernel $k(x, y) = x^\top y$ on $\mathbb{R}^d$ and any $x \in \mathbb{R}^d$, $k(x, x) = \|x\|_2^2 \ge 0$.

## Proof (verbatim)

Not stated separately; combines `linear-kernel-self` ($k(x,x) = \|x\|^2$) with the elementary fact $\|x\|^2 \ge 0$.

Bach's general framework (p. 183) provides the abstract version: for any positive-definite kernel $k$ and any $x$,
$k(x, x) = \langle\phi(x), \phi(x)\rangle = \|\phi(x)\|^2 \ge 0.$ (Sketch.)

## Notes

- Lean form `linearKernel_self_nonneg` in `LTFP/Foundations/Kernel.lean`.
- One-line corollary of `linear-kernel-self` + `sq_nonneg`-type fact.
- Used as a building block for the more general `rkhs-kernel-self-nonneg`.

## Prerequisites (Bach's dependency graph)

- [`linear-kernel`](./linear-kernel.md) — Linear kernel k(x,y) = ⟨x, y⟩ on ℝᵈ

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/Kernel.lean`
- **Theorem/def name:** `linearKernel_self_nonneg`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

