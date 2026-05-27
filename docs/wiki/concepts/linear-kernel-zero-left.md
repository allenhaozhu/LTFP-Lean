# Linear kernel with zero left arg = 0

**ID:** `linear-kernel-zero-left`  
**Chapter:** Ch07 (Bach §F4a)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Kernel`

## Statement

_See textbook excerpt below or [`tasks/linear-kernel-zero-left/`](../../../tasks/linear-kernel-zero-left/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Linear kernel with zero left arg = 0

**Concept ID:** `linear-kernel-zero-left`
**Chapter:** Ch 7
**Section:** §7.3.1 / Foundation F4a (derived corollary)
**Pages:** 186 (book) / PDF p. 202
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For the linear kernel $k(x, y) = x^\top y$ on $\mathbb{R}^d$ and any $y \in \mathbb{R}^d$, $k(0, y) = 0$.

## Proof (verbatim)

Not stated separately by Bach; immediate from the definition $k(x, y) = \langle x, y\rangle$ together with the bilinearity of the Euclidean inner product: $\langle 0, y\rangle = 0$. (Sketch.)

## Notes

- Lean form `linearKernel_zero_left` in `LTFP/Foundations/Kernel.lean`.
- Trivial one-line lemma; used as algebraic plumbing in larger derivations (e.g., to show that KRR coefficients are linear in the labels).
- Paired with `linear-kernel-zero-right` for the symmetric variant.

## Prerequisites (Bach's dependency graph)

- [`linear-kernel`](./linear-kernel.md) — Linear kernel k(x,y) = ⟨x, y⟩ on ℝᵈ

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/Kernel.lean`
- **Theorem/def name:** `linearKernel_zero_left`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

