# Linear kernel symmetry

**ID:** `linear-kernel-symm`  
**Chapter:** Ch07 (Bach §F4a)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Kernel`

## Statement

_See textbook excerpt below or [`tasks/linear-kernel-symm/`](../../../tasks/linear-kernel-symm/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Linear kernel symmetry

**Concept ID:** `linear-kernel-symm`
**Chapter:** Ch 7
**Section:** §7.3.1 / Foundation F4a (derived corollary)
**Pages:** 182, 186 (book) / PDF pp. 198, 202
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For the linear kernel $k(x, y) = x^\top y$ on $\mathbb{R}^d$, symmetry holds: $k(x, y) = k(y, x)$ for all $x, y \in \mathbb{R}^d$.

## Proof (verbatim)

Bach does not state this as a numbered lemma; it is a **direct corollary** of his general remark on p. 182:

"We will need the kernel function $k : \mathcal{X} \times \mathcal{X} \to \mathbb{R}$, which is a **symmetric function** equal to the dot product between feature vectors: $k(x, x') = \langle\phi(x), \phi(x')\rangle$."

For the linear kernel specifically, $\phi = \mathrm{id}$, hence $k(x,y) = \langle x, y\rangle$, and symmetry of the real Euclidean inner product gives $\langle x, y\rangle = \langle y, x\rangle$. (Sketch.)

## Notes

- Lean form `linearKernel_symm` in `LTFP/Foundations/Kernel.lean` follows directly from `real_inner_comm`.
- Symmetry is one of two basic properties (with positive-definiteness) that Bach takes for granted when introducing kernels (p. 182, 183).
- This is a one-line lemma; its main role is as a prerequisite for `gram-matrix-symm` (Gram matrix is symmetric whenever the kernel is).

## Prerequisites (Bach's dependency graph)

- [`linear-kernel`](./linear-kernel.md) — Linear kernel k(x,y) = ⟨x, y⟩ on ℝᵈ

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/Kernel.lean`
- **Theorem/def name:** `linearKernel_symm`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

