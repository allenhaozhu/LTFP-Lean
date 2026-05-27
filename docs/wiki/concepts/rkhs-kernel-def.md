# RKHS kernel extensional definition

**ID:** `rkhs-kernel-def`  
**Chapter:** Ch07 (Bach §F4b)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `RKHS`, `Kernel`

## Statement

_See textbook excerpt below or [`tasks/rkhs-kernel-def/`](../../../tasks/rkhs-kernel-def/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — RKHS kernel extensional definition

**Concept ID:** `rkhs-kernel-def`
**Chapter:** Ch 7
**Section:** §7.3 (Kernels) / Foundation F4b
**Pages:** 182-183 (book) / PDF pp. 198-199
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For an RKHS structure $(\mathcal{H}, \phi)$ on $\mathcal{X}$, the associated kernel function is defined extensionally by

$$k(x, x') := \langle\phi(x), \phi(x')\rangle_\mathcal{H}, \qquad \forall x, x' \in \mathcal{X}.$$

This is the *defining equation* of the kernel — two RKHS structures with the same feature map give the same kernel, and the kernel is symmetric (Bach: "*$k$ is a symmetric function equal to the dot product between feature vectors*").

## Proof (verbatim)

p. 182: "*We will need the kernel function $k : \mathcal{X} \times \mathcal{X} \to \mathbb{R}$, which is a symmetric function equal to the dot product between feature vectors:*
$$k(x, x') = \langle \phi(x), \phi(x')\rangle.$$"

This is the **definition** Bach uses for the kernel induced by a feature map. The converse direction (every PSD kernel comes from some feature map) is Proposition 7.3 (Aronszajn, p. 183).

## Notes

- Lean form `RKHS.kernel_def` in `LTFP/Foundations/RKHS.lean` packages this as a definitional rewrite rule: `RKHS.kernel = fun x y => ⟪φ x, φ y⟫_ℝ`.
- This is the "extensional" form used to *unfold* the abstract `RKHS.kernel` in proofs.
- Symmetry $k(x, x') = k(x', x)$ follows from the symmetry of the real inner product.

## Prerequisites (Bach's dependency graph)

- [`rkhs-foundation`](./rkhs-foundation.md) — RKHS foundation: real Hilbert space + feature map

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/RKHS.lean`
- **Theorem/def name:** `RKHS.kernel_def`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

