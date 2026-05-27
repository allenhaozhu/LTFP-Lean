# Linear kernel k(x,y) = ⟨x, y⟩ on ℝᵈ

**ID:** `linear-kernel`  
**Chapter:** Ch07 (Bach §F4a)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Kernel`

## Statement

_See textbook excerpt below or [`tasks/linear-kernel/`](../../../tasks/linear-kernel/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Linear kernel k(x,y) = ⟨x, y⟩ on ℝᵈ

**Concept ID:** `linear-kernel`
**Chapter:** Ch 7
**Section:** §7.3.1 (Linear and Polynomial Kernels) / Foundation F4a
**Pages:** 186 (book) / PDF p. 202
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

"**Linear kernel.** We define $k(x, x') = x^\top x'$. This kernel corresponds to a function space composed of linear functions $f_\theta(x) = \theta^\top x$, with an $\ell_2$-penalty $\|\theta\|_2^2$."

That is, on $\mathcal{X} = \mathbb{R}^d$, the linear kernel is the Euclidean inner product, with the trivial feature map $\phi = \mathrm{id}_{\mathbb{R}^d}$ and feature space $\mathcal{H} = \mathbb{R}^d$.

## Proof (verbatim)

Bach gives a definition, not a theorem. The justification that $k(x, x') = x^\top x'$ is positive-definite is *immediate* from Proposition 7.3: take $\phi = \mathrm{id}$, then $k(x, x') = \langle\phi(x), \phi(x')\rangle$. (Sketch.)

The associated RKHS interpretation: "function space composed of linear functions $f_\theta(x) = \theta^\top x$, with an $\ell_2$-penalty $\|\theta\|_2^2$" (p. 186).

## Notes

- Lean encoding `linearKernel` in `LTFP/Foundations/Kernel.lean` is `fun x y => ⟪x, y⟫_ℝ` over `EuclideanSpace ℝ (Fin d)`.
- Bach's practical note: "The kernel trick can be useful when the input data have huge dimension $d$ but are quite sparse … so that the dot product $x^\top x'$ can be computed in time $o(d)$" (p. 186).
- Linear kernel is the base case for the polynomial kernel $k(x,x') = (x^\top x')^s$ (p. 186).

## Prerequisites (Bach's dependency graph)

- [`kernel-foundation`](./kernel-foundation.md) — Positive-definite kernel foundation: IsPSDKernel

## Dependents (concepts that use this)

- [`linear-kernel-add-left`](./linear-kernel-add-left.md) — Linear kernel additivity in left arg
- [`linear-kernel-add-right`](./linear-kernel-add-right.md) — Linear kernel additivity in right arg
- [`linear-kernel-self`](./linear-kernel-self.md) — Linear kernel self-evaluation = squared norm
- [`linear-kernel-self-nonneg`](./linear-kernel-self-nonneg.md) — Linear kernel self-eval is nonneg
- [`linear-kernel-symm`](./linear-kernel-symm.md) — Linear kernel symmetry
- [`linear-kernel-zero-left`](./linear-kernel-zero-left.md) — Linear kernel with zero left arg = 0
- [`linear-kernel-zero-right`](./linear-kernel-zero-right.md) — Linear kernel with zero right arg = 0

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/Kernel.lean`
- **Theorem/def name:** `linearKernel`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

