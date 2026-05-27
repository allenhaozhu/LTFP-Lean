# Positive-definite kernel foundation: IsPSDKernel

**ID:** `kernel-foundation`  
**Chapter:** Ch07 (Bach §F4a)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** partial  
**Vendored status:** new  
**Topic tags:** `Kernel`, `Matrix/LinAlg`

## Statement

Wraps Matrix.PosSemidef — required prereq for Ch 7/9/12.

## Bach's textbook treatment

# Bach textbook excerpt — Positive-definite kernel foundation (IsPSDKernel)

**Concept ID:** `kernel-foundation`
**Chapter:** Ch 7
**Section:** §7.3 (Kernels) / Foundation F4a
**Pages:** 183 (book) / PDF p. 199
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Definition 7.1 (Positive-definite kernels). *A function* $k : \mathcal{X} \times \mathcal{X} \to \mathbb{R}$ *is a* **positive-definite kernel** *if and only if all kernel matrices resulting from this kernel functions are symmetric positive semidefinite.*

That is, for every $n \in \mathbb{N}$ and every $x_1, \dots, x_n \in \mathcal{X}$, the Gram matrix $K \in \mathbb{R}^{n\times n}$ with entries $K_{ij} = k(x_i, x_j)$ satisfies $K = K^\top$ and $\alpha^\top K \alpha \ge 0$ for all $\alpha \in \mathbb{R}^n$.

## Proof (verbatim)

Bach gives a definition, not a theorem. The justification that this property holds whenever $k(x,x') = \langle \phi(x),\phi(x')\rangle_\mathcal{H}$ appears immediately after, in the "Partial proof" of Proposition 7.3 (Aronszajn, 1950):

"We first assume that $k(x, x') = \langle\phi(x),\phi(x')\rangle_\mathcal{H}$. Then, for any $\alpha \in \mathbb{R}^n$ and points $x_1, \dots, x_n \in \mathcal{X}$, we have, for the kernel matrix $K$ associated with these points,
$$\alpha^\top K\alpha = \sum_{i,j=1}^n \alpha_i \alpha_j \langle\phi(x_i),\phi(x_j)\rangle_\mathcal{H} = \Big\|\sum_{i=1}^n \alpha_i \phi(x_i)\Big\|_\mathcal{H}^2 \ge 0.$$
Thus, $k$ is a positive-definite kernel."

## Notes

- Bach's terminology distinguishes positive-**definite** kernel functions (defined via PSD Gram matrices, which are positive *semi*-definite) from the linear-algebra term "positive definite matrix." The naming is historical (Aronszajn, 1950); see warning box on p. 183.
- The Lean foundation `IsPSDKernel` (in `LTFP/Foundations/Kernel.lean`) wraps `Matrix.PosSemidef` applied to the Gram matrix. This matches Bach's definition exactly.
- Required prereq for Ch 7/9/12 (per registry note).
- **Flagged ambiguity:** Bach uses the symbol > in extracted text for ≥ (PDF rendering artefact). The PSD condition is $\alpha^\top K\alpha \ge 0$, i.e., positive *semi*-definite in standard matrix terminology.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

- [`gram-matrix`](./gram-matrix.md) — Gram matrix Kᵢⱼ = k(xᵢ, xⱼ)
- [`kernel-expansion`](./kernel-expansion.md) — Kernel-expansion predictor f(x) = ∑ᵢ αᵢ k(x, xᵢ)
- [`linear-kernel`](./linear-kernel.md) — Linear kernel k(x,y) = ⟨x, y⟩ on ℝᵈ
- [`rkhs-foundation`](./rkhs-foundation.md) — RKHS foundation: real Hilbert space + feature map

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = partial`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/Kernel.lean`
- **Theorem/def name:** `IsPSDKernel`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

