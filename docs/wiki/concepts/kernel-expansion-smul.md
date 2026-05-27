# Kernel expansion is homogeneous in coefficients

**ID:** `kernel-expansion-smul`  
**Chapter:** Ch07 (Bach §7.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Kernel`

## Statement

_See textbook excerpt below or [`tasks/kernel-expansion-smul/`](../../../tasks/kernel-expansion-smul/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Kernel expansion is homogeneous in coefficients

**Concept ID:** `kernel-expansion-smul`
**Chapter:** Ch 7
**Section:** §7.2 (Representer Theorem) — derived identity
**Pages:** 182 (book) / PDF p. 198
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

The kernel-expansion predictor $f_\alpha(x) = \sum_{i=1}^n \alpha_i k(x, x_i)$ is *homogeneous* in the coefficient vector: for all $c \in \mathbb{R}$ and $\alpha \in \mathbb{R}^n$,

$$f_{c \cdot \alpha}(x) = c \cdot f_\alpha(x), \qquad \forall x \in \mathcal{X}.$$

Together with additivity (`kernel-expansion-add`), this gives $\mathbb{R}$-linearity.

## Proof (verbatim)

Not stated as a numbered theorem; immediate from the definition:
$f_{c\alpha}(x) = \sum_i (c \alpha_i) k(x, x_i) = c \sum_i \alpha_i k(x, x_i) = c f_\alpha(x).$ (Sketch.)

Visible in Bach's matrix formulation: $(K(c\alpha))_j = c (K\alpha)_j$ (p. 182).

## Notes

- Lean form `kernelExpansion_smul` in `LTFP/Ch07_Kernels/Representer.lean`.
- Used together with `kernel-expansion-add` to derive linearity of KRR predictor in labels.
- Trivial proof — scalar multiplication distributes over the finite sum.

## Prerequisites (Bach's dependency graph)

- [`kernel-expansion`](./kernel-expansion.md) — Kernel-expansion predictor f(x) = ∑ᵢ αᵢ k(x, xᵢ)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch07_Kernels/Representer.lean`
- **Theorem/def name:** `kernelExpansion_smul`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

