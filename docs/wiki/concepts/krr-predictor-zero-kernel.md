# KRR with zero kernel yields zero predictor

**ID:** `krr-predictor-zero-kernel`  
**Chapter:** Ch07 (Bach §7.4)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `RKHS`, `Kernel`

## Statement

_See textbook excerpt below or [`tasks/krr-predictor-zero-kernel/`](../../../tasks/krr-predictor-zero-kernel/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — KRR with zero kernel yields zero predictor

**Concept ID:** `krr-predictor-zero-kernel`
**Chapter:** Ch 7
**Section:** §7.4.1 (edge case / sanity check)
**Pages:** 196 (book) / PDF p. 212
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

If the kernel $k \equiv 0$ (zero kernel), then the KRR predictor is identically zero: for all $\lambda > 0$, $y \in \mathbb{R}^n$, and $x \in \mathcal{X}$,

$$f_{\hat\alpha_\lambda(y)}(x) = 0.$$

## Proof (verbatim)

Not stated by Bach; trivial sanity check. Sketch:

1. With $k \equiv 0$, the Gram matrix $K = 0$ (lemma `gram-matrix-zero`).
2. Then $\hat\alpha_\lambda = (0 + n\lambda I)^{-1} y = (n\lambda)^{-1} y$.
3. The predictor $f_{\hat\alpha_\lambda}(x) = \sum_i (\hat\alpha_\lambda)_i \cdot k(x, x_i) = \sum_i (\hat\alpha_\lambda)_i \cdot 0 = 0.$

## Notes

- Lean form `krrPredictor_zero_kernel` in `LTFP/Ch07_Kernels/Algorithms.lean`.
- Edge-case lemma; not a Bach theorem but a useful sanity check that the formulation handles the degenerate kernel correctly.
- The RKHS of the zero kernel contains only the zero function, so this is consistent with the representer theorem (any predictor in this RKHS is zero).

## Prerequisites (Bach's dependency graph)

- [`krr-predictor`](./krr-predictor.md) — Kernel ridge regression predictor

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch07_Kernels/Algorithms.lean`
- **Theorem/def name:** `krrPredictor_zero_kernel`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

