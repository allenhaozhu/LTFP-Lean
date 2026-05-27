# KRR predictor linear in labels (composition)

**ID:** `krr-predictor-add-y`  
**Chapter:** Ch07 (Bach §7.4)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `RKHS`

## Statement

_See textbook excerpt below or [`tasks/krr-predictor-add-y/`](../../../tasks/krr-predictor-add-y/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — KRR predictor linear in labels (composition)

**Concept ID:** `krr-predictor-add-y`
**Chapter:** Ch 7
**Section:** §7.4.1 / §7.6.1 (derived composition lemma)
**Pages:** 196 (book) / PDF p. 212
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For fixed kernel $k$, training inputs $(x_1, \dots, x_n)$, and regularization $\lambda > 0$, the KRR predictor $y \mapsto f_{\hat\alpha_\lambda(y)}$ is additive in $y$: for all $y_1, y_2 \in \mathbb{R}^n$ and all test points $x \in \mathcal{X}$,

$$f_{\hat\alpha_\lambda(y_1 + y_2)}(x) = f_{\hat\alpha_\lambda(y_1)}(x) + f_{\hat\alpha_\lambda(y_2)}(x).$$

## Proof (verbatim)

Bach states KRR is a linear estimator in §7.6.1 (title: "Kernel Ridge Regression as a Linear Estimator," p. 196). The composition argument is:

1. **Coefficients additive** (`krr-coeffs-add-y`): $\hat\alpha_\lambda(y_1 + y_2) = \hat\alpha_\lambda(y_1) + \hat\alpha_\lambda(y_2)$, from closed form (7.7).
2. **Predictor additive in coefficients** (`kernel-expansion-add`): $f_{\alpha+\beta}(x) = f_\alpha(x) + f_\beta(x)$.

Composing: $f_{\hat\alpha_\lambda(y_1+y_2)}(x) = f_{\hat\alpha_\lambda(y_1) + \hat\alpha_\lambda(y_2)}(x) = f_{\hat\alpha_\lambda(y_1)}(x) + f_{\hat\alpha_\lambda(y_2)}(x).$ (Sketch.)

## Notes

- Lean form `krrPredictor_add_y` in `LTFP/Ch07_Kernels/Algorithms.lean`.
- Composition of two earlier lemmas — `krr-coeffs-add-y` (linear-algebra fact) and `kernel-expansion-add` (predictor algebra).
- This is the precise statement that "KRR is a linear estimator," underlying §7.6's bias-variance analysis.
- Bach: "*Kernel Ridge Regression as a Linear Estimator*" (§7.6.1 heading, p. 196).

## Prerequisites (Bach's dependency graph)

- [`kernel-expansion-add`](./kernel-expansion-add.md) — Kernel expansion is linear in coefficients
- [`krr-coeffs-add-y`](./krr-coeffs-add-y.md) — KRR coefficients linear in labels

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch07_Kernels/Algorithms.lean`
- **Theorem/def name:** `krrPredictor_add_y`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

