# Kernel ridge regression predictor

**ID:** `krr-predictor`  
**Chapter:** Ch07 (Bach §7.4, p. 196)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `RKHS`, `Kernel`, `Ridge`

## Statement

_See textbook excerpt below or [`tasks/krr-predictor/`](../../../tasks/krr-predictor/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Kernel ridge regression predictor

**Concept ID:** `krr-predictor`
**Chapter:** Ch 7
**Section:** §7.4.1 (Representer Theorem — algorithm) + §7.2 (predictor formula)
**Pages:** 182, 196 (book) / PDF pp. 198, 212
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

The kernel ridge regression predictor is the kernel expansion at the KRR coefficient vector $\hat\alpha_\lambda = (K + n\lambda I)^{-1} y$:

$$f_\lambda(x) = \sum_{i=1}^n (\hat\alpha_\lambda)_i \, k(x, x_i), \qquad \hat\alpha_\lambda = (K + n\lambda I)^{-1} y.$$

## Proof (verbatim)

Constructed by composing two earlier statements.

(1) Predictor template (p. 182):
"Note that for any test point $x \in \mathcal{X}$, we have defined the prediction function as
$f(x) = \langle \theta, \phi(x)\rangle = \sum_{i=1}^n \alpha_i k(x, x_i).$"

(2) KRR coefficients (p. 196, equation (7.7)):
"$\alpha = (K + n\lambda I)^{-1} y$".

Substituting $\alpha = \hat\alpha_\lambda$ into the predictor gives the displayed formula.

## Notes

- Bach treats KRR as the canonical example of "representer + closed-form" workflow: representer theorem reduces $\mathcal{H}$ to $\mathbb{R}^n$, the square loss admits a closed-form linear solve, and the predictor follows.
- Lean encoding `krrPredictor` in `LTFP/Ch07_Kernels/Algorithms.lean` is literally `kernelExpansion (krrCoeffs k x y λ) k x` — the composition pattern is faithful to Bach.
- The predictor only ever needs **kernel evaluations** at training points and the test point, never the feature map — this is the kernel trick.
- Connection to chapter 3: when $\mathcal{H} = \mathbb{R}^d$, KRR reduces to ridge regression (Tikhonov), via the matrix inversion lemma $(\Phi\Phi^\top + n\lambda I)^{-1} \Phi = \Phi(\Phi^\top \Phi + n\lambda I)^{-1}$ (Bach mentions this in exercise 7.11).

## Prerequisites (Bach's dependency graph)

- [`kernel-expansion`](./kernel-expansion.md) — Kernel-expansion predictor f(x) = ∑ᵢ αᵢ k(x, xᵢ)
- [`krr-coeffs`](./krr-coeffs.md) — Kernel ridge regression coefficient α̂_λ = (K + nλI)⁻¹ y

## Dependents (concepts that use this)

- [`krr-predictor-zero-kernel`](./krr-predictor-zero-kernel.md) — KRR with zero kernel yields zero predictor

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch07_Kernels/Algorithms.lean`
- **Theorem/def name:** `krrPredictor`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

