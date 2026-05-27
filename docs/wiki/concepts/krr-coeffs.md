# Kernel ridge regression coefficient α̂_λ = (K + nλI)⁻¹ y

**ID:** `krr-coeffs`  
**Chapter:** Ch07 (Bach §7.4, p. 196)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `RKHS`, `Kernel`, `Ridge`

## Statement

_See textbook excerpt below or [`tasks/krr-coeffs/`](../../../tasks/krr-coeffs/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Kernel ridge regression coefficient α̂_λ = (K + nλI)⁻¹ y

**Concept ID:** `krr-coeffs`
**Chapter:** Ch 7
**Section:** §7.4.1 (Representer Theorem — algorithm)
**Pages:** 196 (book) / PDF p. 212
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For kernel ridge regression with regularization parameter $\lambda > 0$, Gram matrix $K \in \mathbb{R}^{n \times n}$ and label vector $y \in \mathbb{R}^n$, the optimal coefficient vector is

$$\hat\alpha_\lambda = (K + n\lambda I)^{-1} y \in \mathbb{R}^n. \quad (7.7)$$

## Proof (verbatim)

"We can directly apply the representer theorem, as done in equation (7.2), and try to solve
$$\min_{\alpha \in \mathbb{R}^n} \frac{1}{n} \sum_{i=1}^n \ell(y_i, (K\alpha)_i) + \frac{\lambda}{2} \alpha^\top K\alpha,$$
which is a convex optimization problem since $\ell$ is assumed convex with respect to the second variable, and $K$ is positive-semidefinite.

In the particular case of the square loss (ridge regression), this leads to
$$\min_{\alpha \in \mathbb{R}^n} \frac{1}{2n} \|y - K\alpha\|_2^2 + \frac{\lambda}{2} \alpha^\top K\alpha,$$
and setting the gradient to zero, we get $(K^2 + n\lambda K)\alpha = Ky$, with a solution
$$\alpha = (K + n\lambda I)^{-1} y, \quad (7.7)$$
which is not unique when $K$ is not invertible."

## Notes

- Bach writes "*not unique when $K$ is not invertible*" — i.e., (7.7) gives **one** solution; any element of $\ker K$ added still solves $(K^2 + n\lambda K)\alpha = Ky$.
- Proof technique: representer theorem reduces the infinite-dim problem to $\alpha \in \mathbb{R}^n$; first-order optimality + the identity $(K + n\lambda I)K = K(K + n\lambda I)$ (which always holds, since these matrices commute).
- Lean form `krrCoeffs` in `LTFP/Ch07_Kernels/Algorithms.lean` uses Mathlib `Matrix.inv` of $(K + n\lambda I)$ — well-defined because $K + n\lambda I \succ 0$ for $\lambda > 0$ (eigenvalues of $K$ are nonneg, shifted by $n\lambda$).
- Bach immediately follows with a *practical* warning: "in general (for the square loss and beyond), it is an ill-conditioned optimization problem because $K$ often has very small eigenvalues" — but this affects numerics, not the mathematical formula.
- Key intermediate lemma: $(K + n\lambda I)$ is invertible whenever $\lambda > 0$ (since $K \succeq 0$).

## Prerequisites (Bach's dependency graph)

- [`gram-matrix`](./gram-matrix.md) — Gram matrix Kᵢⱼ = k(xᵢ, xⱼ)
- [`ridge-closed-form`](./ridge-closed-form.md) — Ridge closed form: β̂_λ = (XᵀX + nλI)⁻¹Xᵀy

## Dependents (concepts that use this)

- [`krr-coeffs-add-y`](./krr-coeffs-add-y.md) — KRR coefficients linear in labels
- [`krr-coeffs-smul-y`](./krr-coeffs-smul-y.md) — KRR coefficients homogeneous in labels
- [`krr-coeffs-zero-y`](./krr-coeffs-zero-y.md) — KRR coefficients with zero labels = 0
- [`krr-predictor`](./krr-predictor.md) — Kernel ridge regression predictor

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch07_Kernels/Algorithms.lean`
- **Theorem/def name:** `krrCoeffs`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

