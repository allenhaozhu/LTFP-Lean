# Double-descent excess risk nonnegativity anchor

**ID:** `double-descent-nonneg`  
**Chapter:** Ch12 (Bach §12.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/double-descent-nonneg/`](../../../tasks/double-descent-nonneg/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Double-descent excess risk nonnegativity anchor

**Concept ID:** `double-descent-nonneg`
**Chapter:** Ch 12
**Section:** 12.2.3 Linear Regression with Gaussian Inputs
**Pages:** 358-360
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
> We now consider a d-dimensional Gaussian random vector with mean 0 and covariance
> matrix identity, with n observations x₁, …, xₙ ∈ ℝᵈ, and responses
> yᵢ = xᵢ⊤ θ* + εᵢ, with εᵢ normal with mean zero and variance σ² I, for i = 1, …, n.
> We will compute an exact expectation of the risk of the minimum norm empirical risk
> minimizer (as detailed in section 12.1.1), which is the one gradient descent
> converges to. We denote by X ∈ ℝⁿˣᵈ the design matrix, and Σ̂ = (1/n) X⊤X the
> non-centered covariance matrix, and by K = XX⊤ ∈ ℝⁿˣⁿ the kernel matrix. As shown
> in section 3.8, the excess risk is
>   R(θ̂) = (θ̂ − θ*)⊤ Σ (θ̂ − θ*) = ‖θ̂ − θ*‖₂²    since Σ = I.

> **Underparameterized regime.** In the underparameterized regime, the minimum norm
> empirical risk minimizer is simply the ordinary least-squares estimator, which is
> unbiased; that is, E[θ̂] = θ*. We then have an expected excess risk equal to
>   E[R(θ̂)] = (σ²/n) E[tr(Σ Σ̂⁻¹)] = σ² E[tr((X⊤X)⁻¹)].
> The matrix X⊤X ∈ ℝᵈˣᵈ has a Wishart distribution with n degrees of freedom. It is
> almost surely invertible if n ≥ d, and is such that E[tr((X⊤X)⁻¹)] = d/(n−d−1) if
> n ≥ d+2. The expectation is infinite for n = d and n = d+1. Therefore, we have for
> n ≥ d+2 an expected excess risk equal to
>   E[R(θ̂)] = σ² · d/(n − d − 1).                                   (12.17)

> **Overparameterized regime.** In the overparameterized regime, when n ≤ d, the
> kernel matrix is almost surely invertible, and the minimum ℓ₂-norm interpolator θ̂
> is equal to (using the formulas in section 12.1.1)
>   θ̂ = X⊤(XX⊤)⁻¹ y = X⊤(XX⊤)⁻¹ X θ* + X⊤(XX⊤)⁻¹ ε.

## Proof (verbatim)
> The variance term is equal to, since Σ = I,
>   E[ε⊤(XX⊤)⁻¹ X Σ X⊤(XX⊤)⁻¹ ε]
>     = σ² E[tr((XX⊤)⁻¹ XX⊤ (XX⊤)⁻¹)]
>     = σ² E[tr((XX⊤)⁻¹)],
> which is the same expectation of the trace of an inverse Wishart matrix, but with
> the order of n and d reversed; that is, σ² · n/(d − n − 1) for d ≥ n+2.

> The bias term is equal to
>   E[R(X⊤(XX⊤)⁻¹ X θ*)] = E[‖Σ^{1/2} X⊤(XX⊤)⁻¹ X θ* − θ*‖₂²]
>                        = E[θ*⊤ (I − X⊤(XX⊤)⁻¹ X) θ*].
> The matrix X⊤(XX⊤)⁻¹ X ∈ ℝᵈˣᵈ is the projection matrix on a random subspace of
> size n ≤ d. By rotational invariance of the Gaussian distribution, this random
> subspace is uniformly distributed among all subspaces, and therefore we can replace
> θ* by ‖θ*‖₂ · eⱼ:
>   E[θ*⊤ X⊤(XX⊤)⁻¹ X θ*] = ‖θ*‖₂² · (1/d) Σⱼ E[eⱼ⊤ X⊤(XX⊤)⁻¹ X eⱼ]
>                         = (‖θ*‖₂² / d) E[tr(X⊤(XX⊤)⁻¹ X)]
>                         = (‖θ*‖₂² / d) · n.
> The bias term is thus equal to ((d − n)/d) · ‖θ*‖₂².

> Therefore, the overall expected risk in the overparameterized regime is
>   E[R(θ̂)] = σ² · n/(d − n − 1) + ‖θ*‖₂² · (d − n)/d.            (12.18)

## Notes
- Summary: combine (12.17) and (12.18):
    if d ≤ n−2: E[R(θ̂)] = σ² · d/(n−d−1)
    if d ≥ n+2: E[R(θ̂)] = σ² · n/(d−n−1) + ‖θ*‖₂² · (d−n)/d
- Both branches are explicitly nonnegative: variance term σ²·(·)/(·) ≥ 0 (Wishart
  trace expectation is positive), bias term ‖θ*‖₂² · (d−n)/d ≥ 0 in the
  overparameterized regime (d ≥ n).
- The "explosion around d = n" is precisely E[tr((X⊤X)⁻¹)] = +∞ for n = d, n = d+1.
- Technique in one line: rotational invariance of isotropic Gaussian + inverse
  Wishart moments + projection-matrix trace = n.
- Anchor scope: the Lean target `double_descent_excess_risk_nonneg` likely
  formalizes the trivial inequality E[R(θ̂)] ≥ 0, i.e., the sum of two nonneg
  terms is nonneg — bypassing the random-matrix combinatorics.
- Ambiguity: textbook does *not* prove a U-shape for d > n in the main text; it is
  Exercise 12.5. The non-negativity property is implicit (variance + bias).

## Prerequisites (Bach's dependency graph)

- [`implicit-bias-full-rank`](./implicit-bias-full-rank.md) — Implicit bias of GD = OLS (full-rank case)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch12_Overparameterized/ImplicitBias.lean`
- **Theorem/def name:** `double_descent_excess_risk_nonneg`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

