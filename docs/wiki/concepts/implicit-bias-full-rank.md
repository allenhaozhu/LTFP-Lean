# Implicit bias of GD = OLS (full-rank case)

**ID:** `implicit-bias-full-rank`  
**Chapter:** Ch12 (Bach §12.1, p. 344)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `OLS`, `Gradient-descent`

## Statement

_See textbook excerpt below or [`tasks/implicit-bias-full-rank/`](../../../tasks/implicit-bias-full-rank/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Implicit bias of GD = OLS (full-rank case)

**Concept ID:** `implicit-bias-full-rank`
**Chapter:** Ch 12
**Section:** 12.1.1 Least-Squares Regression
**Pages:** 344-345
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
> Now we consider the least-squares objective function F(θ) = (1/(2n))·‖y − Xθ‖₂² from
> chapter 3, with y ∈ ℝⁿ, X ∈ ℝⁿˣᵈ such that d ≥ n and (for simplicity) XX⊤ ∈ ℝⁿˣⁿ
> invertible (this is the kernel matrix). There are thus infinitely many (i.e., a whole
> affine subspace of) solutions such that y = Xθ since the column space of X is the
> entire space ℝⁿ and θ has dimension d ≥ n. We apply GD with step size
> γ < 1/L = λ_max((1/n)X⊤X)⁻¹, which is equal to λ_max((1/n)XX⊤)⁻¹, starting from
> θ₀ = 0 and leading to θ_t = θ_{t−1} − (γ/n)·X⊤(Xθ_{t−1} − y).

> Therefore, we have
>     Xθ_t − y = Xθ_{t−1} − y − (γ/n)·XX⊤(Xθ_{t−1} − y) = (I − (γ/n)XX⊤)(Xθ_{t−1} − y),
> leading to, by recursion,
>     Xθ_t − y = (I − (γ/n)XX⊤)^t (Xθ₀ − y) = (I − (γ/n)XX⊤)^t (−y).   (12.1)

> We thus get ‖Xθ_t − y‖₂² ≤ (1 − (γ/n)λ_min(XX⊤))^{2t} · ‖y‖₂², and hence linear
> convergence of Xθ_t toward y, with a convergence rate depending on the condition
> number of the kernel matrix XX⊤.

## Proof (verbatim)
> Moreover, when started at θ₀ = 0, GD techniques (whether stochastic or not) will
> always have iterates θ_t that are linear combinations of rows of X; that is, of the
> form θ_t = X⊤ α_t for some α_t ∈ ℝⁿ. (This is an alternative algorithmic version of
> the representer theorem from chapter 7.)
>
> Since Xθ_t converges to y, Xθ_t = XX⊤ α_t converges to y. Since K = XX⊤ is
> invertible, this means that α_t converges to K⁻¹y, and thus θ_t = X⊤ α_t converges
> to X⊤ K⁻¹ y. One may have recognized in X⊤ K⁻¹ = X⊤(XX⊤)⁻¹ the pseudo-inverse of X,
> and hence X⊤ K⁻¹ y is the minimum ℓ₂-norm solution of {Xθ = y}, as shown next with
> standard Lagrangian duality (Boyd and Vandenberghe, 2004):
>
>     inf_{θ∈ℝᵈ} (1/2)‖θ‖₂²  s.t.  y = Xθ
>       = inf_{θ}  sup_{α∈ℝⁿ}  (1/2)‖θ‖₂² + α⊤(y − Xθ)
>       = sup_α  α⊤ y − (1/2)‖X⊤α‖₂²    (with θ = X⊤α at optimum)
>       = sup_α  α⊤ y − (1/2) α⊤ K α.    (12.2)
>
> The problem in equation (12.2) is exactly solved for α = K⁻¹ y, with θ = X⊤ α at
> optimum.

## Notes
- Setup: overparameterized (d ≥ n), zero initialization θ₀ = 0, GD step size γ < 1/L.
- Representer-theorem corollary: iterates remain in row-span(X), so θ_t = X⊤ α_t.
- Closed-form limit: θ_∞ = X⊤(XX⊤)⁻¹ y = X⁺ y, the minimum ℓ₂-norm interpolator
  (Moore–Penrose pseudoinverse).
- One-line technique: kernel-trick + invertibility of K = XX⊤ + zero init ⇒ implicit
  ℓ₂-min bias.
- Łojasiewicz inequality (eq. 12.3) gives linear convergence with µ = (1/n)·λ⁺_min(K).
- Ambiguity for Lean: the textbook statement uses the convergence limit (t → ∞); the
  Lean target `implicitBias_full_rank_eq_ols` likely anchors the algebraic identity
  X⊤(XX⊤)⁻¹ y = OLS-pseudoinverse output, dropping the dynamic/iterative content.

## Prerequisites (Bach's dependency graph)

- [`gradient-descent-foundation`](./gradient-descent-foundation.md) — Gradient descent foundation: gdStep update map
- [`ols-closed-form`](./ols-closed-form.md) — OLS closed form: β̂ = (XᵀX)⁻¹Xᵀy

## Dependents (concepts that use this)

- [`double-descent-nonneg`](./double-descent-nonneg.md) — Double-descent excess risk nonnegativity anchor
- [`implicit-bias-add-y`](./implicit-bias-add-y.md) — Implicit bias linear in labels
- [`implicit-bias-smul-y`](./implicit-bias-smul-y.md) — Implicit bias homogeneous in labels
- [`implicit-bias-sub-y`](./implicit-bias-sub-y.md) — Implicit bias on subtraction
- [`implicit-bias-zero-labels`](./implicit-bias-zero-labels.md) — OLS with zero labels yields zero estimator
- [`ntk-symmetry-anchor`](./ntk-symmetry-anchor.md) — NTK kernel symmetry algebraic anchor

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch12_Overparameterized/ImplicitBias.lean`
- **Theorem/def name:** `implicitBias_full_rank_eq_ols`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

