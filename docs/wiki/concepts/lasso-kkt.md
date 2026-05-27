# Scalar Lasso KKT (soft-thresholding minimizer)

**ID:** `lasso-kkt`  
**Chapter:** Ch08 (Bach §8.2, p. 230)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** B  
**Mathlib status:** partial  
**Vendored status:** new  
**Topic tags:** `Sub-Gaussian`, `Lasso/Sparse`, `Convex`

## Statement

Scalar form: minimizer of ½(b−c)² + λ|b| is the soft-threshold S_λ(c). Proved directly via case split + nlinarith; no subdifferential calculus needed. Vector form Xᵀ(Xβ⋆−y) ∈ −λ ∂‖β⋆‖₁ reduces to this scalar statement when XᵀX = I; the general case requires subdifferential calculus for ℓ₁, which is partial in Mathlib (Mathlib.Analysis.NormedSpace.Lp / Mathlib.Analysis.Convex.SpecificFunctions.Basic). Promote when the ℓ₁ subgradient set lands upstream.

## Bach's textbook treatment

# Bach textbook excerpt — Scalar Lasso KKT (soft-thresholding minimizer)

**Concept ID:** `lasso-kkt`
**Chapter:** Ch 8
**Section:** 8.3.1 (One-dimensional problem); cross-ref §8.3 optimality conditions
**Pages:** 232 (also relevant: optimality conditions discussion, pp. 233–234)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Verbatim from §8.3.1, "One-dimensional problem" (p. 232):

> Another classical way to understand the sparsity-inducing effect is to consider the one-dimensional problem:
>
>                                 min F(θ) = ½ (y − θ)² + λ|θ|.
>                                  θ∈R
>
> Since F is strongly convex, it has a unique minimizer θ*_λ(y). For λ = 0 (no regularization), we have θ*_0(y) = y, while for λ > 0, by computing the left and right derivatives at zero (the proof is left as an exercise), one can check that
>
>   θ*_λ(y) = 0       if |y| ≤ λ,
>   θ*_λ(y) = y − λ   for y > λ,
>   θ*_λ(y) = y + λ   for y < −λ,
>
> which can be put together as
>
>   θ*_λ(y) = max{|y| − λ, 0} · sign(y),
>
> which is depicted here. This is referred to as "iterative soft thresholding" (this will be useful for the proximal methods discussed next). … Note that the minimizer is either set to zero or shrunk toward zero.

The relevant general (multivariate) optimality conditions appear in §8.3.1 "Optimality conditions (◆)" (pp. 233–234):

> For H(θ) = F(θ) + λ‖θ‖₁, we have
>
>   ∂H(θ, Δ) = F'(θ)ᵀΔ + λ Σ_{j, θⱼ≠0} sign(θⱼ)Δⱼ + λ Σ_{j, θⱼ=0} |Δⱼ|.
>
> It is separable in Δⱼ, j = 1, …, d, and it is nonnegative for all j, if and only if all components that depend on Δⱼ are nonnegative.
> When θⱼ ≠ 0, then this requires F'(θ)ⱼ + λ sign(θⱼ) = 0, while when θⱼ = 0, we need F'(θ)ⱼΔⱼ + λ|Δⱼ| ≥ 0 for all Δⱼ, which is equivalent to |F'(θ)ⱼ| ≤ λ. This leads to the following set of conditions:
>
>   F'(θ)ⱼ + λ sign(θⱼ) = 0,  ∀j ∈ {1, …, d} such that θⱼ ≠ 0,
>   |F'(θ)ⱼ| ≤ λ,              ∀j ∈ {1, …, d} such that θⱼ = 0.

## Proof (verbatim)

Bach explicitly states "(the proof is left as an exercise)" for the scalar case. (sketch) — the standard derivation by left/right derivatives at zero:

For y > λ: F'(θ) = (θ − y) + λ at θ > 0 vanishes at θ = y − λ > 0; strict convexity ⇒ unique minimizer.
For y < −λ: symmetric: minimizer at θ = y + λ < 0.
For |y| ≤ λ: at θ = 0, the right derivative is (0 − y) + λ = λ − y ≥ 0 (since y ≤ λ) and the left derivative is (0 − y) − λ = −y − λ ≤ 0 (since y ≥ −λ). Both subdifferential bounds straddle 0, so 0 is the minimum.

Combined: θ*_λ(y) = sign(y) · max(|y| − λ, 0).

## Notes

- This is the "lasso-kkt" carrier — the scalar minimizer formula and its KKT certification.
- **Bach's proof technique**: strong convexity of (y − θ)²/2 + λ|θ| ⇒ unique minimizer; left/right derivative analysis at θ = 0 to handle the nondifferentiable point; standard first-order condition F'(θ) = 0 in the differentiable regions.
- The general optimality conditions on pp. 233–234 are the multivariate KKT analogue that subsumes the scalar case: when θⱼ ≠ 0, F'(θ)ⱼ + λ sign(θⱼ) = 0; when θⱼ = 0, |F'(θ)ⱼ| ≤ λ.
- For the scalar Lasso with F(θ) = ½(y − θ)², we have F'(θ) = θ − y, so the KKT conditions reduce to: θ ≠ 0 ⇒ θ = y − λ sign(θ); θ = 0 ⇒ |y| ≤ λ.
- **Flagged ambiguity:** Bach uses sign(0) = 0 implicitly (the soft-threshold formula collapses to 0 when |y| ≤ λ, consistent with any convention for sign(0)). The Lean formalization should pick a sign convention (typically sign(0) = 0) and document it.
- **High-stakes registry flag:** the registry flagged `lasso-kkt` as an orphan high-stakes concept. This excerpt anchors the Lean carrier in `LTFP/Ch08_Sparse/L1.lean#lasso_kkt_scalar`.

## Prerequisites (Bach's dependency graph)

- [`soft-threshold`](./soft-threshold.md) — Soft-thresholding operator (closed form for 1-D Lasso)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = partial`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch08_Sparse/L1.lean`
- **Theorem/def name:** `lasso_kkt_scalar`
- **Status:** B
- **Primary closing commit:** `947f879` (theorem `lasso_kkt_abstract`)
- **Audit class:** **B**
- **Audit notes:** Takes `IsL1Subgradient` predicate as HYPOTHESIS (the gradient-of-loss piece is the data)

## Audit history (if any)

- commit `947f879` — theorem `lasso_kkt_abstract` — classified **B** in PROGRESS.md §10 (Takes `IsL1Subgradient` predicate as HYPOTHESIS (the gradient-of-loss piece is the data))

## Notes / open questions

- Carrier is **parametric** — at least one substantive hypothesis is passed through, not discharged.
- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

