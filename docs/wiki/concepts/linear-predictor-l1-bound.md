# Generalization bound for L¹-regularized linear predictors (Lasso)

**ID:** `linear-predictor-l1-bound`  
**Chapter:** Ch08 (Bach §8.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** in_lean_rademacher  
**Topic tags:** `Lasso/Sparse`

## Statement

_See textbook excerpt below or [`tasks/linear-predictor-l1-bound/`](../../../tasks/linear-predictor-l1-bound/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Generalization bound for L¹-regularized linear predictors (Lasso)

**Concept ID:** `linear-predictor-l1-bound`
**Chapter:** Ch 8
**Section:** §8.3.2 (Slow Rates — Random Design); cross-ref §4.5.4 / §4.5.5
**Pages:** 234–236
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Verbatim from §8.3.2 "Slow Rates–Random Design" (pp. 234–236):

> In this section, we consider Lipschitz-continuous loss functions and, thus, an empirical risk of the form
>
>   R̂(θ) = (1/n) Σᵢ ℓ(yᵢ, ϕ(xᵢ)ᵀθ),
>
> with ℓ having the Lipschitz constant G with respect to the second variable. We assume that the expected risk R(θ) = E[ℓ(y, ϕ(x)ᵀθ)] is minimized at a certain θ\* ∈ ℝᵈ, and for simplicity, we consider the estimator θ̂_D obtained by minimizing R̂(θ) with the constraint that ‖θ‖₁ ≤ D, where we will use tools from section 4.5.4 (we could also consider the penalized formulation using proposition 4.7 in section 4.5.5). We assume that ‖ϕ(x)‖_∞ ≤ R almost surely.
>
> From section 4.5.4, we get that
>
>   E[R(θ̂_D)] ≤  inf_{‖θ‖₁≤D}  R(θ) + 4G · Rₙ(F_D),
>
> where Rₙ(F_D) is the Rademacher complexity of the set of linear predictors with weight vectors bounded by D in ℓ₁-norm, which we can compute as
>
>   Rₙ(F_D) = E[ sup_{‖θ‖₁≤D} (1/n) Σᵢ εᵢᴿ ϕ(xᵢ)ᵀ θ ] = D · E[ ‖ (1/n) Σᵢ εᵢᴿ ϕ(xᵢ) ‖_∞ ],
>
> where εᵢᴿ ∈ {−1, 1} are Rademacher random variables. We can now compute a bound on the expectation, first conditioned on the data. Indeed, εᵢᴿ ϕ(xᵢ) has conditional zero mean and is bounded in absolute value by R. It is thus sub-Gaussian with constant R² (see section 1.2.1, which implies that (1/n) Σᵢ εᵢᴿ ϕ(xᵢ) is sub-Gaussian with constant R²/n). We can then use proposition 1.5 to find that the maximum of the 2d sub-Gaussian variables is less than [2R² log(2d)/n]^(1/2). This leads to
>
>   **E[R(θ̂_D)]  ≤  inf_{‖θ‖₁≤D} R(θ)  +  4GRD · √(2 log(2d) / n).**
>
> When D is large enough (e.g., D = ‖θ\*‖₁), then we get an excess risk bounded by 4GRD · √(2 log(2d) / n). If θ\* has only k nonzeros, its ℓ₁-norm will typically grow as O(k), and we see a high-dimensional phenomenon with a bound proportional to k √(log d) / √n, where d can be much larger than n, so long as k² log(d)/n is small. This is a slow rate because of the dependence in n, which is O(1/√n) rather than in O(1/n).

## Proof (verbatim)

The proof is the chained computation above (Rademacher symmetrization from §4.5.4, identification of the Rademacher complexity of the ℓ₁-ball, sub-Gaussian maximum bound from §1.2.4, proposition 1.5).

Key steps in Bach's exposition (verbatim above, summarized):

1. **Symmetrization (from §4.5.4):** E[R(θ̂_D)] ≤ inf R(θ) + 4G · Rₙ(F_D).
2. **Rademacher of ℓ₁-ball:** Rₙ(F_D) = D · E[‖(1/n) Σᵢ εᵢᴿ ϕ(xᵢ)‖_∞] (sup over ‖θ‖₁ ≤ D of ⟨θ, v⟩ equals D · ‖v‖_∞).
3. **Sub-Gaussian per coordinate:** εᵢᴿ ϕ(xᵢ)_j coordinate-wise bounded by R, so sub-Gaussian with constant R²; the mean of n such is sub-Gaussian with constant R²/n.
4. **Maximum of 2d sub-Gaussians:** by proposition 1.5 (Massart-type bound), max ≤ √(2R² log(2d)/n).
5. **Combine:** Rₙ(F_D) ≤ DR √(2 log(2d)/n), giving the displayed bound.

## Notes

- This is the **slow-rate (1/√n) Lasso generalization bound** in random-design with Lipschitz loss.
- Prerequisite (from registry): `rademacher-tail-bound-separable`. Specifically, the ℓ₁-ball Rademacher computation invokes §4.5.4 (parallel structure to `linear_predictor_l2_bound`, both via separable Rademacher tail).
- **Bach's proof technique**: (a) Rademacher symmetrization, (b) compute Rademacher complexity of the constraint set via dual-norm trick (sup over ℓ₁-ball of ⟨θ, v⟩ = D ‖v‖_∞), (c) sub-Gaussian maximum bound (Massart).
- The factor "2d" in log(2d) comes from the union bound over both ±j directions of the ℓ_∞-norm.
- Rate: 4GRD √(2 log(2d) / n); when D ≍ ‖θ\*‖₁ ≍ k, the rate is 4GR · k · √(log d / n), giving the high-dim phenomenon "d can be much larger than n if k² log(d)/n → 0".
- **Flagged ambiguity:** Bach writes "4G · Rₙ(F_D)" using a contraction-type bound; the factor of 4 hides the Lipschitz contraction (factor 2) + symmetrization (factor 2). In Lean, this is the same constant chain as in `linear_predictor_l2_bound`.
- Lean target `LTFP/Foundations/Main.lean#linear_predictor_l1_bound` reuses the `in_lean_rademacher` foundation (status: `done`).

## Prerequisites (Bach's dependency graph)

- [`rademacher-tail-bound-separable`](./rademacher-tail-bound-separable.md) — Tail bound on uniform deviation, separable hypothesis class

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = in_lean_rademacher`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/Main.lean`
- **Theorem/def name:** `linear_predictor_l1_bound`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

