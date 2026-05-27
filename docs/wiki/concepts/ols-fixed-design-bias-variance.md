# Fixed-design OLS bias-variance decomposition

**ID:** `ols-fixed-design-bias-variance`  
**Chapter:** Ch03 (Bach §3.5.1, p. 52)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `OLS`

## Statement

_See textbook excerpt below or [`tasks/ols-fixed-design-bias-variance/`](../../../tasks/ols-fixed-design-bias-variance/) if available._

## Bach's textbook treatment

# Book excerpt — `ols-fixed-design-bias-variance` (Bach 2024 §3.5.1, p. 52)

> **Proposition 3.3 (Risk decomposition for OLS – fixed design).**
> Under the linear model `y = Φ θ_* + ε` with `E[ε] = 0`,
> `E[‖ε‖²] = n σ²`, the population risk satisfies `R* = σ²` and for
> any `θ ∈ ℝᵈ`,
>
>     R(θ) − R* = ‖θ − θ_*‖²_{Σ̂},     where Σ̂ = (1/n) ΦᵀΦ.
>
> *Proof sketch.* Expanding the square in `R(θ) = E_y[(1/n)‖y − Φθ‖²]`
> with `y = Φ θ_* + ε`:
>
>     (1/n)‖y − Φθ‖² = (1/n)‖Φ θ_* + ε − Φθ‖²
>                    = (1/n)‖Φ(θ_* − θ)‖² + (1/n)‖ε‖²
>                          + (2/n)·(Φ(θ_* − θ))ᵀ ε.
>
> Taking expectations over `ε` (with `E[ε] = 0` and `E[‖ε‖²] = n σ²`)
> kills the cross-term and the noise term equals σ², giving
> `R(θ) − σ² = (1/n)‖Φ(θ_* − θ)‖² = ‖θ_* − θ‖²_{Σ̂}`.

## Lean target — pure-algebra core identity

The probability layer is heavy. **Target the deterministic algebraic
identity** that drives the proof (the second line of the sketch). It
needs no expectation operator and no probability space:

    theorem ols_excess_risk {n d : ℕ}
        (X : Matrix (Fin n) (Fin d) ℝ)
        (theta_star theta eps : Fin n → ℝ)  -- treat θ_star, θ as ℝⁿ images
        : ‖X.mulVec theta_star + eps - X.mulVec theta‖^2 =
            ‖X.mulVec theta_star - X.mulVec theta‖^2
            + ‖eps‖^2
            + 2 * ((X.mulVec theta_star - X.mulVec theta) ⬝ᵥ eps)

(Adjust the function signature so the dimensions work — what matters
is the identity `‖a − b + ε‖² = ‖a − b‖² + ‖ε‖² + 2⟨a − b, ε⟩` for
`a = Xθ_*`, `b = Xθ`. You can simplify by introducing `r := Xθ_* − Xθ`
as a single vector.)

Acceptable simplification: drop the design matrix entirely and prove
the underlying identity directly:

    theorem ols_excess_risk {n : ℕ} (r eps : EuclideanSpace ℝ (Fin n)) :
        ‖r + eps‖^2 = ‖r‖^2 + ‖eps‖^2 + 2 * (r ⬝ᵥ eps)

(this is just `inner_add_add_self` / `EuclideanSpace.norm_add_sq` —
literally the polar identity).

## Acceptable smaller fallback

If the polar identity above gets stuck because of `EuclideanSpace`
typeclasses, fall back to a `PiLp` form or use raw `Fin n → ℝ`
together with explicit sums:

    theorem ols_excess_risk {n : ℕ} (r eps : Fin n → ℝ) :
        ∑ i, (r i + eps i)^2 = ∑ i, r i^2 + ∑ i, eps i^2
                                + 2 * ∑ i, r i * eps i

This is `Finset.sum_add_distrib` + `add_sq` repeatedly — pure ring
algebra, no Mathlib analysis at all.

**No `sorry`, no `admit`, no `True`** — pick whichever lands cleanly.
The point of the ticket is to land the algebraic core; the probability
layer is left for a future Phase-2 wave.

## Prerequisites (Bach's dependency graph)

- [`ols-closed-form`](./ols-closed-form.md) — OLS closed form: β̂ = (XᵀX)⁻¹Xᵀy

## Dependents (concepts that use this)

- [`ridge-bias-variance`](./ridge-bias-variance.md) — Ridge bias-variance trade-off (fixed design)

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch03_LinearLeastSquares/FixedDesign.lean`
- **Theorem/def name:** `ols_excess_risk`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

