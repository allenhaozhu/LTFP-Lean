# Zero residual ⇒ zero sum of squares

**ID:** `sum-sq-residuals-zero`  
**Chapter:** Ch03 (Bach §3.5)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/sum-sq-residuals-zero/`](../../../tasks/sum-sq-residuals-zero/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Zero residual ⇒ zero sum of squares

**Concept ID:** `sum-sq-residuals-zero`
**Chapter:** Ch 3
**Section:** 3.5 (Fixed Design Setting), via §3.3 cost function
**Pages:** 46–50
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach does not state this corollary directly; it is the easy direction of
the algebraic equivalence (sum of squared residuals = 0 iff each residual
= 0) underlying the discussion of perfect interpolation. From Bach's
matrix-form cost (eq. (3.2), p. 46):

> `R̂(θ) = (1/n) ‖y − Φθ‖²₂`,
> where `‖α‖²₂ = Σⱼ αⱼ²` is the squared ℓ₂-norm.

If every residual `yᵢ − ϕ(xᵢ)ᵀ θ = 0`, the squared ℓ₂-norm `‖y − Φθ‖²₂`
is a sum whose every term is `0² = 0`, so the total is `0`. Symbolically:

```
(∀ i, residual i = 0) ⇒ Σᵢ (residual i)² = 0.
```

## Proof (verbatim)

Bach treats this as obvious from the definition; no explicit proof is
given.

Bach uses this fact implicitly when discussing perfect interpolation in
§3.6 (Ridge Least-Squares Regression, "Least-squares in high dimensions",
p. 56):

> When `d/n` approaches 1, we are essentially memorizing the
> observations `yᵢ` (that is, e.g., when `d = n` and `Φ` is a square
> invertible matrix, `θ = Φ⁻¹ y` leads to `y = Φθ`; that is, OLS will
> lead to a perfect fit, …)

A "perfect fit" means every residual is zero, hence the sum of squared
residuals is zero — exactly this lemma's content.

## Notes

- Easy direction of the algebraic equivalence
  `Σ (residual)² = 0 ⇔ every residual = 0`.
- The Lean proof at
  `LTFP/Ch03_LinearLeastSquares/FixedDesign.lean#sum_sq_residuals_eq_zero_of_zero`
  is `Finset.sum_eq_zero` applied to the pointwise zero residual.
- Bach uses this only implicitly when discussing perfect fits / over-
  parameterization in §3.6.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch03_LinearLeastSquares/FixedDesign.lean`
- **Theorem/def name:** `sum_sq_residuals_eq_zero_of_zero`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

