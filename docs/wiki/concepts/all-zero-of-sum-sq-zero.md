# Sum of squared residuals = 0 ⇒ each residual = 0

**ID:** `all-zero-of-sum-sq-zero`  
**Chapter:** Ch03 (Bach §3.5)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/all-zero-of-sum-sq-zero/`](../../../tasks/all-zero-of-sum-sq-zero/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Sum of squared residuals = 0 ⇒ each residual = 0

**Concept ID:** `all-zero-of-sum-sq-zero`
**Chapter:** Ch 3
**Section:** 3.5 (Fixed Design Setting), via §3.3 cost function
**Pages:** 46–50
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach does not state this hard direction explicitly; it is the converse
of `sum-sq-residuals-zero` and the algebraic fact that a sum of
nonnegative reals can vanish only if every summand vanishes. Combined
with `sum-sq-residuals-zero` it yields the equivalence

```
Σᵢ (yᵢ − ϕ(xᵢ)ᵀ θ)² = 0   ⇔   ∀ i, yᵢ − ϕ(xᵢ)ᵀ θ = 0.
```

From Bach's matrix form (§3.3, eq. (3.2), p. 46):

> `R̂(θ) = (1/n) ‖y − Φθ‖²₂`,
> where `‖α‖²₂ = Σⱼ αⱼ²`.

Hence `‖y − Φθ‖²₂ = 0` iff `y = Φθ`.

## Proof (verbatim)

Bach gives no explicit proof. The standard argument:

A sum `Σⱼ αⱼ²` of squares of real numbers is zero iff every `αⱼ = 0`.
Equivalently, the squared ℓ₂-norm is a positive-definite quadratic form
on ℝⁿ: `‖α‖₂ = 0 ⇔ α = 0`.

Bach uses this fact implicitly when discussing the OLS normal equation
and perfect interpolation (§3.6, "Least-squares in high dimensions",
p. 56):

> When `d = n` and `Φ` is a square invertible matrix, `θ = Φ⁻¹y` leads
> to `y = Φθ`; that is, OLS will lead to a perfect fit …

Here "perfect fit" `y = Φθ` is precisely the statement that every
residual vanishes, derived from `‖y − Φθ‖²₂ = 0` via this lemma.

## Notes

- Hard direction of the algebraic equivalence
  `Σ (residual)² = 0 ⇔ every residual = 0`.
- Standard proof: `Σⱼ αⱼ² = 0` with each `αⱼ² ≥ 0` forces every
  `αⱼ² = 0`, hence `αⱼ = 0`.
- The Lean proof at
  `LTFP/Ch03_LinearLeastSquares/FixedDesign.lean#all_zero_of_sum_sq_eq_zero`
  uses `Finset.sum_eq_zero_iff_of_nonneg` and `sq_eq_zero_iff`.
- Bach uses this only implicitly when reading off `y = Φθ` from a zero
  empirical risk.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch03_LinearLeastSquares/FixedDesign.lean`
- **Theorem/def name:** `all_zero_of_sum_sq_eq_zero`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

