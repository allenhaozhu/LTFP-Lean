# Sum of squared residuals is nonneg

**ID:** `sum-sq-residuals-nonneg`  
**Chapter:** Ch03 (Bach §3.5)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/sum-sq-residuals-nonneg/`](../../../tasks/sum-sq-residuals-nonneg/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Sum of squared residuals is nonneg

**Concept ID:** `sum-sq-residuals-nonneg`
**Chapter:** Ch 3
**Section:** 3.5 (Fixed Design Setting), via §3.3 cost function
**Pages:** 46–50
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach does not state nonnegativity of the residual sum of squares as a
named proposition; it is an immediate consequence of how the cost
function is defined (Bach, §3.3, eq. (3.2), p. 46):

> The cost function shown in equation (3.1) can be rewritten in matrix
> notation. Let `y = (y₁, …, yₙ)ᵀ ∈ ℝⁿ` be the vector of outputs
> (sometimes called the *response vector*), and `Φ ∈ ℝⁿˣᵈ` the matrix
> of inputs, whose rows are `ϕ(xᵢ)ᵀ`. It is called the **design matrix**
> or **data matrix**. In this notation, the empirical risk is
>
>     R̂(θ) = (1/n) ‖y − Φθ‖²₂,                    (3.2)
>
> where `‖α‖²₂ = Σⱼ αⱼ²` is the squared ℓ₂-norm of `α`.

The sum of squared residuals `Σᵢ (yᵢ − ϕ(xᵢ)ᵀ θ)² = ‖y − Φθ‖²₂ ≥ 0`
because it is a sum of squares of real numbers.

## Proof (verbatim)

Bach gives no explicit proof: nonnegativity of the squared ℓ₂-norm is
treated as definitional. Bach's definition of the squared ℓ₂-norm (p. 46)
makes the nonnegativity transparent:

> `‖α‖²₂ = Σⱼ αⱼ²`

A sum of squares of real numbers is nonnegative.

## Notes

- Trivial corollary of the definition `‖·‖²₂ = Σ (·)²` (Bach, eq. 3.2).
- The Lean proof at
  `LTFP/Ch03_LinearLeastSquares/FixedDesign.lean#sum_sq_residuals_nonneg`
  is `Finset.sum_nonneg` over `sq_nonneg`.
- Bach does not call this out separately — it is the implicit reason
  the OLS objective `R̂(θ) = (1/n) ‖y − Φθ‖²₂` is nonnegative and the
  minimum is attained.
- Mathlib status: in-mathlib (sum of squares ≥ 0).

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch03_LinearLeastSquares/FixedDesign.lean`
- **Theorem/def name:** `sum_sq_residuals_nonneg`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

