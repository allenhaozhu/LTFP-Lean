# ℓ₁ norm: sum of absolute values

**ID:** `l1-norm`  
**Chapter:** Ch08 (Bach §8.3, p. 231)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/l1-norm/`](../../../tasks/l1-norm/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — ℓ₁ norm: sum of absolute values

**Concept ID:** `l1-norm`
**Chapter:** Ch 8
**Section:** §8.3 (Variable Selection by ℓ₁-regularization)
**Pages:** 230–231
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach introduces the ℓ₁-norm at the start of §8.3 (p. 230) as the penalty in the Lasso objective:

> We now consider a computationally efficient alternative to ℓ₀-penalties (namely, using ℓ₁-penalties), by minimizing, for the square loss,
>
>   min   (1/(2n)) ‖y − Φθ‖₂² + **λ‖θ‖₁**.    (8.6)

The ℓ₁-norm itself is the standard sum-of-absolute-values norm on ℝᵈ:

> ‖θ‖₁ = Σⱼ |θⱼ|

(used implicitly throughout §8.3; see also the formula for ∂H(θ, Δ) on p. 233 where the sum-of-absolute-values structure appears explicitly).

It is also identified as the convex envelope of the ℓ₀-penalty on the unit cube (p. 232):

> The ℓ₁-norm is also often introduced as the convex relaxation of the ℓ₀-penalty. Indeed, the ℓ₁-norm is the convex envelope (the largest convex function that is a lower-bound) of the ℓ₀-penalty on the set [−1, 1]ᵈ (the proof is left as an exercise).

## Proof (verbatim)

(definition; standard; not proved in-text)

## Notes

- ‖θ‖₁ = Σⱼ |θⱼ| for θ ∈ ℝᵈ. This is a genuine norm (nonnegative, positively homogeneous, satisfies the triangle inequality).
- Its dual norm is the ℓ_∞ norm (Exercise 8.7, p. 237).
- In §8.3.1, Bach uses the ℓ₁-ball geometry (corners attractive) to motivate sparsity-inducing behavior.
- The ℓ₁-norm is the convex envelope of ‖·‖₀ on [−1, 1]ᵈ (Bach leaves the proof as an exercise).
- **Bach's proof technique** (n/a — definition): standard sum-of-absolute-values; analytical properties (nonnegativity, triangle inequality, invariance under negation) are immediate from the underlying absolute value properties on ℝ.
- Lean target `LTFP/Ch08_Sparse/L1.lean#l1Norm` implements ‖z‖₁ = Σᵢ |zᵢ|.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

- [`l1-norm-eq-zero-of-zero`](./l1-norm-eq-zero-of-zero.md) — ℓ₁ of zero vector = 0
- [`l1-norm-fin-one`](./l1-norm-fin-one.md) — ℓ₁ norm on Fin 1 is |z 0|
- [`l1-norm-neg`](./l1-norm-neg.md) — ℓ₁ norm is invariant under negation
- [`l1-norm-nonneg`](./l1-norm-nonneg.md) — ℓ₁ norm is nonnegative
- [`l1-norm-triangle`](./l1-norm-triangle.md) — ℓ₁ norm triangle inequality (alias)
- [`l1-triangle`](./l1-triangle.md) — ℓ₁ norm satisfies the triangle inequality
- [`soft-threshold`](./soft-threshold.md) — Soft-thresholding operator (closed form for 1-D Lasso)

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch08_Sparse/L1.lean`
- **Theorem/def name:** `l1Norm`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

