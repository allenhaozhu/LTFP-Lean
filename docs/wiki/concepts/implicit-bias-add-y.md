# Implicit bias linear in labels

**ID:** `implicit-bias-add-y`  
**Chapter:** Ch12 (Bach §12.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/implicit-bias-add-y/`](../../../tasks/implicit-bias-add-y/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Implicit bias linear in labels (additivity)

**Concept ID:** `implicit-bias-add-y`
**Chapter:** Ch 12
**Section:** 12.1.1 Least-Squares Regression
**Pages:** 344-345
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
> [Bach, §12.1.1, eq. (12.1)-(12.2), closed-form GD limit.]
> Since K = XX⊤ is invertible, … θ_t = X⊤ α_t converges to X⊤ K⁻¹ y. One may have
> recognized in X⊤ K⁻¹ = X⊤(XX⊤)⁻¹ the pseudo-inverse of X.

> Define the implicit-bias map T : ℝⁿ → ℝᵈ by T(y) := X⊤(XX⊤)⁻¹ y. The matrix
> X⊤(XX⊤)⁻¹ is a fixed linear map (depends only on X), hence T is linear:
>   T(y₁ + y₂) = T(y₁) + T(y₂)        for all y₁, y₂ ∈ ℝⁿ.

## Proof (verbatim)
> [Trivial corollary of the closed-form expression; Bach does not isolate it.]
> By definition, T(y) = M · y where M := X⊤(XX⊤)⁻¹ ∈ ℝᵈˣⁿ is a fixed matrix.
> Matrix multiplication distributes over vector addition:
>   T(y₁ + y₂) = M(y₁ + y₂) = M y₁ + M y₂ = T(y₁) + T(y₂).
>
> Equivalently, from the Lagrangian dual eq. (12.2):
>   sup_α α⊤(y₁ + y₂) − ½ α⊤ K α
> has unique optimizer α* = K⁻¹(y₁ + y₂) = K⁻¹y₁ + K⁻¹y₂ (linearity of K⁻¹),
> and θ* = X⊤ α* = T(y₁) + T(y₂).

## Notes
- Lean target `implicitBias_add_y` anchors the additivity property of the implicit-
  bias map y ↦ X⊤(XX⊤)⁻¹y.
- Source justification: §12.1.1 derives the closed form X⊤(XX⊤)⁻¹y as the GD limit
  and identifies it with the Moore–Penrose pseudoinverse X⁺ y; both are linear
  operators in y.
- Technique in one line: pseudoinverse / linear-map distributivity.
- Bach does not state this as a separate lemma — it is a Lean-side decomposition
  useful for proving the full implicit-bias identity from elementary
  parts (zero, add, smul, sub).
- No ambiguities.

## Prerequisites (Bach's dependency graph)

- [`implicit-bias-full-rank`](./implicit-bias-full-rank.md) — Implicit bias of GD = OLS (full-rank case)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch12_Overparameterized/ImplicitBias.lean`
- **Theorem/def name:** `implicitBias_add_y`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

