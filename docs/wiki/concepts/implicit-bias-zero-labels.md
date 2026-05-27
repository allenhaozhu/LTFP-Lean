# OLS with zero labels yields zero estimator

**ID:** `implicit-bias-zero-labels`  
**Chapter:** Ch12 (Bach §12.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `OLS`

## Statement

_See textbook excerpt below or [`tasks/implicit-bias-zero-labels/`](../../../tasks/implicit-bias-zero-labels/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — OLS with zero labels yields zero estimator

**Concept ID:** `implicit-bias-zero-labels`
**Chapter:** Ch 12
**Section:** 12.1.1 Least-Squares Regression
**Pages:** 344-345
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
> [Implicit-bias formula, from §12.1.1, eq. (12.1)-(12.2)]
> When started at θ₀ = 0, GD techniques (whether stochastic or not) will always have
> iterates θ_t that are linear combinations of rows of X; that is, of the form
> θ_t = X⊤ α_t for some α_t ∈ ℝⁿ. … Since Xθ_t converges to y, Xθ_t = XX⊤ α_t
> converges to y. Since K = XX⊤ is invertible, this means that α_t converges to
> K⁻¹y, and thus θ_t = X⊤ α_t converges to X⊤ K⁻¹ y.

> Equivalently, the closed-form GD limit is
>   θ̂(y) := X⊤(XX⊤)⁻¹ y = X⁺ y.

## Proof (verbatim)
> [Direct algebraic consequence — Bach does not state this corollary explicitly, but
> it is immediate from the closed-form formula θ̂ = X⊤(XX⊤)⁻¹ y.]
> If y = 0 ∈ ℝⁿ, then
>   θ̂(0) = X⊤(XX⊤)⁻¹ · 0 = 0 ∈ ℝᵈ.
> Equivalently, in dynamics form: with y = 0, eq. (12.1) gives
>   Xθ_t − 0 = (I − (γ/n)XX⊤)^t · (−0) = 0,
> so θ_t = 0 for all t when starting from θ₀ = 0 (which is the standard choice).

## Notes
- This is a trivial corollary of `implicit-bias-full-rank`: the implicit-bias map
  y ↦ X⊤(XX⊤)⁻¹ y is linear in y, hence sends 0 ↦ 0.
- Lean target `implicitBias_zero_labels` anchors the identity θ̂(0) = 0.
- Bach does not state it as a separate lemma; it is implicit in eq. (12.2): the
  Lagrangian dual sup_α [α⊤y − ½ α⊤Kα] at y=0 is uniquely attained at α = 0, hence
  θ* = X⊤ α = 0.
- Technique in one line: linearity of the pseudoinverse map.
- No ambiguities.

## Prerequisites (Bach's dependency graph)

- [`implicit-bias-full-rank`](./implicit-bias-full-rank.md) — Implicit bias of GD = OLS (full-rank case)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch12_Overparameterized/ImplicitBias.lean`
- **Theorem/def name:** `implicitBias_zero_labels`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

