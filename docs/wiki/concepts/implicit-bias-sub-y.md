# Implicit bias on subtraction

**ID:** `implicit-bias-sub-y`  
**Chapter:** Ch12 (Bach §12.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/implicit-bias-sub-y/`](../../../tasks/implicit-bias-sub-y/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Implicit bias on subtraction

**Concept ID:** `implicit-bias-sub-y`
**Chapter:** Ch 12
**Section:** 12.1.1 Least-Squares Regression
**Pages:** 344-345
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
> [Bach, §12.1.1, eq. (12.1)-(12.2), closed-form GD limit.]
> θ_t = X⊤ α_t converges to X⊤ K⁻¹ y = X⊤(XX⊤)⁻¹ y, the pseudoinverse output.

> The implicit-bias map T(y) := X⊤(XX⊤)⁻¹ y is linear, hence respects subtraction:
>   T(y₁ − y₂) = T(y₁) − T(y₂)        for all y₁, y₂ ∈ ℝⁿ.

## Proof (verbatim)
> [Trivial corollary of additivity + homogeneity; Bach does not isolate it.]
> By definition, T(y) = M y where M := X⊤(XX⊤)⁻¹ is a fixed matrix. Linearity gives
>   T(y₁ − y₂) = M(y₁ − y₂) = M y₁ − M y₂ = T(y₁) − T(y₂).
>
> Equivalently, this follows by combining `implicit-bias-add-y` and
> `implicit-bias-smul-y` with c = −1:
>   T(y₁ − y₂) = T(y₁ + (−1)·y₂) = T(y₁) + T((−1)·y₂)
>             = T(y₁) + (−1)·T(y₂) = T(y₁) − T(y₂).

## Notes
- Lean target `implicitBias_subtract_y` anchors the subtraction-compatibility
  property of the implicit-bias map.
- Source justification: §12.1.1 closed form X⊤(XX⊤)⁻¹y is linear in y; subtraction
  is linearity with coefficient −1.
- Technique in one line: linearity combined with additive inverse.
- Algebraic dependency: `implicitBias_subtract_y` ↞ `implicitBias_add_y` +
  `implicitBias_smul_y` (with c = −1), or directly from linearity.
- Bach does not state this as a separate lemma — Lean-side decomposition only.
- No ambiguities.

## Prerequisites (Bach's dependency graph)

- [`implicit-bias-full-rank`](./implicit-bias-full-rank.md) — Implicit bias of GD = OLS (full-rank case)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch12_Overparameterized/ImplicitBias.lean`
- **Theorem/def name:** `implicitBias_subtract_y`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

