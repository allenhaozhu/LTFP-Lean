# ℓ₁ norm on Fin 1 is |z 0|

**ID:** `l1-norm-fin-one`  
**Chapter:** Ch08 (Bach §8.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/l1-norm-fin-one/`](../../../tasks/l1-norm-fin-one/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — ℓ₁ norm on Fin 1 is |z 0|

**Concept ID:** `l1-norm-fin-one`
**Chapter:** Ch 8
**Section:** §8.3 (used in §8.3.1, "One-dimensional problem", p. 232)
**Pages:** 232
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach does not state this as a numbered lemma. The fact appears
implicitly in §8.3.1 (p. 232) when Bach passes from the multivariate
Lasso to the one-dimensional problem:

>   min F(θ) = ½ (y − θ)² + λ|θ|.
>    θ∈ℝ

Here the multivariate penalty λ‖θ‖₁ reduces to λ|θ| precisely because
‖θ‖₁ on a one-dimensional vector is just the absolute value of its
single coordinate.

## Proof (verbatim)

(sketch) — Bach does not give a separate proof. One-liner:
for z : Fin 1 → ℝ, ‖z‖₁ = Σ_{j : Fin 1} |z_j| = |z 0|, since the sum
over a singleton index set has one term.

## Notes

- Foundational lemma — bridges the multivariate ‖·‖₁ definition with
  the scalar absolute value, which is what the 1-D Lasso analysis uses.
- This is the connection that lets `lasso-kkt` (scalar minimizer) and
  `soft-threshold` (scalar operator) be applied as the 1-D specialization
  of the general Lasso.
- Lean target `LTFP/Ch08_Sparse/L1.lean#l1Norm_fin_one`.
- Bach's proof technique: standard (n/a).

## Prerequisites (Bach's dependency graph)

- [`l1-norm`](./l1-norm.md) — ℓ₁ norm: sum of absolute values

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch08_Sparse/L1.lean`
- **Theorem/def name:** `l1Norm_fin_one`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

