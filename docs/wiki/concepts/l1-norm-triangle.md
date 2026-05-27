# ℓ₁ norm triangle inequality (alias)

**ID:** `l1-norm-triangle`  
**Chapter:** Ch08 (Bach §8.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/l1-norm-triangle/`](../../../tasks/l1-norm-triangle/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — ℓ₁ norm triangle inequality (alias)

**Concept ID:** `l1-norm-triangle`
**Chapter:** Ch 8
**Section:** §8.3
**Pages:** 230 (definition page); used in lemma 8.4 proof p. 236
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Alias for the triangle inequality for ‖·‖₁ — see `l1-triangle`. Bach
invokes "the triangle inequality" by name in the proof of Lemma 8.4
(p. 236, see `l1-triangle` excerpt for the verbatim quote).

The statement is the standard norm-axiom inequality:

>   ‖θ + φ‖₁ ≤ ‖θ‖₁ + ‖φ‖₁  for all θ, φ ∈ ℝᵈ.

## Proof (verbatim)

(sketch) — coordinate-wise from |a + b| ≤ |a| + |b|, then sum:
‖θ + φ‖₁ = Σⱼ |θⱼ + φⱼ| ≤ Σⱼ (|θⱼ| + |φⱼ|) = ‖θ‖₁ + ‖φ‖₁.

## Notes

- This is an alias for `l1-triangle`; both expose the same Lean
  statement.
- Lean target `LTFP/Ch08_Sparse/L1.lean#l1Norm_triangle`.
- Bach's proof technique: standard (n/a).
- **Flagged ambiguity:** the registry distinguishes `l1-triangle`
  (primary) from `l1-norm-triangle` (alias). The Lean library may
  expose both names for ergonomic reference.

## Prerequisites (Bach's dependency graph)

- [`l1-norm`](./l1-norm.md) — ℓ₁ norm: sum of absolute values

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch08_Sparse/L1.lean`
- **Theorem/def name:** `l1Norm_triangle`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

