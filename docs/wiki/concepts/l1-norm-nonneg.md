# ℓ₁ norm is nonnegative

**ID:** `l1-norm-nonneg`  
**Chapter:** Ch08 (Bach §8.3, p. 231)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/l1-norm-nonneg/`](../../../tasks/l1-norm-nonneg/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — ℓ₁ norm is nonnegative

**Concept ID:** `l1-norm-nonneg`
**Chapter:** Ch 8
**Section:** §8.3
**Pages:** 230 (definition page)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Implicit in Bach's use of ‖·‖₁ as a norm throughout §8.3 (pp. 230 ff.).
Bach does not state nonnegativity as a numbered lemma — it is immediate
from the definition ‖θ‖₁ = Σⱼ |θⱼ|, since each |θⱼ| ≥ 0 and a sum of
nonnegatives is nonnegative.

## Proof (verbatim)

(sketch) — Bach does not give a separate proof. Standard one-liner:
each absolute value is nonnegative; finite sum of nonnegatives is
nonnegative; hence ‖θ‖₁ = Σⱼ |θⱼ| ≥ 0.

## Notes

- Bach uses ‖·‖₁ as a norm without proving the norm axioms; the
  axioms (nonnegativity, definiteness, homogeneity, triangle
  inequality) are standard background.
- Foundational lemma, used silently throughout §8.3 in inequalities
  involving ‖θ\*‖₁, ‖θ̂‖₁, ‖∆‖₁.
- Lean target `LTFP/Ch08_Sparse/L1.lean#l1Norm_nonneg`.
- **Flagged ambiguity:** none — entirely standard.

## Prerequisites (Bach's dependency graph)

- [`l1-norm`](./l1-norm.md) — ℓ₁ norm: sum of absolute values

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch08_Sparse/L1.lean`
- **Theorem/def name:** `l1Norm_nonneg`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

