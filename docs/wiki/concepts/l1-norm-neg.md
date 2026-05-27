# ℓ₁ norm is invariant under negation

**ID:** `l1-norm-neg`  
**Chapter:** Ch08 (Bach §8.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/l1-norm-neg/`](../../../tasks/l1-norm-neg/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — ℓ₁ norm is invariant under negation

**Concept ID:** `l1-norm-neg`
**Chapter:** Ch 8
**Section:** §8.3
**Pages:** 230 (definition page)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach does not state ‖−θ‖₁ = ‖θ‖₁ as a numbered lemma — it is
immediate from the definition ‖θ‖₁ = Σⱼ |θⱼ| and |−θⱼ| = |θⱼ|.

The property is used implicitly throughout §8.3 (e.g., in the
absolute-value/sign manipulations of the optimality conditions on
p. 233).

## Proof (verbatim)

(sketch) — Bach does not give a separate proof. One-liner:
‖−θ‖₁ = Σⱼ |−θⱼ| = Σⱼ |θⱼ| = ‖θ‖₁.

## Notes

- Foundational lemma.
- Lean target `LTFP/Ch08_Sparse/L1.lean#l1Norm_neg`.
- Bach's proof technique: standard (n/a).

## Prerequisites (Bach's dependency graph)

- [`l1-norm`](./l1-norm.md) — ℓ₁ norm: sum of absolute values

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch08_Sparse/L1.lean`
- **Theorem/def name:** `l1Norm_neg`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

