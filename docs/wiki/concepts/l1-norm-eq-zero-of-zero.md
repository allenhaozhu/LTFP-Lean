# ℓ₁ of zero vector = 0

**ID:** `l1-norm-eq-zero-of-zero`  
**Chapter:** Ch08 (Bach §8.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/l1-norm-eq-zero-of-zero/`](../../../tasks/l1-norm-eq-zero-of-zero/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — ℓ₁ of zero vector = 0

**Concept ID:** `l1-norm-eq-zero-of-zero`
**Chapter:** Ch 8
**Section:** §8.3
**Pages:** 230 (definition page)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach does not state ‖0‖₁ = 0 as a numbered lemma — it is
immediate from the definition ‖θ‖₁ = Σⱼ |θⱼ| evaluated at θ = 0:
each summand is |0| = 0, and the sum is 0.

The property is used implicitly throughout §8.3 (e.g., when Bach
notes the Lasso minimizer is θ = 0 for sufficiently large λ —
Exercise 8.6, p. 234).

## Proof (verbatim)

(sketch) — Bach does not give a separate proof. One-liner:
‖0‖₁ = Σⱼ |0_j| = Σⱼ 0 = 0.

## Notes

- Foundational lemma.
- Lean target `LTFP/Ch08_Sparse/L1.lean#l1Norm_eq_zero_of_zero`.
- Note: this is the "easy direction" of definiteness. The full
  definiteness statement (‖θ‖₁ = 0 ↔ θ = 0) requires also the
  converse, which Bach does not state separately either.
- Bach's proof technique: standard (n/a).

## Prerequisites (Bach's dependency graph)

- [`l1-norm`](./l1-norm.md) — ℓ₁ norm: sum of absolute values

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch08_Sparse/L1.lean`
- **Theorem/def name:** `l1Norm_eq_zero_of_zero`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

