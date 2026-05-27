# Tail bound on uniform deviation, separable hypothesis class

**ID:** `rademacher-tail-bound-separable`  
**Chapter:** Ch04 (Bach §4.5)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** in_lean_rademacher  
**Topic tags:** `Rademacher`

## Statement

_See textbook excerpt below or [`tasks/rademacher-tail-bound-separable/`](../../../tasks/rademacher-tail-bound-separable/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Tail bound on uniform deviation, separable hypothesis class

**Concept ID:** `rademacher-tail-bound-separable`
**Chapter:** Ch 4
**Section:** 4.5 (separability/measurability remark)
**Pages:** 91-94
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
For a separable hypothesis class F (so that the suprema sup_{f ∈ F} (R(f) − R̂(f)) and
sup_{h ∈ H} (1/n) Σ ε_i h(z_i) are measurable and equal almost surely to suprema over a
countable dense subset), the same tail bound holds:

with probability ≥ 1 − δ,
$$\sup_{f\in F}\big(R(f)-\hat R(f)\big)\le 2 R_n(H)+\tfrac{\ell_\infty}{\sqrt{2n}}\sqrt{\log(1/\delta)}.$$

## Proof (verbatim)
Bach treats the separable case as the same statement, since on a separable hypothesis class
the supremum equals the supremum over a countable dense subset and all the integrals /
expectations involved are measurable. The proof is therefore literally that of the countable
case (Proposition 4.2 + bounded differences + McDiarmid). Bach does not single out a separate
proof in section 4.5.1; he relies on measurability conventions throughout chapter 4.

## Notes
- Standard measurability remark: separability of (F, d_∞) suffices to make sup_{f∈F} ξ(f)
  measurable for ξ continuous in f.
- For our Lean formalization, the separable case is the operative one: it reduces to the
  countable-dense-subset tail bound by pointwise approximation.
- Same constants as the countable case.

## Prerequisites (Bach's dependency graph)

- [`rademacher-tail-bound-countable`](./rademacher-tail-bound-countable.md) — Tail bound on uniform deviation, countable hypothesis class

## Dependents (concepts that use this)

- [`linear-predictor-l1-bound`](./linear-predictor-l1-bound.md) — Generalization bound for L¹-regularized linear predictors (Lasso)
- [`linear-predictor-l2-bound`](./linear-predictor-l2-bound.md) — Generalization bound for L²-regularized linear predictors (ridge)

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = in_lean_rademacher`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/Main.lean`
- **Theorem/def name:** `uniform_deviation_tail_bound_separable`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

