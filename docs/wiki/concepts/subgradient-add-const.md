# Subgradient is invariant under additive constants

**ID:** `subgradient-add-const`  
**Chapter:** Ch05 (Bach §5.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Sub-Gaussian`

## Statement

_See textbook excerpt below or [`tasks/subgradient-add-const/`](../../../tasks/subgradient-add-const/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Subgradient invariant under additive constants

**Concept ID:** `subgradient-add-const`
**Chapter:** Ch 5
**Section:** 5.3 (immediate from Definition of subdifferential)
**Pages:** 130-131 (book), PDF pp. 146-147
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

If $z \in \partial F(\theta)$ and $c \in \mathbb{R}$, then $z \in \partial(F + c)(\theta)$.
Equivalently: $\partial(F + c) = \partial F$ pointwise.

Bach does not state this as a numbered proposition — it is an immediate
algebraic consequence of the defining inequality
$F(\eta) \ge F(\theta) + z^\top(\eta - \theta)$, which is preserved when both
sides shift by the same constant.

## Proof (verbatim)

Direct algebraic verification: for any $\eta$,
$(F + c)(\eta) = F(\eta) + c \ge F(\theta) + z^\top(\eta - \theta) + c = (F+c)(\theta) + z^\top(\eta - \theta).$

## Notes

- A basic sanity-check lemma; used implicitly whenever Bach normalizes
  $F$ so that $F(\eta_*) = 0$ in convergence proofs.
- Lean form: `IsSubgradient F θ z → IsSubgradient (fun x => F x + c) θ z`.
- Dual property: scaling $F$ by a positive constant scales the subgradient by
  the same constant (not required by this concept).

## Prerequisites (Bach's dependency graph)

- [`subgradient`](./subgradient.md) — Subgradient predicate IsSubgradient

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch05_Optimization/Subgradient.lean`
- **Theorem/def name:** `IsSubgradient.add_const`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

