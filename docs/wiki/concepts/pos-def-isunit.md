# Positive-definite matrix is invertible

**ID:** `pos-def-isunit`  
**Chapter:** Ch01 (Bach §1.1.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** `Matrix/LinAlg`

## Statement

_See textbook excerpt below or [`tasks/pos-def-isunit/`](../../../tasks/pos-def-isunit/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Positive-definite matrix is invertible

**Concept ID:** `pos-def-isunit`
**Chapter:** Ch 1
**Section:** 1.1.1
**Pages:** 3
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach does not isolate this as a numbered proposition; it appears as a parenthetical
remark in the opening sentence of §1.1.1 (page 3):

> Given a positive-definite (and hence invertible) symmetric matrix $A \in \mathbb{R}^{n\times n}$
> and vector $b \in \mathbb{R}^n$, the minimization of quadratic forms with linear terms
> can be done in closed form: ...

The contrapositive is the only place Bach elaborates (page 3, bottom):

> If $A$ were not invertible (simply positive semidefinite) and $b$ were not in the
> column space of $A$, then the infimum would be $-\infty$.

## Proof (verbatim)

Bach gives no proof; he treats this as a standard fact from linear algebra. The
classical proof (which Lean targets) runs:

- A symmetric matrix is positive definite iff $x^\top A x > 0$ for all $x \ne 0$.
- If $A x = 0$ for some $x \ne 0$, then $x^\top A x = 0$, contradicting positive
  definiteness.
- Hence $\ker A = \{0\}$, so $A$ is invertible.

Equivalently (and closer to the Mathlib formulation `Matrix.PosDef.isUnit_det`):
$\det A = \prod \lambda_i > 0$ since every eigenvalue $\lambda_i$ of a positive-definite
matrix is positive; a matrix is invertible iff its determinant is a unit.

## Notes

- Bach defers entirely; the linear-algebra prerequisite is assumed.
- Used immediately as the justification for writing $A^{-1} b$ in the closed-form
  minimizer $x_\star = A^{-1} b$ of $f(x) = \tfrac{1}{2} x^\top A x - b^\top x$.
- Standard Mathlib target: `Matrix.PosDef.isUnit_det` (a `PosDef` matrix has nonzero
  determinant, hence is invertible).
- This is an "F10-style" alias concept — Bach's contribution is using the fact, not
  proving it.

## Prerequisites (Bach's dependency graph)

- [`quadratic-form-min`](./quadratic-form-min.md) — Minimization of a positive-definite quadratic form

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch01_Preliminaries/LinAlg.lean`
- **Theorem/def name:** `posDef_isUnit`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

