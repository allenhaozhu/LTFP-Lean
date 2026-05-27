# Soft threshold at level lam = 0 at z = lam

**ID:** `soft-threshold-at-lam`  
**Chapter:** Ch08 (Bach §8.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Lasso/Sparse`

## Statement

_See textbook excerpt below or [`tasks/soft-threshold-at-lam/`](../../../tasks/soft-threshold-at-lam/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Soft threshold at level lam = 0 at z = lam

**Concept ID:** `soft-threshold-at-lam`
**Chapter:** Ch 8
**Section:** §8.3.1 (One-dimensional problem)
**Pages:** 232
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach does not state S_λ(λ) = 0 as a numbered lemma, but it follows
directly from the piecewise definition on p. 232:

>   θ*_λ(y) = 0       if |y| ≤ λ,
>   θ*_λ(y) = y − λ   for y > λ,
>   θ*_λ(y) = y + λ   for y < −λ.

The boundary case y = λ falls in the first branch (|y| ≤ λ), giving
S_λ(λ) = 0. Equivalently, by the closed form:

>   S_λ(λ) = max(|λ| − λ, 0) · sign(λ) = max(0, 0) · sign(λ) = 0.

(Assuming λ ≥ 0, the standard convention for the regularization
parameter throughout §8.3.)

## Proof (verbatim)

(sketch) — Bach does not give a separate proof. Direct computation:
|λ| − λ = 0 ⇒ max(0, 0) = 0 ⇒ S_λ(λ) = 0 · sign(λ) = 0.

## Notes

- Boundary lemma at the threshold y = λ.
- Confirms that the soft-threshold operator is continuous: it
  evaluates to 0 both just-inside (|y| ≤ λ branch) and just-at the
  boundary (y = λ).
- Lean target `LTFP/Ch08_Sparse/L1.lean#softThreshold_at_lam`.
- Bach's proof technique: standard (n/a).
- **Flagged ambiguity:** the boundary point y = λ is shared between
  the |y| ≤ λ branch (gives 0) and the y > λ branch (would give
  y − λ = 0 at the limit y → λ⁺). Both branches agree at the
  boundary; the closed form max(|y| − λ, 0) · sign(y) is the
  canonical resolution.

## Prerequisites (Bach's dependency graph)

- [`soft-threshold`](./soft-threshold.md) — Soft-thresholding operator (closed form for 1-D Lasso)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch08_Sparse/L1.lean`
- **Theorem/def name:** `softThreshold_at_lam`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

