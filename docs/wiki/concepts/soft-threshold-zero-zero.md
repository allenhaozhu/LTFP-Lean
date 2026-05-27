# Soft threshold of 0 at level 0 = 0

**ID:** `soft-threshold-zero-zero`  
**Chapter:** Ch08 (Bach §8.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Lasso/Sparse`

## Statement

_See textbook excerpt below or [`tasks/soft-threshold-zero-zero/`](../../../tasks/soft-threshold-zero-zero/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Soft threshold of 0 at level 0 = 0

**Concept ID:** `soft-threshold-zero-zero`
**Chapter:** Ch 8
**Section:** §8.3.1 (One-dimensional problem)
**Pages:** 232
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach does not state S_0(0) = 0 as a numbered lemma — it is immediate
from the closed-form definition S_λ(y) = max(|y| − λ, 0) · sign(y)
(p. 232).

At y = 0, λ = 0:

>   S_0(0) = max(|0| − 0, 0) · sign(0) = 0 · sign(0) = 0.

This is also consistent with Bach's stated boundary behavior on
p. 232: "For λ = 0 (no regularization), we have θ\*_0(y) = y", which
at y = 0 gives θ\*_0(0) = 0.

## Proof (verbatim)

(sketch) — Bach does not give a separate proof. Direct computation:
S_0(0) = max(0 − 0, 0) · sign(0) = 0 · 0 = 0.

## Notes

- Trivial boundary case of the soft-threshold operator.
- Used as a sanity check / boundary lemma for the soft-threshold
  closed form.
- Lean target `LTFP/Ch08_Sparse/L1.lean#softThreshold_zero_zero`.
- Bach's proof technique: standard (n/a).
- Note: well-defined regardless of the sign(0) convention, since
  the max factor is 0.

## Prerequisites (Bach's dependency graph)

- [`soft-threshold`](./soft-threshold.md) — Soft-thresholding operator (closed form for 1-D Lasso)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch08_Sparse/L1.lean`
- **Theorem/def name:** `softThreshold_zero_zero`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

