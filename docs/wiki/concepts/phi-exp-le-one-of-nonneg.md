# phiExp ≤ 1 for nonneg margin

**ID:** `phi-exp-le-one-of-nonneg`  
**Chapter:** Ch04 (Bach §4.1.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/phi-exp-le-one-of-nonneg/`](../../../tasks/phi-exp-le-one-of-nonneg/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — phiExp ≤ 1 for nonneg margin

**Concept ID:** `phi-exp-le-one-of-nonneg`
**Chapter:** Ch 4
**Section:** 4.1.1
**Pages:** 74
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
For every margin u ≥ 0, the exponential surrogate is bounded above by 1:
$$u \ge 0 \implies \Phi_{\text{exp}}(u) = \exp(-u) \le 1.$$

## Proof (verbatim)
(Trivial.) For u ≥ 0, −u ≤ 0, so exp(−u) ≤ exp(0) = 1.

## Notes
- Trivial corollary of `phi-exp-zero` (= 1) and `phi-exp-antitone`.
- Symmetric counterpart: for u ≤ 0, Φ_exp(u) ≥ 1.
- Used in margin-bound arguments: well-classified examples contribute ≤ 1 to the exp loss.

## Prerequisites (Bach's dependency graph)

- [`phi-exponential`](./phi-exponential.md) — Exponential surrogate Φ(u) = exp(-u) — yields AdaBoost

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/Convexification.lean`
- **Theorem/def name:** `phiExponential_le_one_of_nonneg`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

