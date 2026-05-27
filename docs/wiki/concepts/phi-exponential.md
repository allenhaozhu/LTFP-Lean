# Exponential surrogate Φ(u) = exp(-u) — yields AdaBoost

**ID:** `phi-exponential`  
**Chapter:** Ch04 (Bach §4.1.1, p. 74)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Boosting/Ensemble`

## Statement

_See textbook excerpt below or [`tasks/phi-exponential/`](../../../tasks/phi-exponential/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Exponential surrogate Φ(u) = exp(−u)

**Concept ID:** `phi-exponential`
**Chapter:** Ch 4
**Section:** 4.1.1
**Pages:** 74
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
Exponential loss: Φ(u) = exp(−u). "This loss is often used within the boosting framework
presented in section 10.3, in particular through the Adaboost algorithm (section 10.3.4)."

## Proof (verbatim)
(Definition — no proof.)

## Notes
- Convex, C^∞, decreasing.
- Φ'(0) = −1 < 0 → classification-calibrated by Proposition 4.1.
- Φ(0) = 1; Φ(u) ≤ 1 for u ≥ 0 (well-classified case); Φ(u) → 0 as u → +∞.
- Driver of AdaBoost: the Adaboost weight update arises from the gradient of exp-loss.
- Not Lipschitz (gradient blows up as u → −∞), in contrast to hinge / logistic.

## Prerequisites (Bach's dependency graph)

- [`convex-foundation`](./convex-foundation.md) — Convex analysis foundation: L-smooth alias + Mathlib re-exports

## Dependents (concepts that use this)

- [`boosted-predictor`](./boosted-predictor.md) — Boosted predictor: weighted sum of weak learners
- [`phi-exp-antitone`](./phi-exp-antitone.md) — phiExp is antitone
- [`phi-exp-le-one-of-nonneg`](./phi-exp-le-one-of-nonneg.md) — phiExp ≤ 1 for nonneg margin
- [`phi-exp-zero`](./phi-exp-zero.md) — phiExponential 0 = 1

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/Convexification.lean`
- **Theorem/def name:** `phiExponential`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

