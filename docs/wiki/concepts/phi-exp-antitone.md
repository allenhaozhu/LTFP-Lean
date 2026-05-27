# phiExp is antitone

**ID:** `phi-exp-antitone`  
**Chapter:** Ch04 (Bach §4.1.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/phi-exp-antitone/`](../../../tasks/phi-exp-antitone/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — phiExp is antitone

**Concept ID:** `phi-exp-antitone`
**Chapter:** Ch 4
**Section:** 4.1.1
**Pages:** 74
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
The exponential surrogate Φ_exp(u) = exp(−u) is non-increasing on R:
$$u \le u' \implies \Phi_{\text{exp}}(u) \ge \Phi_{\text{exp}}(u').$$

## Proof (verbatim)
Bach implicitly uses this when classifying the "nonincreasing surrogates": square is not,
hinge / logistic / exponential are.

(Trivial.) exp is monotone increasing on R; u ≤ u' implies −u ≥ −u' implies exp(−u) ≥ exp(−u'). □

## Notes
- Antitone / monotone-decreasing.
- Together with Φ_exp(0) = 1: exp-surrogate ≤ 1 for non-negative margin (`phi-exp-le-one-of-nonneg`).
- Pedagogical: monotone "more correct ⇒ less cost", which is essential to AdaBoost's
  margin-improvement argument.

## Prerequisites (Bach's dependency graph)

- [`phi-exponential`](./phi-exponential.md) — Exponential surrogate Φ(u) = exp(-u) — yields AdaBoost

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/Convexification.lean`
- **Theorem/def name:** `phiExponential_antitone`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

