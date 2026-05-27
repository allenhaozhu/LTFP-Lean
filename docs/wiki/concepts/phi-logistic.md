# Logistic surrogate Φ(u) = log(1 + exp(-u))

**ID:** `phi-logistic`  
**Chapter:** Ch04 (Bach §4.1.1, p. 74)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/phi-logistic/`](../../../tasks/phi-logistic/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Logistic surrogate Φ(u) = log(1 + e^{−u})

**Concept ID:** `phi-logistic`
**Chapter:** Ch 4
**Section:** 4.1.1
**Pages:** 74
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
Logistic loss: Φ(u) = log(1 + e^{−u}), leading to
$$\Phi(yg(x)) = \log(1+e^{-yg(x)}) = -\log\Big(\tfrac{1}{1+e^{-yg(x)}}\Big) = -\log\sigma(yg(x)),$$
where σ(v) = 1/(1 + e^{−v}) is the sigmoid function. "Note the link with maximum likelihood
estimation, where we define the model through

P(y = 1|x) = σ(g(x))  and  P(y = −1|x) = σ(−g(x)) = 1 − σ(g(x))."

"The risk is, then, the negative conditional log-likelihood E[−log p(y|x)]. It is also often
called the 'cross-entropy loss.' See more details about probabilistic methods in chapter 14."

## Proof (verbatim)
(Definition — no proof.)

## Notes
- Convex, C^∞, with Φ'(0) = −1/2 < 0 → classification-calibrated.
- Bounded below by 0; Φ(0) = log 2.
- Smooth (Lipschitz gradient) with constant 1/4 (sigmoid bound) — calibrated with H(σ) = √(2σ)
  (4.1.4).
- Probabilistic / maximum-likelihood interpretation: equivalent to logistic regression.

## Prerequisites (Bach's dependency graph)

- [`convex-foundation`](./convex-foundation.md) — Convex analysis foundation: L-smooth alias + Mathlib re-exports

## Dependents (concepts that use this)

- [`phi-logistic-zero`](./phi-logistic-zero.md) — phiLogistic 0 = log 2

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/Convexification.lean`
- **Theorem/def name:** `phiLogistic`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

