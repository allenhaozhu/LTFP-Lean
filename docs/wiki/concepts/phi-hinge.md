# Hinge surrogate Φ(u) = max(1-u, 0) — yields SVM

**ID:** `phi-hinge`  
**Chapter:** Ch04 (Bach §4.1.1, p. 74)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/phi-hinge/`](../../../tasks/phi-hinge/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Hinge surrogate Φ(u) = max(1−u, 0)

**Concept ID:** `phi-hinge`
**Chapter:** Ch 4
**Section:** 4.1.1
**Pages:** 74
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
Hinge loss: Φ(u) = max(1 − u, 0). "With linear predictors, this leads to the support vector
machine (SVM), and yg(x) is often called the 'margin' in this context. This loss has a
geometric interpretation (see section 4.1.2)."

There is also a smooth variant: "Squared hinge loss: Φ(u) = max(1 − u, 0)². This is a smooth
counterpart to the regular hinge loss."

## Proof (verbatim)
(Definition — no proof.) The geometric derivation in 4.1.2 then ties hinge to the maximum-margin
SVM problem (4.2)–(4.3).

## Notes
- Convex but not differentiable at u = 1.
- Non-increasing on R; Φ(u) = 0 for u ≥ 1 (well-classified margin), Φ(u) = 1 − u for u ≤ 1.
- Not classification-calibrated by Bach's calibrate-via-differentiability route at 0 — but
  hinge IS calibrated since Φ is differentiable at 0 with Φ'(0) = −1 < 0 (Proposition 4.1).
- Hinge's calibration function H(σ) = σ is identity (no √-degradation), advantageous for the
  excess-risk → excess-Φ-risk transfer (section 4.1.4).

## Prerequisites (Bach's dependency graph)

- [`convex-foundation`](./convex-foundation.md) — Convex analysis foundation: L-smooth alias + Mathlib re-exports

## Dependents (concepts that use this)

- [`empirical-phi-risk`](./empirical-phi-risk.md) — Empirical Φ-risk R̂_Φ_n(g) = (1/n) ∑ᵢ Φ(yᵢ · g(xᵢ))
- [`phi-hinge-antitone`](./phi-hinge-antitone.md) — Hinge surrogate antitone
- [`phi-hinge-at-zero-anchor`](./phi-hinge-at-zero-anchor.md) — phiHinge 0 = 1 (alias)
- [`phi-hinge-eq-1-sub-of-le-one`](./phi-hinge-eq-1-sub-of-le-one.md) — Hinge equals 1 - u on u ≤ 1
- [`phi-hinge-zero`](./phi-hinge-zero.md) — phiHinge 0 = 1
- [`phi-hinge-zero-of-ge-one`](./phi-hinge-zero-of-ge-one.md) — Hinge surrogate vanishes on margin ≥ 1
- [`phi-zero-one-le-hinge`](./phi-zero-one-le-hinge.md) — Hinge upper-bounds 0-1 surrogate (margin bound)

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/Convexification.lean`
- **Theorem/def name:** `phiHinge`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

