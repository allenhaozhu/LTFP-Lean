# Hinge upper-bounds 0-1 surrogate (margin bound)

**ID:** `phi-zero-one-le-hinge`  
**Chapter:** Ch04 (Bach §4.1.4, p. 76)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/phi-zero-one-le-hinge/`](../../../tasks/phi-zero-one-le-hinge/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Hinge upper-bounds 0-1 surrogate (margin bound)

**Concept ID:** `phi-zero-one-le-hinge`
**Chapter:** Ch 4
**Section:** 4.1.4 (and discussion preceding 4.1.3)
**Pages:** 76, 81-82
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
For all u ∈ R, the margin-based 0-1 surrogate is upper-bounded by the hinge surrogate:
$$\Phi_{0-1}(u) \le \Phi_{\text{hinge}}(u) = \max(1-u, 0).$$

More generally, Bach writes: "All the convex surrogates presented in section 4.1.1 are upper
bounds on the 0–1 loss or can be made so with rescaling. This simple fact allows us to get
a variety of so-called 'margin bounds' where the 0–1 risk is upper-bounded by the Φ-risk."

## Proof (verbatim)
(In-line proof — by case analysis on u.)
- If u < 0: Φ_{0-1}(u) = 1 and max(1 − u, 0) = 1 − u ≥ 1 (since u < 0), so Φ_{0-1}(u) ≤ 1 ≤ 1 − u.
- If u = 0: Φ_{0-1}(u) = 1/2 and max(1 − u, 0) = 1, so 1/2 ≤ 1.
- If 0 < u ≤ 1: Φ_{0-1}(u) = 0 and max(1 − u, 0) = 1 − u ≥ 0.
- If u > 1: Φ_{0-1}(u) = 0 and max(1 − u, 0) = 0; equality.

Bach uses this in (4.7) as Φ_{0-1}((2ξ−1)u) ≤ 1_{(2ξ−1) u ≤ 0}, which is exactly the hinge
dominance bound rescaled.

## Notes
- Hinge is the smallest convex surrogate dominating Φ_{0-1} pointwise.
- Immediate corollary at the population level: R(g) = E[Φ_{0-1}(y g(x))] ≤ R_hinge(g).
- Foundation for the SVM excess-risk → 0-1 excess-risk transfer (calibration function = identity, p. 82).
- Trivial 4-case algebraic proof.

## Prerequisites (Bach's dependency graph)

- [`phi-hinge`](./phi-hinge.md) — Hinge surrogate Φ(u) = max(1-u, 0) — yields SVM
- [`phi-zero-one`](./phi-zero-one.md) — Margin-based 0-1 surrogate Φ_{0-1}(u) = 1[u ≤ 0]

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/Convexification.lean`
- **Theorem/def name:** `phiZeroOne_le_phiHinge`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

