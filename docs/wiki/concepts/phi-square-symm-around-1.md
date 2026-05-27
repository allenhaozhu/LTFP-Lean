# phiSquare symmetric around u = 1

**ID:** `phi-square-symm-around-1`  
**Chapter:** Ch04 (Bach §4.1.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/phi-square-symm-around-1/`](../../../tasks/phi-square-symm-around-1/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — phiSquare symmetric around u = 1

**Concept ID:** `phi-square-symm-around-1`
**Chapter:** Ch 4
**Section:** 4.1.1
**Pages:** 73 (definitional)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
The square surrogate is symmetric around u = 1:
$$\Phi_{\text{square}}(1 + v) = \Phi_{\text{square}}(1 - v) = v^2 \quad \forall v \in \mathbb{R}.$$

## Proof (verbatim)
(Trivial.) Φ_square(1 + v) = ((1 + v) − 1)² = v². Φ_square(1 − v) = ((1 − v) − 1)² = (−v)² = v².
Hence both equal v² and are equal to each other.

## Notes
- Trivial symmetry.
- Reflects the U-shape parabola: the unique minimum at u = 1, with equal cost on either side.
- Used in calibration arguments to identify Φ_square(yg(x)) = (y − g(x))² and exploit
  the symmetric overpenalty property (Bach's remark on p. 73).

## Prerequisites (Bach's dependency graph)

- [`phi-square`](./phi-square.md) — Square surrogate Φ(u) = (u-1)²

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/Convexification.lean`
- **Theorem/def name:** `phiSquare_symm_around_one`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

