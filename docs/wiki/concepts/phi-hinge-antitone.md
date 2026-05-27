# Hinge surrogate antitone

**ID:** `phi-hinge-antitone`  
**Chapter:** Ch04 (Bach §4.1.1)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/phi-hinge-antitone/`](../../../tasks/phi-hinge-antitone/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Hinge surrogate antitone

**Concept ID:** `phi-hinge-antitone`
**Chapter:** Ch 4
**Section:** 4.1.1
**Pages:** 74
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
The hinge surrogate Φ_hinge(u) = max(1 − u, 0) is non-increasing (antitone) on R:
$$u \le u' \implies \Phi_{\text{hinge}}(u) \ge \Phi_{\text{hinge}}(u').$$

## Proof (verbatim)
Bach observes this implicitly when contrasting hinge with the square loss:
"Note the overpenalization for a large positive value of yg(x) that will not be present
for the other losses discussed next (which are nonincreasing)."

(Trivial.) max is monotonic in each argument; 1 − u is decreasing in u; 0 is constant.
Hence Φ_hinge(u) = max(1 − u, 0) is decreasing in u.

## Notes
- Antitone / monotone-decreasing.
- Hinge, logistic, exponential are all antitone; square is not (it is U-shaped about 1).
- Pedagogical: antitone surrogates reward larger margins monotonically — the "no overpenalty"
  property Bach contrasts with the square loss.

## Prerequisites (Bach's dependency graph)

- [`phi-hinge`](./phi-hinge.md) — Hinge surrogate Φ(u) = max(1-u, 0) — yields SVM

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/Convexification.lean`
- **Theorem/def name:** `phiHinge_antitone`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

