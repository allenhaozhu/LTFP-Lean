# Excess risk telescope: a-c = (a-b)+(b-c)

**ID:** `excess-risk-telescope`  
**Chapter:** Ch04 (Bach §4.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/excess-risk-telescope/`](../../../tasks/excess-risk-telescope/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Excess risk telescope: a − c = (a − b) + (b − c)

**Concept ID:** `excess-risk-telescope`
**Chapter:** Ch 4
**Section:** 4.2
**Pages:** 84
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
Telescoping identity for excess risk decomposition:
$$R(\hat f) - R^* = \big(R(\hat f) - \inf_{f \in F} R(f)\big) + \big(\inf_{f \in F} R(f) - R^*\big).$$

More abstractly, for any a, b, c:
$$a - c = (a - b) + (b - c).$$

## Proof (verbatim)
"We can decompose the risk into two terms as follows:
R(f̂) − R^* = { R(f̂) − inf_{f' ∈ F} R(f') } + { inf_{f' ∈ F} R(f') − R^* }
            = estimation error + approximation error."

(Trivial telescoping.)

## Notes
- Pure algebraic identity (sub_add_sub_cancel).
- The cornerstone of the chapter-4 storyline: every excess-risk argument starts by
  inserting an intermediate `inf_{f ∈ F} R(f)` to split into approximation + estimation.
- Lean: `theorem telescope (a b c : ℝ) : a - c = (a - b) + (b - c) := by ring`.

## Prerequisites (Bach's dependency graph)

- [`excess-risk-decomposition`](./excess-risk-decomposition.md) — Excess risk = approximation + estimation

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/RiskDecomposition.lean`
- **Theorem/def name:** `excess_risk_telescope_anchor`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

