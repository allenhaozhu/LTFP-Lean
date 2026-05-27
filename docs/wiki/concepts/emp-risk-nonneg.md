# Empirical risk of nonneg loss is nonneg

**ID:** `emp-risk-nonneg`  
**Chapter:** Ch02 (Bach §2.3.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `ERM`

## Statement

_See textbook excerpt below or [`tasks/emp-risk-nonneg/`](../../../tasks/emp-risk-nonneg/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Empirical risk of nonneg loss is nonneg

**Concept ID:** `emp-risk-nonneg`
**Chapter:** Ch 2
**Section:** 2.2.2 (Risks)
**Pages:** 27
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

From Definition 2.2 (p. 27):

>     R̂(f) = (1/n) Σ_{i=1}^n ℓ(yi, f(xi)).

If `ℓ ≥ 0` pointwise, then every summand `ℓ(yi, f(xi)) ≥ 0`. The sum is
therefore `≥ 0`, and division by the positive scalar `n` preserves
nonnegativity:

>     R̂(f) ≥ 0.

## Proof (verbatim)

Bach does not prove this; implicit in the framing that losses "often" take
values in `R+` (§2.2.1, p. 25), and that averages preserve sign.

In Lean: `Finset.sum_nonneg` of `fun i => ℓ_nonneg ..`, then divide by
`(n : ℝ) ≥ 0`.

## Notes

- Empirical analog of `pop-risk-nonneg`.
- The two together give: under nonneg loss, both `R̂` and `R` are nonneg —
  the proper starting point for two-sided generalization bounds
  `0 ≤ R(f) ≤ R̂(f) + (deviation)`.
- One-line in Lean via `Finset.sum_nonneg` + `div_nonneg`.

## Prerequisites (Bach's dependency graph)

- [`empirical-risk`](./empirical-risk.md) — Empirical risk R̂_n(f)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch02_SupervisedLearning/ERM.lean`
- **Theorem/def name:** `empiricalRisk_nonneg`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

