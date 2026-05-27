# Bagging a constant predictor yields the same constant

**ID:** `bagging-const`  
**Chapter:** Ch10 (Bach §10.1.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Boosting/Ensemble`

## Statement

_See textbook excerpt below or [`tasks/bagging-const/`](../../../tasks/bagging-const/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Bagging a constant predictor yields the same constant

**Concept ID:** `bagging-const`
**Chapter:** Ch 10
**Section:** 10.1.2 "Bagging" (algebraic sanity)
**Pages:** 286-288
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
Algebraic sanity lemma for the bagged predictor of §10.1.2: averaging the
same predictor `f` over `B` resamples returns `f`:

    baggingPredictor (fun _ x => f x) x = f x.

Bach does not state this as a separate proposition. It is the obvious
consistency check that bagging does not perturb a predictor that is
identical on every bootstrap replication — used implicitly in the page-287
discussion: "as will be shown for 1-nearest-neighbor, bagging will reduce
variance while increasing the bias, thus leading to trade-offs that are
common in regularizing methods." The variance-reduction-without-bias-
shift baseline requires that the constant-predictor case reduce to
identity.

## Proof (verbatim)
Definitional. `(1/B) Σ_{b=1}^B f x = (1/B) · B · f x = f x` when `B > 0`.

## Notes
- Sanity check used to validate that the `baggingPredictor` definition does
  not impose spurious scaling.
- Technique in one line: unfold the average; the inner sum is `B · f x`.
- Ambiguity: `B = 0` requires care — the Lean statement may handle it via
  a convention (`Finset.sum_const` returns `0`, so the lemma reads
  `0 = f x` only when `f x = 0`). Downstream theorems use `B ≥ 1`.

## Prerequisites (Bach's dependency graph)

- [`bagging-predictor`](./bagging-predictor.md) — Bagging: average of B sub-predictors

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch10_Ensemble/RandomProjections.lean`
- **Theorem/def name:** `baggingPredictor_const`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

