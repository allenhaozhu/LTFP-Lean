# Bagging: average of B sub-predictors

**ID:** `bagging-predictor`  
**Chapter:** Ch10 (Bach §10.1.2)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Boosting/Ensemble`

## Statement

_See textbook excerpt below or [`tasks/bagging-predictor/`](../../../tasks/bagging-predictor/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Bagging: average of B sub-predictors

**Concept ID:** `bagging-predictor`
**Chapter:** Ch 10
**Section:** 10.1.2 "Bagging"
**Pages:** 286-288
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
Bach introduces bagging at the top of §10.1.2 (page 286):

> "We consider datasets `D^(b)`, obtained with random weights `v_i^(b) ∈ ℝ₊`,
> `i = 1, …, n`. For the bootstrap, we consider `n` samples from the original
> `n` data points with replacement, which correspond to integer weights
> `v_i^(b) ∈ ℕ`, `i = 1, …, n`, that sum to `n`. Such sets of weights are
> sampled independently `m` times. We study `m = ∞` for simplicity; that is,
> infinitely many replications (in practice, the infinite `m` behavior can be
> achieved with moderate `m`'s). Infinitely many bootstrap replications lead
> to a form of stabilization, which is important for highly variable
> predictors (which usually imply a large estimation variance)."

The bagged predictor is the average of the `m` sub-predictors obtained on the
resampled datasets:

    f̂(x) = (1/B) Σ_{b=1}^B f̂^(b)(x).

For the 1-nearest-neighbor example developed in §10.1.2 (page 286), Bach
specializes this to

    f̂(x) = Σ_{i=1}^n V_i · y_{(i)}(x),

where `V_i` is the probability that the `i`-th-nearest neighbor of `x` is
the 1-nearest neighbor in a uniform subsample of size `s`.

## Proof (verbatim)
Definitional — `baggingPredictor f x := (1/B) Σ_{b=1}^B f b x`. Bach does
not prove anything about the definition itself; he uses it as the starting
point for the §10.1.2 variance/bias analysis (page 287).

## Notes
- Two equivalent presentations in the textbook: (a) "average of B predictors
  trained on B resampled datasets" (definitional); (b) for the 1-NN case,
  the closed-form `Σ V_i y_{(i)}` on page 286.
- For the Lean foundation only the definitional form is needed; the 1-NN
  specialization is exercise material (page 287, exercise 10.4 on the
  expected fraction of distinct items in bootstrap sampling).
- Technique in one line: average a finite family of predictors with uniform
  weight `1/B`.
- Ambiguity: Bach occasionally treats `B = ∞` for analysis convenience; the
  Lean definition uses finite `B` and downstream theorems instantiate `B = 0`,
  `B = 1`, or constant families.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

- [`bagging-const`](./bagging-const.md) — Bagging a constant predictor yields the same constant
- [`bagging-index-anchor`](./bagging-index-anchor.md) — Bagging index reflexivity anchor
- [`bagging-predictor-zero`](./bagging-predictor-zero.md) — Bagging zero predictors yields zero

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch10_Ensemble/RandomProjections.lean`
- **Theorem/def name:** `baggingPredictor`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

