# Boosted predictor: weighted sum of weak learners

**ID:** `boosted-predictor`  
**Chapter:** Ch10 (Bach §10.3, p. 298)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Boosting/Ensemble`

## Statement

_See textbook excerpt below or [`tasks/boosted-predictor/`](../../../tasks/boosted-predictor/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Boosted predictor: weighted sum of weak learners

**Concept ID:** `boosted-predictor`
**Chapter:** Ch 10
**Section:** 10.3 "Boosting"
**Pages:** 298-302
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
Section 10.3 (pages 298-300) sets up the boosting problem. Given an input
space `X`, observations `(x_i, y_i) ∈ X × ℝ`, and a parametric family of
weak learners `φ(·, w): X → ℝ` for `w ∈ W` (a compact subset of a
finite-dimensional vector space), boosting produces a predictor that is a
weighted sum of `t` weak learners obtained by sequential calls to the weak
learner oracle.

From page 299:

> "Boosting procedures will make sequential calls to the weak learner oracle
> that outputs `w_1, …, w_t ∈ W` with `t` the number of iterations, and
> linearly combine the function `φ(·, w_1), …, φ(·, w_t)`. Therefore, the set
> of predictors that are explored are not only the functions `φ(·, w)`, but
> all linear combinations; that is, functions of the form
>
>     f(x) = ∫_W φ(x, w) dν(w),                                       (10.8)
>
> for `ν` a signed measure on `W`, which we assume to have finite mass."

For a finite measure `ν = Σ_{i=1}^t b_i δ_{w_i}` (page 299) the predictor
specializes to

    f(x) = Σ_{i=1}^t b_i · φ(x, w_i).

This is the "boosted predictor": a weighted finite sum of weak-learner
evaluations. In the Lean formalization the coefficients are denoted `α t`
and the weak learners `h t`:

    boostedPredictor α h T x = Σ_{t=0}^{T-1} α t · h t x.

## Proof (verbatim)
Definitional. The "proof" is the statement of equation (10.8) on page 299
specialized to a discrete signed measure (page 299, paragraph below
equation 10.8).

## Notes
- Bach distinguishes between the integral form `∫_W φ(x, w) dν(w)` (continuous
  `W`) and the discrete sum `Σ b_i φ(·, w_i)` (finite measure). The Lean
  formalization uses the discrete form throughout.
- The page-299 setup also fixes the normalization `|φ(x, w)| ≤ R` for all
  `w ∈ W, x ∈ X`, and central symmetry of `{φ(·, w) : w ∈ W}` — these are
  later hypotheses, not part of the definition itself.
- Technique in one line: take a finite weighted sum of weak-learner outputs.
- Ambiguity: Bach uses `b_i` for coefficients in §10.3.1 (page 299), `α_j`
  for the `Adaboost` re-parameterization (§10.3.4, page 303), and `α_t` for
  the gradient-boosting analysis (§10.3.5+). The Lean formalization fixes
  `α t` for consistency.

## Prerequisites (Bach's dependency graph)

- [`phi-exponential`](./phi-exponential.md) — Exponential surrogate Φ(u) = exp(-u) — yields AdaBoost

## Dependents (concepts that use this)

- [`boost-eq`](./boost-eq.md) — Boosted predictor = sum α t · h t x (definitional)
- [`boost-one-step`](./boost-one-step.md) — Boosting with single weak learner
- [`boost-zero-coeffs`](./boost-zero-coeffs.md) — Boosting with zero coefficients gives zero predictions
- [`boost-zero-h`](./boost-zero-h.md) — Boosting with zero weak learners gives zero
- [`boosted-add-coeff`](./boosted-add-coeff.md) — Boosted predictor linear in coefficients α

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch10_Ensemble/Boosting.lean`
- **Theorem/def name:** `boostedPredictor`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

