# localAvg(-Y) = -localAvg(Y)

**ID:** `localavg-neg-y`  
**Chapter:** Ch06 (Bach §6.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/localavg-neg-y/`](../../../tasks/localavg-neg-y/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — localAvg(-Y) = -localAvg(Y)

**Concept ID:** `localavg-neg-y`
**Chapter:** Ch 6
**Section:** 6.2
**Pages:** 157
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
This concept formalizes the **sign-flip** consequence of linearity in `y`. Bach asserts (p. 157):

> For regression: $\mathcal Y = \mathbb R$: $\hat f(x) = \sum_{i=1}^{n} \hat w_i(x)\, y_i$. This is why the terminology "linear estimators" is sometimes used: as a function of the response vector in $\mathbb R^n$, the estimator is linear.

The Lean statement is:
$$\text{localAvg}(-Y,\ w,\ x) \;=\; -\,\text{localAvg}(Y,\ w,\ x).$$

This is the `c = -1` specialization of `localavg-smul-y`, but is kept as a separate lemma because additive groups (and many downstream rewrite goals) prefer to invoke negation directly rather than route through scalar multiplication.

## Proof (verbatim)
Bach does not state this explicitly. The proof is the `c = -1` instance of homogeneity (or equivalently, distributivity of negation over the sum):
$$\sum_{i=1}^n \hat w_i(x)\,(-y_i) \;=\; -\sum_{i=1}^n \hat w_i(x)\,y_i.$$

## Notes
- Lean carrier: `LTFP/Ch06_LocalAveraging/Estimators.lean#localAvg_neg_Y`.
- Proof technique: unfold `localAvg`, use `Pi.neg_apply`, `mul_neg`, `Finset.sum_neg_distrib` — a one-line `simp` chain.
- Together with `localAvg_add_Y` and `localAvg_smul_Y`, this completes the algebraic-linearity suite for `localAvg` in `Y`.
- The asymmetry property Bach asserts on p. 158 ("if $y_i \leqslant y_i'$ for all $i$, then $\hat f(x) \leqslant \hat f'(x)$") is an *order-theoretic* companion that relies on `wᵢ ≥ 0`; the present lemma is purely algebraic and does not need weight nonnegativity.
- No ambiguity.

## Prerequisites (Bach's dependency graph)

- [`local-averaging`](./local-averaging.md) — Local averaging predictors (k-NN, partition, kernel)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch06_LocalAveraging/Estimators.lean`
- **Theorem/def name:** `localAvg_neg_Y`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

