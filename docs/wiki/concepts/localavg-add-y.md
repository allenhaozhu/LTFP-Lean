# localAvg is linear in labels Y

**ID:** `localavg-add-y`  
**Chapter:** Ch06 (Bach §6.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/localavg-add-y/`](../../../tasks/localavg-add-y/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — localAvg is linear in labels Y

**Concept ID:** `localavg-add-y`
**Chapter:** Ch 6
**Section:** 6.2
**Pages:** 157-158
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
This concept formalizes the **additivity in `Y`** half of Bach's observation on p. 157 that the local-averaging estimator is **linear** as a function of the response vector. Bach writes (p. 157):

> For regression: $\mathcal Y = \mathbb R$: $\hat f(x) = \sum_{i=1}^{n} \hat w_i(x)\, y_i$. This is why the terminology "linear estimators" is sometimes used: as a function of the response vector in $\mathbb R^n$, the estimator is linear (note that this is also the case for kernel ridge regression in chapter 7; see section 7.6.1). If we only consider predictions $\hat f(x_i)$ at the observed inputs, the vector $\hat y \in \mathbb R^n$ of predictions $\hat y_i = \hat f(x_i)$, for $i \in \{1, \ldots, n\}$ is of the form $\hat y = Hy$, where the matrix $H \in \mathbb R^{n \times n}$, often called the "smoothing matrix" or the "hat matrix," is such that $H_{ij} = \hat w_j(x_i)$.

Bach also notes (p. 158, second `△!` block):

> if the same constant is added to all outputs, the exact same constant is added to the prediction function; moreover, given two vectors of outputs $y$ and $y' \in \mathbb R^n$ with two prediction functions $\hat f$ and $\hat f'$, if $y_i \leqslant y_i'$ for all $i \in \{1, \ldots, n\}$, then $\hat f(x) \leqslant \hat f'(x)$ for all $x \in \mathcal X$.

Both properties are immediate consequences of linearity in `y`.

The Lean statement specializes to additivity:
$$\text{localAvg}(Y_1 + Y_2,\ w,\ x) \;=\; \text{localAvg}(Y_1,\ w,\ x) \;+\; \text{localAvg}(Y_2,\ w,\ x).$$

## Proof (verbatim)
Bach does not state this as a numbered theorem. The proof is immediate from the linearity of the defining sum `∑ wᵢ(x) · yᵢ` in `y`:
$$\sum_{i=1}^n \hat w_i(x)\,(y_i + y'_i) = \sum_{i=1}^n \hat w_i(x)\,y_i + \sum_{i=1}^n \hat w_i(x)\,y'_i.$$

## Notes
- Lean carrier: `LTFP/Ch06_LocalAveraging/Estimators.lean#localAvg_add_Y`.
- Proof technique: `Pi.add_apply`, `mul_add`, `Finset.sum_add_distrib` — a one-line `simp` chain.
- This is part of an algebraic-properties suite (`localAvg_add_Y`, `localAvg_smul_Y`, `localAvg_neg_Y`) packaging the linearity Bach asserts on p. 157.
- The "smoothing matrix" framing (`ŷ = Hy`) is the matrix-level encoding of linearity; the per-`x` algebraic identities are the pointwise version Bach implicitly uses.
- No ambiguity — the property is mechanical.

## Prerequisites (Bach's dependency graph)

- [`local-averaging`](./local-averaging.md) — Local averaging predictors (k-NN, partition, kernel)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch06_LocalAveraging/Estimators.lean`
- **Theorem/def name:** `localAvg_add_Y`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

