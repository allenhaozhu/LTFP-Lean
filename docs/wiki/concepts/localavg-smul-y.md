# localAvg is homogeneous in labels

**ID:** `localavg-smul-y`  
**Chapter:** Ch06 (Bach §6.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/localavg-smul-y/`](../../../tasks/localavg-smul-y/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — localAvg is homogeneous in labels

**Concept ID:** `localavg-smul-y`
**Chapter:** Ch 6
**Section:** 6.2
**Pages:** 157
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
This concept formalizes the **scalar-homogeneity** half of Bach's "linear in `y`" claim (p. 157):

> For regression: $\mathcal Y = \mathbb R$: $\hat f(x) = \sum_{i=1}^{n} \hat w_i(x)\, y_i$. This is why the terminology "linear estimators" is sometimes used: as a function of the response vector in $\mathbb R^n$, the estimator is linear.

The Lean statement is:
$$\text{localAvg}(c \cdot Y,\ w,\ x) \;=\; c \,\cdot\, \text{localAvg}(Y,\ w,\ x).$$

Together with `localavg-add-y`, this completes the verification that the map `y ↦ ŷ` is an `ℝ`-linear map on `ℝⁿ`, justifying the "linear estimator" / "hat matrix `H`" terminology Bach uses immediately afterwards (p. 157):

> the vector $\hat y \in \mathbb R^n$ of predictions $\hat y_i = \hat f(x_i)$, for $i \in \{1, \ldots, n\}$ is of the form $\hat y = Hy$ […].

## Proof (verbatim)
Bach does not state this as a numbered theorem. The proof is immediate from scalar-out-of-sum:
$$\sum_{i=1}^n \hat w_i(x)\,(c \cdot y_i) \;=\; c \cdot \sum_{i=1}^n \hat w_i(x)\,y_i.$$

## Notes
- Lean carrier: `LTFP/Ch06_LocalAveraging/Estimators.lean#localAvg_smul_Y`.
- Proof technique: unfold `localAvg`, use `Pi.smul_apply` / `mul_assoc` / `Finset.mul_sum` — a few-line `simp` / `rw` chain.
- Companion to `localAvg_add_Y` and `localAvg_neg_Y`; together they witness `ℝ`-linearity in `Y`.
- No ambiguity — the property is mechanical and not given a Bach proposition number; it's a direct consequence of the displayed regression formula on p. 157.

## Prerequisites (Bach's dependency graph)

- [`local-averaging`](./local-averaging.md) — Local averaging predictors (k-NN, partition, kernel)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch06_LocalAveraging/Estimators.lean`
- **Theorem/def name:** `localAvg_smul_Y`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

