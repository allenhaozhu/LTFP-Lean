# Partition-based weights (histogram estimator)

**ID:** `partition-weights`  
**Chapter:** Ch06 (Bach §6.2.2, p. 158)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Local-averaging`

## Statement

_See textbook excerpt below or [`tasks/partition-weights/`](../../../tasks/partition-weights/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Partition-based weights (histogram estimator)

**Concept ID:** `partition-weights`
**Chapter:** Ch 6
**Section:** 6.2.2
**Pages:** 158-159
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
From §6.2.2 "Partition Estimators" (p. 158):

> If $\mathcal X = \bigcup_{j \in J} A_j$ is a partition (such that for all distinct $j, j' \in J$, $A_j \cap A_{j'} = \emptyset$) of $\mathcal X$ with a countable index set $J$ (which we will assume to be finite for simplicity, equal to $\{1, \ldots, |J|\}$), then we can consider for any $x \in \mathcal X$ the corresponding element $A(x)$ of the partition (i.e., $A(x)$ is the unique $A_j$, $j \in J$, such that $x \in A_j$), and define
> $$\hat w_i(x) \;=\; \frac{\mathbf 1_{x_i \in A(x)}}{\sum_{i'=1}^{n} \mathbf 1_{x_{i'} \in A(x)}}, \quad (6.2)$$
> with the convention that if no training data point lies in $A(x)$, then $\hat w_i(x)$ is equal to $1/n$ for each $i \in \{1, \ldots, n\}$. This implies that each $\hat w_i$ is piecewise constant with respect to the partition; that is, for any nonempty cell $A_j$ (i.e., such that at least one observation falls in $A_j$), for any $x \in A_j$, the vectors $(\hat w_i(x))_{i \in \{1, \ldots, n\}}$ has weights equal to $1/n_{A_j}$ for $i \in A_j$, where $n_{A_j}$ is the number of training points in set $A_j$, and 0 otherwise.

## Proof (verbatim)
N/A — this is a definition. The equivalence with least-squares regression is sketched on p. 159:

> When applied to regression where the estimator is $\hat f(x) = \sum_{i=1}^{n} \hat w_i(x)\, y_i$, using a partition estimator can be seen as a least-squares estimator with feature vector $\varphi(x) = \bigl(\mathbf 1_{x \in A_j}\bigr)_{j \in J}$ […]. It turns out that matrix $\hat\Sigma = \frac{1}{n}\sum_{i=1}^{n}\varphi(x_i)\varphi(x_i)^\top$ is diagonal where for each $j \in J$, $n\hat\Sigma_{jj}$ is equal to the number $n_{A_j}$ of data points lying in cell $A_j$.

## Notes
- Lean carrier: `LTFP/Ch06_LocalAveraging/Estimators.lean#partitionWeights`. The Lean version is parametrized by a partition-index function `P : 𝒳 → ℕ` and the training points `xs : Fin n → 𝒳`; weight `wᵢ(x)` is `1 / #{i' : P (xs i') = P x}` if `i` lies in the cell, else `0`.
- Two predictor names Bach uses: **regressogram** (fixed bin partition of `[0,1]^d`) and **decision trees** (data-adaptive partition).
- Conventions for empty cells matter: Bach's choice `1/n` (i.e., predict the global mean) is one of several "other conventions exist (such as all zero weights when no data point lies in $A(x)$)" (p. 159). Lean uses 0 for the empty-cell fallback (companion theorems handle it separately), since the partition-only definition cannot see `n` directly without the convention being baked in.
- Bach later (p. 165, Proposition 6.1) uses this scheme to derive the canonical $O(n^{-2/(d+2)})$ rate.
- No proof technique needed — pure definition.

## Prerequisites (Bach's dependency graph)

- [`local-averaging`](./local-averaging.md) — Local averaging predictors (k-NN, partition, kernel)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch06_LocalAveraging/Estimators.lean`
- **Theorem/def name:** `partitionWeights`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

