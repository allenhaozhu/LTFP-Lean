# Nearest-neighbour indicator weights (1-NN)

**ID:** `nn-weights`  
**Chapter:** Ch06 (Bach §6.2.3, p. 160)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/nn-weights/`](../../../tasks/nn-weights/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Nearest-neighbour indicator weights (1-NN)

**Concept ID:** `nn-weights`
**Chapter:** Ch 6
**Section:** 6.2.3
**Pages:** 160-161
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
From §6.2.3 "Nearest-Neighbors" (pp. 160-161):

> Given an integer $k \geqslant 1$, and a distance $\Delta$ on $\mathcal X$, for any $x \in \mathcal X$, we can order the $n$ observations so that
> $$\Delta(x_{i_1(x)}, x) \leqslant \Delta(x_{i_2(x)}, x) \leqslant \cdots \leqslant \Delta(x_{i_n(x)}, x),$$
> where $\{i_1(x), \ldots, i_n(x)\} = \{1, \ldots, n\}$ and ties are broken randomly (i.e., for all $x \in \mathcal X$, the indices that come first are sampled randomly).
>
> We then define
> $$\hat w_i(x) \;=\; 1/k\ \text{if}\ i \in \{i_1(x), \ldots, i_k(x)\},\ \text{and}\ 0\ \text{otherwise.}$$
>
> Given a new input $x \in \mathbb R^d$, the nearest neighbor predictor looks at the $k$ nearest points $x_i$ in the dataset $\{(x_1, y_1), \ldots, (x_n, y_n)\}$ and predicts a majority vote among them (for classification) or simply the averaged response (for regression). The number of nearest-neighbors is the hyperparameter, which needs to be estimated (typically by cross-validation); see section 6.3.2 for an analysis.

For the **1-NN** specialization (`k = 1`) (p. 161):

> For $k = 1$, the prediction function is piecewise constant, with each constant piece corresponding to a region where a given observation is the nearest-neighbor, leading, in two dimensions, to the Voronoi diagram, with all regions displayed.

## Proof (verbatim)
N/A — this is a definition.

## Notes
- Lean carrier: `LTFP/Ch06_LocalAveraging/Estimators.lean#nnWeights`. The Lean signature `nnWeights (witness : 𝒳 → Fin n) : LocalWeights 𝒳 n` abstracts the nearest-neighbour search via a witness function, returning `1` at the witness index and `0` elsewhere — i.e., the `k=1` specialization with the tie-breaking encapsulated in `witness`.
- The general `k`-NN scheme requires the `1/k` normalization and an ordering of indices; the Lean library currently formalizes only the 1-NN case (as recorded in `nnWeights_localAvg`: see the next concept).
- Bach defers the consistency analysis (and the lemmas 6.1 / 6.2 bounding the expected distance to the kth-NN) to §6.3.2 (pp. 168-169).
- Tie-breaking: Bach uses random ties, but notes the footnote "Other conventions share the weights among all ties" (p. 160). Lean's `witness` function side-steps the issue.
- No proof technique needed — pure definition.

## Prerequisites (Bach's dependency graph)

- [`local-averaging`](./local-averaging.md) — Local averaging predictors (k-NN, partition, kernel)

## Dependents (concepts that use this)

- [`nn-weights-localavg`](./nn-weights-localavg.md) — 1-NN local average evaluates to label at witness index

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch06_LocalAveraging/Estimators.lean`
- **Theorem/def name:** `nnWeights`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

