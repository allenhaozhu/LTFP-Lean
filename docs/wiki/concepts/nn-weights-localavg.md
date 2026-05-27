# 1-NN local average evaluates to label at witness index

**ID:** `nn-weights-localavg`  
**Chapter:** Ch06 (Bach §6.2.3, p. 160)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Neural-network`

## Statement

_See textbook excerpt below or [`tasks/nn-weights-localavg/`](../../../tasks/nn-weights-localavg/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — 1-NN local average evaluates to label at witness index

**Concept ID:** `nn-weights-localavg`
**Chapter:** Ch 6
**Section:** 6.2.3
**Pages:** 160-161
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
This concept formalizes Bach's informal observation (p. 161) that the 1-NN regression predictor at a test point `x` simply returns the label `y_{i_1(x)}` of the nearest training observation:

> For $k = 1$, the prediction function is piecewise constant, with each constant piece corresponding to a region where a given observation is the nearest-neighbor, leading, in two dimensions, to the Voronoi diagram.

Equivalently, from §6.2.3, when the weights `wᵢ(x) = 1/k` for `i ∈ {i₁(x), …, iₖ(x)}` and `0` otherwise, specializing to `k = 1` yields `w_{i₁(x)}(x) = 1` and all others `0`. The local-average estimator (p. 157, "For regression: $\hat f(x) = \sum_{i=1}^n \hat w_i(x)\, y_i$") then collapses to
$$\hat f(x) \;=\; y_{i_1(x)}.$$

## Proof (verbatim)
Bach does not give an explicit proof — the statement is immediate from the definitions. The chain:

1. (p. 161 definition) `wᵢ(x) = 1/k` if `i ∈ {i₁(x), …, iₖ(x)}`, `0` otherwise.
2. (p. 157, plug-in / linear estimator) `f̂(x) = ∑ᵢ wᵢ(x) · yᵢ`.
3. For `k = 1`, only `i = i₁(x)` contributes, with weight `1/1 = 1`. Hence `f̂(x) = y_{i₁(x)}`.

(sketch — single substitution; no Bach text beyond the displayed equations on pp. 157, 161.)

## Notes
- Lean carrier: `LTFP/Ch06_LocalAveraging/Estimators.lean#nnWeights_localAvg`. Statement:
  `localAvg Y (nnWeights witness) x = Y (witness x)`.
- The Lean proof is a one-step `simp`/`unfold` over `localAvg` and `nnWeights`: the sum collapses by `Finset.sum_ite_eq'` or equivalent because exactly one index hits.
- Proof technique: trivial substitution. No external lemma needed.
- This theorem is **not stated as a numbered proposition in Bach** — it's a one-line consequence of the definition that Bach takes for granted when describing the Voronoi-cell behaviour. Promoting it to a named Lean theorem makes the consistency results downstream (which depend on `f̂(x) − f*(x) = y_{witness} − f*(x)`) easier to discharge.
- Ambiguity flag: Bach's 1-NN uses a randomized tie-break; the Lean version pushes randomization into the `witness` function, so the theorem is deterministic given a witness.

## Prerequisites (Bach's dependency graph)

- [`nn-weights`](./nn-weights.md) — Nearest-neighbour indicator weights (1-NN)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch06_LocalAveraging/Estimators.lean`
- **Theorem/def name:** `nnWeights_localAvg`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

