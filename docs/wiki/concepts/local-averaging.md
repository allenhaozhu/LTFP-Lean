# Local averaging predictors (k-NN, partition, kernel)

**ID:** `local-averaging`  
**Chapter:** Ch02 (Bach §2.3.1, p. 31)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Kernel`, `Local-averaging`

## Statement

_See textbook excerpt below or [`tasks/local-averaging/`](../../../tasks/local-averaging/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Local averaging predictors

**Concept ID:** `local-averaging`
**Chapter:** Ch 2
**Section:** 2.3.1 (Local Averaging)
**Pages:** 31-32
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

From §2.3.1 (p. 31):

> The goal here is to approximate/emulate the Bayes predictor (e.g.,
> `f∗(x') = E[y | x = x']` for least-squares regression, or
> `f∗(x') = arg max_{z ∈ Y} P(y = z | x = x')` for classification with the 0–1 loss)
> from empirical data. This is often done by explicit or implicit estimation of the
> conditional distribution by local averaging (k-nearest neighbors, which is used as
> the primary example for this chapter; Nadaraya-Watson estimators; or decision
> trees).

**The k-nearest-neighbor classifier** (p. 31):

> Given `n` observations `(x1, y1), …, (xn, yn)` where `X` is a metric space and
> `Y ∈ {−1, +1}`, a new point `x_test` is classified by a majority vote among the
> `k` nearest neighbors of `x_test`.

Bach also discusses the bias/variance tradeoff in `k` (p. 31-32):

> When `k` is too large, there is underfitting (the learned function is too close to
> a constant, which is too simple), while for `k` too small, there is overfitting
> (there is a strong discrepancy between the testing and training errors).

## Proof (verbatim)

(Definitional / family description — no theorem.) Bach defers detailed analysis to
chapter 6.

## Notes

- Local-averaging methods are the **first** of the two main algorithm families Bach
  treats; the other is ERM (§2.3.2).
- The defining feature: prediction at `x_test` depends only on training points whose
  inputs are *near* `x_test` (geometrically or topologically).
- Examples Bach explicitly mentions:
  - k-nearest-neighbors (primary chapter 2 example, detailed in chapter 6).
  - Nadaraya-Watson kernel regression (chapter 6).
  - Decision trees (mentioned in passing).
  - Implicitly: partition estimators (cubes / histograms).
- Lean target: choose **one** concrete instance (likely majority-vote over the full
  sample as a degenerate "k = n" case, or constant-output Nadaraya-Watson with the
  trivial uniform kernel) for a definitional anchor. The full consistency theorems
  (Stone 1977) are deferred to chapter 6.

## Prerequisites (Bach's dependency graph)

- [`population-risk`](./population-risk.md) — Population risk R(f) = E[ℓ(f(x), y)]

## Dependents (concepts that use this)

- [`local-avg-bias-term`](./local-avg-bias-term.md) — Pointwise bias term of a local-averaging estimator
- [`localavg-add-y`](./localavg-add-y.md) — localAvg is linear in labels Y
- [`localavg-neg-y`](./localavg-neg-y.md) — localAvg(-Y) = -localAvg(Y)
- [`localavg-smul-y`](./localavg-smul-y.md) — localAvg is homogeneous in labels
- [`nn-weights`](./nn-weights.md) — Nearest-neighbour indicator weights (1-NN)
- [`partition-weights`](./partition-weights.md) — Partition-based weights (histogram estimator)
- [`uniform-local-weights`](./uniform-local-weights.md) — Uniform local-averaging weights wᵢ(x) = 1/n

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch02_SupervisedLearning/LocalAveraging.lean`
- **Theorem/def name:** `localAvg`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

