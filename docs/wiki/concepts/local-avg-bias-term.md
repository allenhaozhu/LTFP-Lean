# Pointwise bias term of a local-averaging estimator

**ID:** `local-avg-bias-term`  
**Chapter:** Ch06 (Bach §6.3, p. 163)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `ERM`

## Statement

_See textbook excerpt below or [`tasks/local-avg-bias-term/`](../../../tasks/local-avg-bias-term/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Pointwise bias term of a local-averaging estimator

**Concept ID:** `local-avg-bias-term`
**Chapter:** Ch 6
**Section:** 6.3
**Pages:** 163-165
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
From §6.3 "Generic Simplest Consistency Analysis" (pp. 163-164), Bach derives the bias-variance decomposition for any local-averaging estimator. Assuming `f*(x) = E[y|x]` and that the weight functions are independent of the labels, at a test point `x ∈ 𝒳`:

> $$\hat f(x) - f_*(x) \;=\; \sum_{i=1}^{n} y_i \hat w_i(x) - \mathbb E[y\mid x]$$
> $$=\; \sum_{i=1}^{n} \hat w_i(x)\bigl(y_i - \mathbb E[y_i \mid x_i]\bigr) \;+\; \sum_{i=1}^{n} \hat w_i(x)\bigl(\mathbb E[y_i \mid x_i] - \mathbb E[y\mid x]\bigr)$$
> $$=\; \sum_{i=1}^{n} \hat w_i(x)\bigl(y_i - \mathbb E[y_i \mid x_i]\bigr) \;+\; \sum_{i=1}^{n} \hat w_i(x)\bigl(f_*(x_i) - f_*(x)\bigr).$$

Taking expectations (over labels only, conditional on inputs):

> $$\mathbb E\bigl[(\hat f(x) - f_*(x))^2 \,\big|\, x_1, \ldots, x_n\bigr]$$
> $$=\; \Bigl[\sum_{i=1}^{n} \hat w_i(x)\bigl(f_*(x_i) - f_*(x)\bigr)\Bigr]^2 \;+\; \sum_{i=1}^{n} \hat w_i(x)^2\, \mathbb E\bigl[(y_i - \mathbb E[y_i\mid x_i])^2\,\big|\, x_i\bigr]$$
> $$=\; \text{bias} \;+\; \text{variance},$$
> with a "bias" term that is zero if $f_*$ is constant, and a "variance" term that is zero when $y$ is a deterministic function of $x$ (i.e., $\sigma = 0$).

The **pointwise bias term** in Bach's decomposition is therefore
$$\Bigl[\sum_{i=1}^{n} \hat w_i(x)\bigl(f_*(x_i) - f_*(x)\bigr)\Bigr]^2 \;=\; \Bigl[\sum_{i=1}^{n} \hat w_i(x)\, f_*(x_i) \;-\; f_*(x)\Bigr]^2$$
(using `∑ wᵢ(x) = 1` so that `f*(x) = ∑ wᵢ(x) · f*(x)`).

The Lean definition `localAvgBiasTerm` captures the **inner** quantity `∑ᵢ wᵢ(x) · f*(xᵢ) − f*(x)` (without the square), which is what Bach actually decomposes.

## Proof (verbatim)
N/A — this is a definition, with the derivation above showing where it comes from. Bach's footnote 6 (p. 164) notes:
> What we call "bias" in this book is sometimes referred to as the "squared bias."

## Notes
- Lean carrier: `LTFP/Ch06_LocalAveraging/Consistency.lean#localAvgBiasTerm`. Definition:
  `localAvgBiasTerm fstar xs w x := ∑ i, w x i * fstar (xs i) − fstar x`.
- This is the **unsquared, pre-expectation, deterministic** part of Bach's decomposition. Squaring + integrating over `x` then gives the bias contribution to the expected excess risk in (6.3)-(6.5) (p. 164).
- The Lean library proves two sanity lemmas: `localAvgBiasTerm_const_zero` (constant `f*` gives zero bias, assuming `∑ wᵢ(x) = 1`) and `localAvgBiasTerm_zero_fstar` (the trivial `f* = 0` case — proved via `simp`).
- Bach's proof technique: linearity of expectation plus the conditional-variance identity. No nontrivial inequality is invoked at this stage — the upper bounds via Jensen come later (p. 164, (6.4)).
- Ambiguity: Bach toggles between "bias" and "squared bias" terminology (footnote 6); the Lean definition uses the unsquared form, with squaring deferred to wherever the bound feeds into excess risk.

## Prerequisites (Bach's dependency graph)

- [`local-averaging`](./local-averaging.md) — Local averaging predictors (k-NN, partition, kernel)
- [`uniform-local-weights`](./uniform-local-weights.md) — Uniform local-averaging weights wᵢ(x) = 1/n

## Dependents (concepts that use this)

- [`localavg-bias-zero-fstar`](./localavg-bias-zero-fstar.md) — localAvgBiasTerm vanishes when fstar = 0

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch06_LocalAveraging/Consistency.lean`
- **Theorem/def name:** `localAvgBiasTerm`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

