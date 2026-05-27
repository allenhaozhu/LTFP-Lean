# localAvgBiasTerm vanishes when fstar = 0

**ID:** `localavg-bias-zero-fstar`  
**Chapter:** Ch06 (Bach §6.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `ERM`

## Statement

_See textbook excerpt below or [`tasks/localavg-bias-zero-fstar/`](../../../tasks/localavg-bias-zero-fstar/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — localAvgBiasTerm vanishes when fstar = 0

**Concept ID:** `localavg-bias-zero-fstar`
**Chapter:** Ch 6
**Section:** 6.3
**Pages:** 163-164
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
This concept is a degenerate-case sanity lemma for the bias term Bach introduces in the consistency analysis of §6.3 (p. 164). Recall (see also `local-avg-bias-term`):

> with a "bias" term that is zero if $f_*$ is constant, and a "variance" term that is zero when $y$ is a deterministic function of $x$ (i.e., $\sigma = 0$).

Bach explicitly flags the constant-`f*` case as bias-free in the parenthetical above. The Lean library checks the trivial sub-case `f* ≡ 0`:
$$\text{localAvgBiasTerm}(\mathbf 0,\ xs,\ w,\ x) \;=\; 0.$$

By the definition `localAvgBiasTerm fstar xs w x := ∑ᵢ w x i · fstar (xs i) − fstar x`, plugging `fstar = 0` gives `∑ᵢ w x i · 0 − 0 = 0`, which holds **without** any sum-to-one hypothesis on the weights.

## Proof (verbatim)
Not stated explicitly by Bach; it's a direct corollary of his "constant `f*` ⇒ bias = 0" remark on p. 164. The argument:

> If $f_* \equiv c$, then $\sum_{i=1}^{n} \hat w_i(x)\bigl(f_*(x_i) - f_*(x)\bigr) = \sum_{i=1}^{n} \hat w_i(x)(c - c) = 0$.

(sketch — one-line cancellation; the `c = 0` case used in Lean avoids needing `∑ wᵢ = 1`.)

## Notes
- Lean carrier: `LTFP/Ch06_LocalAveraging/Consistency.lean#localAvgBiasTerm_zero_fstar`. Proof is `unfold localAvgBiasTerm; simp` — a one-liner.
- A stronger companion lemma in the same file, `localAvgBiasTerm_const_zero c xs w x (hsum : ∑ i, w x i = 1) : localAvgBiasTerm (fun _ => c) xs w x = 0`, captures the general constant-`f*` case Bach actually states (which requires `∑ wᵢ = 1`).
- Proof technique: trivial — only needs `mul_zero` and that the empty/all-zero sum is zero. No probabilistic or analytic machinery.
- Relation to Bach's text: the `c = 0` case sidesteps the `∑ wᵢ = 1` assumption, making it a strictly weaker (and Lean-friendlier) lemma than the constant-`c` version. Both are useful as smoke tests for the `localAvgBiasTerm` definition.
- No ambiguity.

## Prerequisites (Bach's dependency graph)

- [`local-avg-bias-term`](./local-avg-bias-term.md) — Pointwise bias term of a local-averaging estimator

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch06_LocalAveraging/Consistency.lean`
- **Theorem/def name:** `localAvgBiasTerm_zero_fstar`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

