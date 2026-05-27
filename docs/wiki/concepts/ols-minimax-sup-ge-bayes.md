# Bach §3.7 Node 1: sup-over-θ ≥ Bayes-average (finite-grid pigeonhole)

**ID:** `ols-minimax-sup-ge-bayes`  
**Chapter:** Ch03 (Bach §3.7, p. 60)  
**Kind:** lemma  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** `Bayes-risk`, `Lower-bound`

## Statement

Node 1 of the B4 decomposition (docs/wiki/B4_DECOMPOSITION_PLAN.md). Classical pigeonhole: for any prior weight `w` on a finite grid `θ`, `∃ k, bound ≤ f(θ_k)` whenever `bound ≤ ∑ w_k · f(θ_k)`. Discharges the sup-vs-average step in the minimax → Bayes-risk reduction. Backed by Mathlib's `bayesRisk_le_minimaxRisk` and the LTFP-local `sup_ge_bayes_average` (~35 lines).


## Bach's textbook treatment

_No book excerpt available._ See [`tasks/ols-minimax-sup-ge-bayes/`](../../../tasks/ols-minimax-sup-ge-bayes/) if a context kit has been built, or generate one with `python -m tools.context_kit`.

## Prerequisites (Bach's dependency graph)

- [`ridge-bias-variance`](./ridge-bias-variance.md) — Ridge bias-variance trade-off (fixed design)

## Dependents (concepts that use this)

- [`ols-minimax-lower-bound`](./ols-minimax-lower-bound.md) — Minimax lower bound for least-squares (♦) — umbrella

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch03_LinearLeastSquares/FixedDesign.lean`
- **Theorem/def name:** `sup_ge_bayes_average`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- **No verified book excerpt** — verify before citing this concept by a textbook equation number; equation labels in synthesized notes can drift relative to the canonical Bach (2024) PDF.

