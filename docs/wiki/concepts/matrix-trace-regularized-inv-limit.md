# Bach §3.7 Node 4: tr((Σ̂+λI)⁻¹ Σ̂) → d as λ → 0 (full-rank Σ̂)

**ID:** `matrix-trace-regularized-inv-limit`  
**Chapter:** Ch03 (Bach §3.7, p. 61)  
**Kind:** lemma  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Kernel`, `Neural-network`, `Matrix/LinAlg`

## Statement

Node 4 of the B4 decomposition. The limit `tr((Σ̂+λI)⁻¹ Σ̂) → tr(I) = d` as `λ → 0⁺` when `Σ̂` is full-rank. Self-contained (~120 lines), no LTFP-local dependencies — a Mathlib-PR-shaped artifact. Already wired into `bayes_trace_limit_discharged`. Shared with B8 NTK (same shape `(Σ + λI)⁻¹ Σ → I` appears in kernel-regression analysis).


## Bach's textbook treatment

_No book excerpt available._ See [`tasks/matrix-trace-regularized-inv-limit/`](../../../tasks/matrix-trace-regularized-inv-limit/) if a context kit has been built, or generate one with `python -m tools.context_kit`.

## Prerequisites (Bach's dependency graph)

- [`ridge-bias-variance`](./ridge-bias-variance.md) — Ridge bias-variance trade-off (fixed design)

## Dependents (concepts that use this)

- [`ols-minimax-lower-bound`](./ols-minimax-lower-bound.md) — Minimax lower bound for least-squares (♦) — umbrella

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/MathlibExt/LinearAlgebra/MatrixInverseLimit.lean`
- **Theorem/def name:** `trace_regularized_inv_mul_tendsto_card`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- **No verified book excerpt** — verify before citing this concept by a textbook equation number; equation labels in synthesized notes can drift relative to the canonical Bach (2024) PDF.

