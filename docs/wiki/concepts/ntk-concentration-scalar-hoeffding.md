# Empirical NTK concentration via scalar Hoeffding + union bound (N4 alt)

**ID:** `ntk-concentration-scalar-hoeffding`  
**Chapter:** Ch12 (Bach §12.4, p. 376)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** pending  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Kernel`, `Gaussian`, `Sub-Gaussian`, `Concentration`, `Neural-network`, `Matrix/LinAlg`

## Statement

Node N4 alternative path of the B8 decomposition (docs/wiki/B8_DECOMPOSITION_PLAN.md). For a finite input set, treat each kernel entry `K̂_m(xᵢ,xⱼ) − K(xᵢ,xⱼ)` as an iid average of bounded scalars, apply Hoeffding per entry, and union-bound over `n²` entries. Yields entrywise `O(√(log(n²/δ)/m))` → operator-norm `O(n·√(log(n²/δ)/m))` via `‖·‖_op ≤ n · ‖·‖_max`. Looser by `√n` than Tropp matrix Bernstein but uses only scalar concentration already in Mathlib (`SubGaussian.lean`) — no Lieb, no Tropp, no matrix MGF. Unblocks B8 without waiting on B6's operator-theory tower. Honesty note: Bach §12.4 is `(◇)` and states the LLN-style claim without non-asymptotic bound; this goes beyond what Bach proves (Jacot et al. 2018 / Arora et al. 2019 territory).


## Bach's textbook treatment

_No book excerpt available._ See [`tasks/ntk-concentration-scalar-hoeffding/`](../../../tasks/ntk-concentration-scalar-hoeffding/) if a context kit has been built, or generate one with `python -m tools.context_kit`.

## Prerequisites (Bach's dependency graph)

- [`hoeffding-lemma`](./hoeffding-lemma.md) — Hoeffding's lemma (MGF bound for bounded variables)
- [`ntk-symmetry-anchor`](./ntk-symmetry-anchor.md) — NTK kernel symmetry algebraic anchor

## Dependents (concepts that use this)

- [`lazy-training-linearization`](./lazy-training-linearization.md) — Lazy-training linearization: `f(θ_t) ≈ f(θ₀) + ⟨∇f(θ₀), θ_t − θ₀⟩` (N5)

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `TBD`
- **Theorem/def name:** `ntk_concentration_scalar_hoeffding`
- **Status:** pending
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- **No verified book excerpt** — verify before citing this concept by a textbook equation number; equation labels in synthesized notes can drift relative to the canonical Bach (2024) PDF.

