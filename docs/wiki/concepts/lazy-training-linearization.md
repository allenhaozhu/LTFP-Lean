# Lazy-training linearization: `f(θ_t) ≈ f(θ₀) + ⟨∇f(θ₀), θ_t − θ₀⟩` (N5)

**ID:** `lazy-training-linearization`  
**Chapter:** Ch12 (Bach §12.4, p. 377)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** pending  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Concentration`, `Neural-network`

## Statement

Node N5 of the B8 decomposition. Combine N1 (gradient-flow ODE setup, already landed via `LTFP/MathlibExt/Calculus/GradientFlow.lean` and `lazy_training_via_continuous_flow`), N3 (random-init feature map + rank-1 outer products), and N4 (NTK concentration) to show: along gradient flow with lazy scaling `α = √m`, `f(θ_t) ≈ f(θ₀) + ⟨∇f(θ₀), θ_t − θ₀⟩` uniformly on the training set with deviation `O(1/√m)`. The algebraic skeleton `linearization_quadratic` (toy `f(θ) = ½‖θ‖²`) already proved in `ntk-symmetry-anchor`; generalising to a network `h(V)` is the residual. M-scale (~1 week) once N4 lands.


## Bach's textbook treatment

_No book excerpt available._ See [`tasks/lazy-training-linearization/`](../../../tasks/lazy-training-linearization/) if a context kit has been built, or generate one with `python -m tools.context_kit`.

## Prerequisites (Bach's dependency graph)

- [`ntk-concentration-scalar-hoeffding`](./ntk-concentration-scalar-hoeffding.md) — Empirical NTK concentration via scalar Hoeffding + union bound (N4 alt)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `TBD`
- **Theorem/def name:** `lazy_training_linearization`
- **Status:** pending
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- **No verified book excerpt** — verify before citing this concept by a textbook equation number; equation labels in synthesized notes can drift relative to the canonical Bach (2024) PDF.

