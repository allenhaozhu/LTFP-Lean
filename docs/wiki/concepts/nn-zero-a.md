# NN with zero output weights = 0

**ID:** `nn-zero-a`  
**Chapter:** Ch09 (Bach §9.3)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Neural-network`

## Statement

_See textbook excerpt below or [`tasks/nn-zero-a/`](../../../tasks/nn-zero-a/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — NN with zero output weights = 0

**Concept ID:** `nn-zero-a`
**Chapter:** Ch 9
**Section:** 9.3 (linearity in output weights, used throughout)
**Pages:** 253, 257-258 (book; PDF pages 269, 273-274)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

A single-hidden-layer ReLU network whose output weights all vanish (η_j = 0 for
all j) is identically zero as a function of x:

>     f_0(x) = Σ_{j=1}^m 0 · σ(w_j^⊤ x + b_j) = 0   for all x ∈ R^d.

This is the η = 0 specialisation of Bach's equation (9.1) (p. 249).

## Proof (verbatim)

Direct: each summand is 0 · σ(·) = 0, and Σ_j 0 = 0. Therefore f_0 ≡ 0.

Equivalently, this is the "η ↦ f_η is R-linear ⇒ f_0 = 0" specialisation of the
linearity-in-output-weights structure (concept `single-hidden-relu-add-a`).

## Notes

- **Intermediate lemmas:** `0 · y = 0`, finite-sum-of-zeros = 0; or the
  generic fact that a linear map sends the zero vector to zero.
- **Technique in one line:** `f_η` is R-linear in η, so f_0 = 0.
- **Why this matters in Bach.** Used implicitly:
  - **§9.2.3, p. 254**, equation (9.3): the linear-in-η structure is exploited
    via Hölder's inequality `sup_{‖η‖_1 ≤ D} z^⊤ η = D‖z‖_∞`. The η = 0 case
    is the trivial baseline.
  - **§9.3.2, p. 257-258**, equation (9.4): the integral representation
    f(x) = ∫ (w^⊤ x + b)_+ dν(w, b) with ν = Σ η_j δ_(w_j, b_j) sends η = 0 (no
    Dirac mass anywhere) to the zero measure and hence to f ≡ 0.
  - **§9.3.6**, Frank-Wolfe construction: the iterate f_0 (initial point) is
    customarily taken to be 0 ∈ F_1.
- **Companion concept.** `single-hidden-relu-add-a` (additivity / R-linearity
  in η).

## Prerequisites (Bach's dependency graph)

- [`single-hidden-relu`](./single-hidden-relu.md) — Single-hidden-layer ReLU neural network

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch09_NeuralNetworks/SingleHidden.lean`
- **Theorem/def name:** `singleHiddenReLU_zero_a`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

