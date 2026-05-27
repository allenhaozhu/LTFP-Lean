# Generalization bound for L²-regularized linear predictors (ridge)

**ID:** `linear-predictor-l2-bound`  
**Chapter:** Ch04 (Bach §4.5.4)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** in_lean_rademacher  
**Topic tags:** `Ridge`

## Statement

_See textbook excerpt below or [`tasks/linear-predictor-l2-bound/`](../../../tasks/linear-predictor-l2-bound/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Generalization bound for L²-regularized linear predictors

**Concept ID:** `linear-predictor-l2-bound`
**Chapter:** Ch 4
**Section:** 4.5.4
**Pages:** 96-98
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
**Proposition 4.5 (Estimation error — linear predictions).** Assume that the loss function
is G-Lipschitz-continuous, with a set of linear prediction functions
F = {f_θ(x) = θ^⊤ ϕ(x), ‖θ‖_2 ≤ D}, where E[‖ϕ(x)‖_2^2] ≤ R^2. Let f̂ = f_{θ̂} ∈ F be the
minimizer of the empirical risk. Then

$$\mathbb{E}[R(f_{\hat\theta})] \le \inf_{\|\theta\|_2 \le D} R(f_\theta) + \frac{4 G R D}{\sqrt{n}}.$$

## Proof (verbatim)
"Using proposition 4.2 to relate the uniform deviation to the Rademacher average,
equation (4.15) to take care of the Lipschitz-continuous loss, and equation (4.16) to
account for the ℓ_2-norm constraint, we get the desired result. Note that the factor of 4
comes from symmetrization (proposition 4.2, which leads to a factor of 2), and equation (4.10)
in section 4.4 (which leads to another factor of 2)."

The three ingredients (recalled from the chapter):
- Proposition 4.2: E sup_{h∈H} (R(h) − R̂(h)) ≤ 2 R_n(H).
- Eq. (4.15) (contraction for Lipschitz loss): R_n(H) ≤ G · R_n(F).
- Eq. (4.16): R_n(F) ≤ √(E[‖ϕ(x)‖_2^2]) · D / √n ≤ R D / √n.
- Eq. (4.10): R(f̂) − inf_{f∈F} R(f) ≤ 2 sup_{f∈F} |R(f) − R̂(f)|.

Chaining: E[R(f̂)] − inf_{f∈F} R(f) ≤ 2 E sup |R−R̂| ≤ 4 R_n(H) ≤ 4G R_n(F) ≤ 4GRD/√n.

## Notes
- Dimension-independent bound — only ‖ϕ(x)‖_2 enters, not the ambient dim d.
- Three constants: 4 (twice from symmetrization × twice from estim-error decomposition);
  G (loss Lipschitz constant); RD (geometric).
- Generalizes to ℓ_p-balls via dual-norm Rademacher computation (Exercise 4.14, ℓ_1: extra √log d factor).
- Foundational for kernel-methods generalization in Chapter 7.

## Prerequisites (Bach's dependency graph)

- [`rademacher-tail-bound-separable`](./rademacher-tail-bound-separable.md) — Tail bound on uniform deviation, separable hypothesis class

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = in_lean_rademacher`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/Main.lean`
- **Theorem/def name:** `linear_predictor_l2_bound`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

