# Margin satisfaction monotone in γ

**ID:** `margin-mono`  
**Chapter:** Ch13 (Bach §13.5)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/margin-mono/`](../../../tasks/margin-mono/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Margin satisfaction monotone in γ

**Concept ID:** `margin-mono`
**Chapter:** Ch 13
**Section:** 13.5 / 13.5.1 "Structured Support Vector Machines"
**Pages:** 398-399
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Sanity lemma: if `γ₁ ≤ γ₂` and the score vector `s` satisfies the margin
condition with margin `γ₂` for the true class `y`, then it also satisfies
the margin condition with the smaller margin `γ₁`. Formally:

    γ₁ ≤ γ₂ → MarginSatisfied s y γ₂ → MarginSatisfied s y γ₁.

Bach does not state this as a numbered proposition — it is the trivial
monotonicity of the structured-SVM hard-margin constraint from §13.5.1
(page 399):

> "The surrogate function S(y, h(x, ·)) is defined as the minimal ξ ∈ R+
> such that, for all z ∈ Y,
>
>     h(x, y) ≥ h(x, z) + ℓ(z, y) − ℓ(y, y) − ξ."

A larger admissible slack `ξ` (equivalently a smaller required margin)
trivially admits any tighter scenario. The same monotonicity is used
implicitly in the hinge-loss equation (13.1) on page 381:

> "S(y, g(x)) = sup_{j∈{1,...,k}} (1_{y≠j} + g_j(x) − g_y(x))."   (13.1)

If `s_y − s_j ≥ γ₂` for all `j ≠ y`, then *a fortiori* `s_y − s_j ≥ γ₁`
for any `γ₁ ≤ γ₂`. This monotonicity lets calibration-function arguments
trade off the geometric margin against the surrogate value continuously.

## Proof (verbatim)
Definitional. From `s_y − s_j ≥ γ₂` and `γ₁ ≤ γ₂`, transitivity of `≤`
gives `s_y − s_j ≥ γ₁`. Apply to every `j ≠ y`.

## Notes
- Used in calibration-function arguments (Bach's §13.5.2 / §13.6) where
  one trades off the geometric margin against the surrogate gap.
- Technique in one line: transitivity of `≤` under the universal
  quantifier over wrong labels.
- No ambiguity — a one-line monotonicity check on a `∀`-quantified
  inequality.

## Prerequisites (Bach's dependency graph)

- [`margin-satisfied`](./margin-satisfied.md) — Max-margin (structured SVM): MarginSatisfied predicate

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch13_StructuredPrediction/Surrogates.lean`
- **Theorem/def name:** `MarginSatisfied.mono`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

