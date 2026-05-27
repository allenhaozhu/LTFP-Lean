# Max-margin (structured SVM): MarginSatisfied predicate

**ID:** `margin-satisfied`  
**Chapter:** Ch13 (Bach §13.5, p. 398)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Structured-prediction`

## Statement

_See textbook excerpt below or [`tasks/margin-satisfied/`](../../../tasks/margin-satisfied/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Max-margin (structured SVM): MarginSatisfied predicate

**Concept ID:** `margin-satisfied`
**Chapter:** Ch 13
**Section:** 13.5 "Max-Margin Formulations" / 13.5.1 "Structured Support Vector Machines"
**Pages:** 398-399
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

The structured-SVM margin condition is introduced at the start of §13.5
(page 398):

> "Rather than extending the square or logistic loss from binary
> classification to structured prediction, we can also extend the hinge
> loss, leading to 'max-margin' formulations, with reference to the
> geometric interpretation from section 4.1.2."

The structured SVM construction in §13.5.1 (page 399) gives the surrogate
via the margin condition:

> "Following Taskar et al. (2005) and Tsochantaridis et al. (2005), we
> consider a traditional extension of the support vector machine (SVM)
> with a simple interpretation.
>
> To introduce the convex surrogate in its full generality, we consider a
> score function h that is a function of x ∈ X and y ∈ Y, with the decoder
>
>     arg max_{z ∈ Y} h(x, z).
>
> The surrogate function S(y, h(x, ·)) is defined as the minimal ξ ∈ R+
> such that, for all z ∈ Y,
>
>     h(x, y) ≥ h(x, z) + ℓ(z, y) − ℓ(y, y) − ξ.
>
> The intuition behind this definition is that we aim to make h(x, y)
> larger for the observed y than for the other h(x, z), with a difference
> that is stronger when y and z are further apart, as measured by the loss."

For the multicategory 0-1 loss (where `ℓ(y,y) = 0` and `ℓ(z,y) = 1_{z≠y}`),
the constraint specializes to: for all `j ≠ y`, `s_y ≥ s_j + 1 − ξ`,
equivalently (with `γ = 1 − ξ`) `s_y − s_j ≥ γ` for all `j ≠ y`.

The Lean predicate `MarginSatisfied s y γ` records exactly this:
"the score `s_y` of the true class exceeds every other score by at least
the margin `γ`," i.e. `∀ j ≠ y, s y − s j ≥ γ`. This is the multicategory
analogue of the binary hinge condition `y · g(x) ≥ 1`.

The earlier hinge-loss form for multicategory classification (equation
13.1, page 381) confirms the algebra:

> "S(y, g(x)) = sup_{j∈{1,...,k}} (1_{y≠j} + g_j(x) − g_y(x)) ."   (13.1)

Setting this surrogate to zero is equivalent to `MarginSatisfied g(x) y 1`.

## Proof (verbatim)
Definitional. No proof — this is the geometric margin condition that
defines hard-margin satisfiability for the structured SVM.

## Notes
- Bach uses the slack-variable form (`ξ ≥ 0`); the Lean predicate uses the
  direct margin `γ = 1 − ξ`. The two are interchangeable: `MarginSatisfied`
  is the "ξ = 0 with margin γ" view, while equation (13.1)'s `sup ≤ 0` is
  the same condition with `γ = 1`.
- Technique in one line: universal quantifier over all wrong labels, with a
  uniform lower bound on the score gap.
- For multicategory 0-1 loss, `MarginSatisfied s y γ` for any `γ > 0`
  implies that `y` is the *strict* argmax of `s`; the converse (with
  `γ = min_{j≠y} (s_y − s_j) > 0`) also holds.

## Prerequisites (Bach's dependency graph)

- [`score-loss`](./score-loss.md) — Score-vector loss via witnessed argmax

## Dependents (concepts that use this)

- [`margin-mono`](./margin-mono.md) — Margin satisfaction monotone in γ

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch13_StructuredPrediction/Surrogates.lean`
- **Theorem/def name:** `MarginSatisfied`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

