# Score-vector loss via witnessed argmax

**ID:** `score-loss`  
**Chapter:** Ch13 (Bach §13.3.1, p. 392)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/score-loss/`](../../../tasks/score-loss/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Score-vector loss via witnessed argmax

**Concept ID:** `score-loss`
**Chapter:** Ch 13
**Section:** 13.3.1 "Score Functions and Decoding Step"
**Pages:** 380, 391-392
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

The score-vector loss composes Bach's decoding step with the task loss. On
page 380 he writes the predictor as

> "f(x) ∈ arg max_{j∈{1,...,k}} g_j(x) ⊂ Y"

and the empirical/expected risks in §13.3.1 (page 392):

> "We then need a surrogate loss S : Y × H → R, which will be used to form
> empirical and expected surrogate risks:
>
>     R̂_S(g) = (1/n) Σ_{i=1}^n S(y_i, g(x_i))   and   R_S(g) = E[S(y, g(x))]."

For the *task* loss (not surrogate) we plug the decoded prediction into the
0-1 loss. With the witnessed-argmax predicate `IsArgmax s j`, the Lean
`scoreLoss s y j hj` evaluates `multicategoryLoss y j` whenever `j` is a
valid argmax index of the score vector `s`. This is the
"task-loss-at-the-decoded-label" pattern Bach uses implicitly: the
prediction `f(x)` is any argmax index of `g(x)`, and the loss paid is
`1_{y ≠ f(x)}`.

By writing `scoreLoss s y j hj` with the witness `hj : IsArgmax s j` as a
proof argument, we avoid choosing a tie-breaking convention; both Bach's
"randomized decoder" remark (page 380, footnote 1) and the symmetry of the
0-1 loss make this safe.

## Proof (verbatim)
Definitional. No proof — this is the composition of the decoder (argmax)
with the multicategory 0-1 loss.

## Notes
- The witness-style signature (`scoreLoss s y j hj` with `hj : IsArgmax s j`)
  is the Lean equivalent of Bach's "f(x) ∈ arg max..." set-membership
  phrasing on page 380. It defers tie-breaking to the caller without losing
  any mathematical content because the 0-1 loss only sees the chosen index.
- Technique in one line: feed the decoded label into `multicategoryLoss`.
- Ambiguity: the value depends only on whether `j = y`, not on the score
  vector `s` directly — but the witness `hj` ensures we are measuring the
  loss of an actual argmax prediction.

## Prerequisites (Bach's dependency graph)

- [`is-argmax`](./is-argmax.md) — Argmax predicate for a score vector
- [`multicategory-loss`](./multicategory-loss.md) — Multicategory 0-1 loss for k classes

## Dependents (concepts that use this)

- [`margin-satisfied`](./margin-satisfied.md) — Max-margin (structured SVM): MarginSatisfied predicate

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch13_StructuredPrediction/Surrogates.lean`
- **Theorem/def name:** `scoreLoss`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

