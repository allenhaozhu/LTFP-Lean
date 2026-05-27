# Multicategory 0-1 loss for k classes

**ID:** `multicategory-loss`  
**Chapter:** Ch13 (Bach §13.1.1, p. 380)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/multicategory-loss/`](../../../tasks/multicategory-loss/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Multicategory 0-1 loss for k classes

**Concept ID:** `multicategory-loss`
**Chapter:** Ch 13
**Section:** 13.1 / 13.1.1 (setup) and 13.2 (loss-matrix form)
**Pages:** 380, 387
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

The multicategory 0-1 loss is the canonical loss for `k`-class classification
introduced at the start of Chapter 13. Bach sets up the framework in §13.1
(page 380):

> "We dealt with binary classification with Y = {−1, 1} in section 4.1.1 by
> estimating real-valued prediction functions and taking their signs. Going
> from 2 to k > 2 classes requires multidimensional vector-space valued
> functions. To preserve symmetry among classes, we will consider
> k-dimensional outputs (rather (k − 1)-dimensional). That is, for
> Y = {1, . . . , k}, we will estimate a function g : X → R^k and predict the
> label through f(x) ∈ arg max_{j∈{1,...,k}} g_j(x) ⊂ Y."

The Bayes predictor for the 0–1 loss is stated immediately after (page 380):

> "the Bayes predictor for the 0–1 loss, equal to arg max_{z∈{1,...,k}}
> P(y = z|x)."

The explicit loss-matrix form is given in §13.2 (page 387, in the list of
classic structured-prediction examples):

> "Multicategory classification: Y = {1, . . . , k} and a loss matrix
> L ∈ R^{k×k}, with ℓ(i, j) = L_{ij}. The usual 0–1 loss from section 13.1
> corresponds to L_{ij} = 1_{i≠j}, but in most applications, errors do not
> have the same cost (e.g., in spam prediction, classifying a legitimate email
> as spam costs much more than the opposite)."

In Lean we vendor this as `multicategoryLoss y ŷ = if y = ŷ then 0 else 1`,
i.e. the `1_{y ≠ ŷ}` indicator from Bach's loss-matrix notation.

## Proof (verbatim)
Definitional. No proof — this is the loss function itself.

## Notes
- Two equivalent phrasings appear in the book: (a) the predictor-side
  description "predict arg max; pay 1 if wrong, 0 if right" (page 380), and
  (b) the loss-matrix form `L_{ij} = 1_{i ≠ j}` (page 387, in §13.2). The
  Lean `multicategoryLoss` matches (b) directly.
- Technique in one line: indicator function on disagreement.
- No ambiguity. The 0-1 loss is symmetric (`L_{ij} = L_{ji}`), bounded
  in `{0, 1}`, and vanishes on the diagonal — all of which are recorded as
  separate concept entries (`multicategory-loss-symm`,
  `multicat-zero-or-one`, `multicat-loss-diag`).

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

- [`multicat-loss-diag`](./multicat-loss-diag.md) — multicategoryLoss y y = 0
- [`multicat-loss-in-unit`](./multicat-loss-in-unit.md) — Multicat loss in 0-1 unit interval
- [`multicat-zero-or-one`](./multicat-zero-or-one.md) — Multicat loss is 0 or 1
- [`multicategory-eq-one-iff`](./multicategory-eq-one-iff.md) — Multicat loss = 1 iff prediction wrong
- [`multicategory-loss-le-one`](./multicategory-loss-le-one.md) — Multicategory loss is bounded by 1
- [`multicategory-loss-symm`](./multicategory-loss-symm.md) — Multicategory loss is symmetric
- [`score-loss`](./score-loss.md) — Score-vector loss via witnessed argmax

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch13_StructuredPrediction/Multicategory.lean`
- **Theorem/def name:** `multicategoryLoss`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

