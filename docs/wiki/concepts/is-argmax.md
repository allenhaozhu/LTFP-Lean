# Argmax predicate for a score vector

**ID:** `is-argmax`  
**Chapter:** Ch13 (Bach §13.3.1, p. 392)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/is-argmax/`](../../../tasks/is-argmax/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Argmax predicate for a score vector

**Concept ID:** `is-argmax`
**Chapter:** Ch 13
**Section:** 13.3.1 "Score Functions and Decoding Step"
**Pages:** 391-392
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

The argmax predicate captures the "decoding step" in Bach's general
surrogate framework. He introduces score functions and the decoder in
§13.3.1 (pages 391-392):

> "In this chapter, we will consider functions f : X → Y that can be written
> as
>
>     f(x) = dec ∘ g(x),
>
> where
>   • g : X → H is a function with values in the vector space H, referred
>     to as a 'score function.'
>   • dec : H → Y is the 'decoding function,' which can be randomized (in
>     particular when taking maxima of functions that may have equal
>     values)."

For multicategory classification with `H = R^k`, the canonical decoder is
the argmax (Bach gives this already on page 380):

> "we will estimate a function g : X → R^k and predict the label through
> f(x) ∈ arg max_{j∈{1,...,k}} g_j(x) ⊂ Y."

The Lean predicate `IsArgmax s j` says: index `j` realizes the maximum of
the score vector `s : Fin k → ℝ`, i.e. `∀ i, s i ≤ s j`. This is the
membership condition `j ∈ arg max_i s i`. Bach notes (footnote 1, page 380)
that equality cases ("ties") "do not really matter, and precise statements
based on randomized predictions are left as exercises" — which justifies
using a non-strict `≤` in the predicate (any tied index is a valid argmax
witness).

## Proof (verbatim)
Definitional. No proof — this is the witness predicate for "j is an argmax
index of the score vector s."

## Notes
- The predicate is set-membership in `arg max`, not a function returning a
  single index. This avoids the tie-breaking complications Bach explicitly
  defers to exercises (page 380, footnote 1).
- Technique in one line: universal quantifier over indices.
- Ambiguity: when scores tie, multiple indices satisfy `IsArgmax s j`. This
  matches Bach's treatment (decoder can be randomized).

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

- [`score-loss`](./score-loss.md) — Score-vector loss via witnessed argmax

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch13_StructuredPrediction/Surrogates.lean`
- **Theorem/def name:** `IsArgmax`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

