# ReLU equals itself (reflexivity anchor)

**ID:** `relu-eq-relu`  
**Chapter:** Ch09 (Bach §F6)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/relu-eq-relu/`](../../../tasks/relu-eq-relu/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — ReLU equals itself (reflexivity anchor)

**Concept ID:** `relu-eq-relu`
**Chapter:** Ch 9
**Section:** 9.2 (F6 foundation file in LTFP-Lean)
**Pages:** 249 (book; PDF page 265)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For all z ∈ R,

>     relu(z) = relu(z).

## Proof (verbatim)

Reflexivity of equality. There is nothing to prove.

## Notes

- **Intermediate lemmas:** none.
- **Technique in one line:** `rfl`.
- **Why this exists in the registry.** This is a **placeholder / anchor lemma**
  in the LTFP-Lean foundation file. It is not a Bach textbook lemma. Its role is
  organisational: it provides a registered `lean_target` so that downstream
  tactics, simp sets, or notational unfoldings can hang off a canonical name.
  Bach does not mention it.
- **Ambiguities for Lean formalization.** None. The Lean target is `rfl`. The
  concept exists in the registry to keep the F6 file's coverage report aligned
  with the file's actual surface area.

## Prerequisites (Bach's dependency graph)

- [`neural-net-foundation`](./neural-net-foundation.md) — Neural-network foundation: ReLU activation

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/NeuralNet.lean`
- **Theorem/def name:** `relu_eq_relu`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

