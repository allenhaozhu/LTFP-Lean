# NN with zero bias, 1 neuron

**ID:** `nn-zero-bias-one-neuron`  
**Chapter:** Ch09 (Bach §9.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Neural-network`

## Statement

_See textbook excerpt below or [`tasks/nn-zero-bias-one-neuron/`](../../../tasks/nn-zero-bias-one-neuron/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — NN with zero bias, single neuron

**Concept ID:** `nn-zero-bias-one-neuron`
**Chapter:** Ch 9
**Section:** 9.2
**Pages:** 249 (book; PDF page 265)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

A single-neuron (m = 1) ReLU network with zero bias (b = 0) reduces to a scaled,
ReLU-rectified linear functional:

>     f(x) = η · σ(w^⊤ x + 0) = η · (w^⊤ x)_+ = η · relu(w^⊤ x).

This is the m = 1, b = 0 specialisation of Bach's equation (9.1) (p. 249):

>     f(x) = Σ_{j=1}^m η_j σ(w_j^⊤ x + b_j).

## Proof (verbatim)

Specialisation: take m = 1, then the sum collapses to its single term,
η_1 σ(w_1^⊤ x + b_1). Take b_1 = 0 and rename (η_1, w_1) = (η, w):
f(x) = η σ(w^⊤ x). For ReLU specifically, σ = (·)_+ = relu.

There is nothing to prove beyond unfolding the definition.

## Notes

- **Intermediate lemmas:** none — direct unfolding of (9.1).
- **Technique in one line:** specialise the width-m sum to m = 1, then set
  b_1 = 0.
- **Why this exists in the registry.** Sanity / closure lemma for the
  `single-hidden-relu` definition. Useful for downstream proofs that need to
  reason about a "smallest non-trivial network" — e.g., the m = 1 case of any
  inductive argument over network width, or as a building block for the CPA
  construction in §9.3.1 where a single neuron `v_0 (x + R)_+` covers the
  leftmost interval [−R, a_1].
- **Bach context.** Bach does not state this as a separate lemma; it is just
  the m = 1, b = 0 instance of (9.1).

## Prerequisites (Bach's dependency graph)

- [`single-hidden-relu`](./single-hidden-relu.md) — Single-hidden-layer ReLU neural network

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch09_NeuralNetworks/SingleHidden.lean`
- **Theorem/def name:** `singleHiddenReLU_with_zero_bias_one_neuron`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

