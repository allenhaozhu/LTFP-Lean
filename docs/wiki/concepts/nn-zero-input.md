# NN on zero input = ∑ a · relu(b)

**ID:** `nn-zero-input`  
**Chapter:** Ch09 (Bach §9.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Neural-network`

## Statement

_See textbook excerpt below or [`tasks/nn-zero-input/`](../../../tasks/nn-zero-input/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — NN on zero input = Σ η_j · relu(b_j)

**Concept ID:** `nn-zero-input`
**Chapter:** Ch 9
**Section:** 9.2
**Pages:** 249 (book; PDF page 265)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Evaluating Bach's single-hidden-layer ReLU network (equation (9.1), p. 249) at
the input x = 0 collapses to a bias-only sum:

>     f(0) = Σ_{j=1}^m η_j σ(w_j^⊤ · 0 + b_j) = Σ_{j=1}^m η_j σ(b_j) = Σ_{j=1}^m η_j (b_j)_+.

For ReLU specifically, σ = (·)_+ = relu, so

>     f(0) = Σ_{j=1}^m η_j · relu(b_j).

## Proof (verbatim)

Direct substitution into equation (9.1):

    f(0) = Σ_j η_j σ(w_j^⊤ · 0 + b_j)
         = Σ_j η_j σ(0 + b_j)              [w_j^⊤ · 0 = 0 (linearity of inner product)]
         = Σ_j η_j σ(b_j)                  [0 + b_j = b_j]
         = Σ_j η_j (b_j)_+.                [σ = ReLU]

## Notes

- **Intermediate lemmas:** `w^⊤ · 0 = 0` (linearity of inner product in the
  second argument), and `0 + b = b`.
- **Technique in one line:** plug in x = 0 and use linearity of `⟨w, ·⟩` plus
  the additive identity.
- **Why this exists in the registry.** Boundary-value / sanity lemma that
  characterises the network's evaluation at the origin. Useful when separating
  "contribution from biases" from "contribution from input weights" — e.g., the
  CPA approximation argument in §9.3.1 (p. 256-257) considers a function
  satisfying f(−R) = 0, which is the analogue of imposing a constraint on the
  bias-only sum at a chosen reference input.
- **Bach context.** Bach does not isolate this; it is the x = 0 specialisation
  of (9.1).

## Prerequisites (Bach's dependency graph)

- [`single-hidden-relu`](./single-hidden-relu.md) — Single-hidden-layer ReLU neural network

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch09_NeuralNetworks/SingleHidden.lean`
- **Theorem/def name:** `singleHiddenReLU_zero_input`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

