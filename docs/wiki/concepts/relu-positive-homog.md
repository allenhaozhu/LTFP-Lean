# ReLU positive homogeneity: relu(c·z) = c·relu(z) for c ≥ 0

**ID:** `relu-positive-homog`  
**Chapter:** Ch09 (Bach §F6)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/relu-positive-homog/`](../../../tasks/relu-positive-homog/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — ReLU positive homogeneity

**Concept ID:** `relu-positive-homog`
**Chapter:** Ch 9
**Section:** 9.2.2 (Rectified Linear Units and Homogeneity)
**Pages:** 253 (book; PDF page 269)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

From section 9.2.2, p. 253 (verbatim):

> The main property that we will employ is its "positive homogeneity"; that is, for
> α > 0, (α u)_+ = α u_+.

In symbols, for all α ≥ 0 and all u ∈ R,

>     relu(α · u) = α · relu(u).

(Bach states α > 0; the α = 0 case is trivially 0 = 0 from `relu(0) = 0`.)

## Proof (verbatim)

Bach states the identity without proof — it is treated as elementary. The proof is
a one-line case split on the sign of u (using α ≥ 0):

- If u ≥ 0, then α u ≥ 0, so `(α u)_+ = α u = α · u_+`.
- If u < 0, then α u ≤ 0 (since α ≥ 0), so `(α u)_+ = 0 = α · 0 = α · u_+`.

## Notes

- **Intermediate lemmas:** none — direct from `max` algebra and `0 ≤ α`.
- **Technique in one line:** sign case split on u; both branches collapse to the
  same constant.
- **Why this matters in Bach.** Bach calls this *the* main property of ReLU and
  uses it twice in section 9.2.2 alone (p. 253):
  - To rescale individual neurons: η_j (w_j^⊤ x + b_j)_+ = (α_j η_j) ((w_j/α_j)^⊤ x + b_j/α_j)_+.
  - To normalize ‖w_j‖_2² + b_j²/R² = 1 at the cost of putting the ℓ_1 norm on η.
  This rescaling underpins both the estimation-error analysis (§9.2.3, leading to
  proposition 9.1) and the variation-norm formulation (§9.3.2, equation (9.4)).
- **Ambiguities for Lean formalization.** Hypothesis is `0 ≤ α` (Bach writes
  α > 0 but the α = 0 case is trivial; both versions appear in the literature).

## Prerequisites (Bach's dependency graph)

- [`neural-net-foundation`](./neural-net-foundation.md) — Neural-network foundation: ReLU activation

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/NeuralNet.lean`
- **Theorem/def name:** `relu_smul_nonneg`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

