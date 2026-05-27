# Single-hidden-layer ReLU neural network

**ID:** `single-hidden-relu`  
**Chapter:** Ch09 (Bach §9.2, p. 249)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Neural-network`

## Statement

_See textbook excerpt below or [`tasks/single-hidden-relu/`](../../../tasks/single-hidden-relu/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Single-hidden-layer ReLU neural network

**Concept ID:** `single-hidden-relu`
**Chapter:** Ch 9
**Section:** 9.2
**Pages:** 249-250 (book; PDF pages 265-266)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

From section 9.2, *Single Hidden-Layer Neural Network* (p. 249):

> We consider X = R^d and the set of prediction functions that can be written as
>
>     f(x) = Σ_{j=1}^m η_j σ(w_j^⊤ x + b_j),                       (9.1)
>
> where w_j ∈ R^d, b_j ∈ R, j = 1, ..., m are the input weights, η_j ∈ R, j = 1, ..., m,
> are the output weights, and σ is an activation function.

ReLU specialization (from the same section, p. 249):

> The activation function is typically chosen from one of the following examples [...]:
> [...]
> • **Rectified linear unit (ReLU)** σ(u) = (u)_+ = max{u, 0}, which will be the main
>   focus of this chapter.

## Proof (verbatim)

This concept is a **definition**, not a theorem; there is nothing to prove. The defining
equation is (9.1) above.

Bach attaches a structural remark immediately after the definition (p. 250):

> Function f is defined as the linear combination of m functions x ↦ σ(w_j^⊤ x + b_j),
> which are the hidden neurons. If the input weights are fixed, we obtain a linear model
> with the m hidden neurons as features. A key benefit of neural networks is that they
> perform feature learning by optimizing with respect to input weights.

And a naming caveat:

> The constant terms b_j are sometimes referred to as "biases," which is unfortunate in
> a statistical context, as that word already has a precise meaning within the
> bias/variance trade-off (see chapter 3 and section 7.3).

## Notes

- **Intermediate components in the definition:**
  - Activation σ : R → R, here specialized to ReLU σ(u) = max(u, 0) = (u)_+.
  - Affine pre-activations a_j(x) = w_j^⊤ x + b_j with input weight w_j ∈ R^d and bias
    (intercept) b_j ∈ R.
  - Output / mixing coefficients η_j ∈ R.
  - Width m ∈ ℕ (number of hidden neurons).
- **Technique in one line:** finite linear combination of ReLU-of-affine atoms.
- **Domain conventions for the rest of Ch 9.** Bach assumes input data are bounded:
  ‖x‖_2 ≤ R almost surely (p. 253). For the *theoretical* analysis (estimation +
  approximation), input weights are normalized to ‖w_j‖_2² + b_j²/R² = 1, and the
  output weights are constrained by ‖η‖_1 ≤ D (p. 253). The compact constraint set is
  K = { (w, b/R) : ‖w‖_2 = 1, |b| ≤ R } (p. 258, 259).
- **Ambiguities for Lean formalization.**
  - The definition is parameterised by σ; for downstream ReLU-specific theorems (e.g.,
    `single-hidden-relu-add-a`, `nn-zero-input`, `relu-positive-homog`), σ should be
    locked to the ReLU. A `Function` field with a separate hypothesis `IsReLU σ` is
    cleaner than baking σ = max(·, 0) into the type.
  - Bach uses η_j ∈ R; multi-output extension (η_j ∈ R^k, section 13.1) is OUT OF SCOPE
    for chapter 9.
  - The width m may be any natural; in some sub-sections (9.2.3 onward) it is treated
    as fixed; in section 9.3 it is implicitly allowed to grow / tend to infinity.

## Prerequisites (Bach's dependency graph)

- [`neural-net-foundation`](./neural-net-foundation.md) — Neural-network foundation: ReLU activation

## Dependents (concepts that use this)

- [`nn-zero-a`](./nn-zero-a.md) — NN with zero output weights = 0
- [`nn-zero-bias-one-neuron`](./nn-zero-bias-one-neuron.md) — NN with zero bias, 1 neuron
- [`nn-zero-input`](./nn-zero-input.md) — NN on zero input = ∑ a · relu(b)
- [`single-hidden-relu-add-a`](./single-hidden-relu-add-a.md) — Single-hidden ReLU NN is linear in output weights
- [`universal-approximation`](./universal-approximation.md) — Universal approximation theorem (Cybenko/Hornik) (♦)

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch09_NeuralNetworks/SingleHidden.lean`
- **Theorem/def name:** `singleHiddenReLU`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

