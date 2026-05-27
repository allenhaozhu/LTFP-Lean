# Single-hidden ReLU NN is linear in output weights

**ID:** `single-hidden-relu-add-a`  
**Chapter:** Ch09 (Bach §9.3, p. 257)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Neural-network`

## Statement

_See textbook excerpt below or [`tasks/single-hidden-relu-add-a/`](../../../tasks/single-hidden-relu-add-a/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Single-hidden ReLU NN is linear in output weights

**Concept ID:** `single-hidden-relu-add-a`
**Chapter:** Ch 9
**Section:** 9.3, 9.3.2
**Pages:** 257-258 (book; PDF pages 273-274)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

A single-hidden-layer ReLU network with **fixed** input weights (w_j, b_j) is **linear
in the output weights η = (η_1, ..., η_m)**:

>     f_η(x) = Σ_{j=1}^m η_j (w_j^⊤ x + b_j)_+ = ⟨η, φ(x)⟩,
>
> where φ(x)_j = (w_j^⊤ x + b_j)_+ depends only on the (fixed) input weights and on x.

This is the structural observation Bach uses repeatedly in §§9.2.3 (estimation error
via Rademacher complexity), 9.3.2 (variation-norm reformulation through measures), and
9.3.6 (Frank-Wolfe representation with a finite number of neurons).

Direct quotation, p. 250:

> If the input weights are fixed, we obtain a linear model with the m hidden neurons as
> features.

And from §9.3.2 (p. 257-258), the integral form that *defines* the variation norm:

> We can write a neural network with finitely many neurons f(x) = Σ_{j=1}^m η_j(w_j^⊤ x + b_j)_+
> as the integral
>
>     f(x) = ∫_K (w^⊤ x + b)_+ dν(w, b),                     (9.4)
>
> for ν being the signed measure ν = Σ_{j=1}^m η_j δ_(w_j, b_j), where δ_(w_j, b_j) is the
> Dirac measure at (w_j, b_j). Then the penalty can be written as
> ‖η‖_1 = ∫_K |dν(w, b)|, which is the total variation of ν.

The "linear in η" structure is exactly what lets the signed measure ν enter linearly.

## Proof (verbatim)

This is again a **direct algebraic identity**, not a theorem to be derived. The proof
is the one-line distributivity argument:

    f_{α η + β η'}(x) = Σ_j (α η_j + β η'_j)(w_j^⊤ x + b_j)_+
                     = α Σ_j η_j (w_j^⊤ x + b_j)_+ + β Σ_j η'_j (w_j^⊤ x + b_j)_+
                     = α f_η(x) + β f_{η'}(x).

In particular, *additivity in η* (the precise name of this concept in the registry —
"add-a" = additivity in the output weight a, with Bach's η):

    f_{η + η'}(x) = f_η(x) + f_{η'}(x).

This is just the additivity of the finite sum and of scalar multiplication.

## Notes

- **Intermediate lemmas (trivial):**
  - Additivity of finite sums: Σ (a + b) = Σ a + Σ b.
  - The atomic neuron (w_j^⊤ x + b_j)_+ is **fixed** when we vary η, so it factors
    out as the j-th feature.
- **Technique in one line:** finite sum is linear in its coefficients.
- **Why this matters in Bach's exposition.** This trivial observation is load-bearing:
  - §9.2.3 estimation error: lets the supremum over ‖η‖_1 ≤ D collapse to the linear
    dual sup ‖z‖_∞ via Hölder, after which only the input-weight side carries
    Rademacher dependence.
  - §9.3.2 variation norm: the linear-in-η structure is precisely what allows the
    network to be re-expressed as an integral against a signed measure ν =
    Σ η_j δ_(w_j, b_j), and the ℓ_1 norm of η as the total variation of ν.
  - §9.3.6 Frank-Wolfe: convex hull of single-neuron functions s·γ_1(g)·(w^⊤ · + b)_+
    (s ∈ {−1, +1}) — only possible because η enters linearly.
- **Ambiguities for Lean formalization.**
  - For ReLU specifically, *linearity of f_η in η* is preserved even though ReLU is not
    linear (because ReLU is applied to the input side, BEFORE multiplication by η).
    A Lean statement should be careful: `f (η + η') x = f η x + f η' x` is true; but
    `f η (x + x') = f η x + f η x'` is FALSE for ReLU.
  - "Linear in η" in Bach's wording means R-linear as a map η ↦ f_η in the function
    space `X → R`, holding (w_j, b_j) fixed.

## Prerequisites (Bach's dependency graph)

- [`single-hidden-relu`](./single-hidden-relu.md) — Single-hidden-layer ReLU neural network

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch09_NeuralNetworks/SingleHidden.lean`
- **Theorem/def name:** `singleHiddenReLU_add_a`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

