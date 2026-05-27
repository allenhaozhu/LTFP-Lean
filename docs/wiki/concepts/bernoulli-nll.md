# Bernoulli negative log-likelihood (logistic loss in disguise)

**ID:** `bernoulli-nll`  
**Chapter:** Ch14 (Bach §14.1, p. 411)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/bernoulli-nll/`](../../../tasks/bernoulli-nll/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Bernoulli negative log-likelihood (logistic loss)

**Concept ID:** `bernoulli-nll`
**Chapter:** Ch 14
**Section:** §14.1.1 "Conditional Likelihoods"
**Pages:** 411 (book); PDF page 427
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement (verbatim)

Bach (p.411), opening of §14.1.1:

> For logistic regression where Y ∈ {−1, 1}, we can interpret the loss
> as the conditional log-likelihood of the model, where
>
>     P(yᵢ = 1 | xᵢ)  =  1 / (1 + exp(−fθ(xᵢ))),
>
> which can be put in a compact way as `p(yᵢ|xᵢ) = sigmoid(yᵢ fθ(xᵢ))`,
> where `sigmoid : α ↦ (1 + e^{−α})⁻¹` is the sigmoid function.

So the negative conditional log-likelihood is
`ℓ(y, fθ(x)) = log(1 + exp(−y · fθ(x)))` (the standard logistic loss).

For the y ∈ {0, 1} parameterization (the form the Lean target uses),
the Bernoulli NLL is

    bernoulliNLL p y  =  − y · log p  −  (1 − y) · log(1 − p),

equivalent to the {−1, 1} form after reparameterizing `p = sigmoid(z)`.

Bach (p.411, sidebar warning, also within §14.1.1):

> To apply logistic regression, there is no need to assume that the
> model is well specified; that is, there exists a θ* so that the data
> are actually generated from the conditional model above.

## Notes

- The Lean `bernoulliNLL` uses the (p, y) form with y ∈ {0, 1} and
  p ∈ [0, 1], the standard parameterization in Mathlib's probability
  library. Bach uses the equivalent y ∈ {−1, 1} sigmoid form.
- The "logistic loss in disguise" tag is exactly Bach's framing:
  logistic loss and Bernoulli NLL are the same object up to a
  change of variables `p = sigmoid(z)`.
- Bach uses this only to motivate the probabilistic interpretation of
  the logistic loss; he does not work out properties of the function
  (those are in chapter 4 on convex surrogates).

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

- [`bernoulli-at-half`](./bernoulli-at-half.md) — Bernoulli NLL at p = 1/2 = log 2
- [`bernoulli-nll-correct-zero`](./bernoulli-nll-correct-zero.md) — Bernoulli NLL at p=0, y=0 is 0

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch14_Probabilistic/LogLikelihood.lean`
- **Theorem/def name:** `bernoulliNLL`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

