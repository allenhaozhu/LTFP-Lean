# Gaussian negative log-likelihood (square loss + const)

**ID:** `gaussian-nll`  
**Chapter:** Ch14 (Bach §14.1, p. 409)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Gaussian`

## Statement

_See textbook excerpt below or [`tasks/gaussian-nll/`](../../../tasks/gaussian-nll/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Gaussian negative log-likelihood

**Concept ID:** `gaussian-nll`
**Chapter:** Ch 14
**Section:** §14.1.1 "Conditional Likelihoods"
**Pages:** 411 (book); PDF page 427
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement (verbatim)

Bach (p.411), within the discussion of "Conditional Likelihoods":

> For least-squares regression, we can interpret the loss
> `(1/2) (yᵢ − fθ(xᵢ))²` as a Gaussian model with mean `fθ(xᵢ)` and
> variance 1. We can also estimate a more general variance parameter
> that is uniform across all x (homoscedastic regression) or depends
> on x (heteroscedastic regression).

And in Exercise 14.1 (p.411, immediately below):

> **Exercise 14.1.** Show that the negative log density of the
> Gaussian distribution with mean μ and variance σ² (i.e.,
> `−log p(y|μ, σ) = (1/(2σ²)) (x − μ)² + (1/2) log(2π) + (1/2) log σ²`)
> is not convex in (μ, σ²) but is jointly convex in (μ/σ², σ⁻²).

## Notes

- For the σ = 1 case relevant to the registry, the Gaussian NLL
  reduces to `½ (y − μ)² + constants`. The Lean wrapper `gaussianNLL`
  drops the additive constants and keeps only the data-dependent
  `½ (y − μ)²` term, since constants don't affect minimization or
  comparison.
- Bach explicitly normalizes via `½ kyᵢ − fθ(xᵢ)k²` (i.e., the ½
  prefactor is part of the loss, not the model). This is consistent
  with the Lean `gaussianNLL (μ y : ℝ) := (y − μ)^2 / 2`.
- Bach flags (p.411 right under): "There is no need to have Gaussian
  noise! Having zero mean and bounded variance is enough for the
  analysis." So the Gaussian NLL is a *probabilistic interpretation*
  of square loss, not a hard modeling assumption.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

- [`gaussian-nll-eq-sqdisp`](./gaussian-nll-eq-sqdisp.md) — Gaussian NLL = (y - μ)² / 2 (definitional)
- [`gaussian-nll-le-iff-sq`](./gaussian-nll-le-iff-sq.md) — Gaussian NLL monotone in (y-μ)²
- [`gaussian-nll-self`](./gaussian-nll-self.md) — Gaussian NLL vanishes when prediction = truth
- [`gaussian-nll-sub-zero-nonneg`](./gaussian-nll-sub-zero-nonneg.md) — Gaussian NLL minus 0 is nonneg
- [`gaussian-nll-symm`](./gaussian-nll-symm.md) — Gaussian NLL symmetric in (μ, y)
- [`gaussian-nll-zero-disp`](./gaussian-nll-zero-disp.md) — Gaussian NLL at zero displacement = 0

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch14_Probabilistic/LogLikelihood.lean`
- **Theorem/def name:** `gaussianNLL`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

