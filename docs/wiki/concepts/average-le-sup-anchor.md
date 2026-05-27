# Average ≤ sup minimax anchor (alias of leCam)

**ID:** `average-le-sup-anchor`  
**Chapter:** Ch15 (Bach §15.1.4)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Le Cam`, `Lower-bound`

## Statement

_See textbook excerpt below or [`tasks/average-le-sup-anchor/`](../../../tasks/average-le-sup-anchor/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Average ≤ sup minimax anchor (alias of leCam)

**Concept ID:** `average-le-sup-anchor`
**Chapter:** Ch 15
**Section:** §15.1.4 (Lower Bound on Hypothesis Testing Based on Information Theory)
**Pages:** 434 (book) / 450 (PDF)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Carrier `LTFP.Ch15_LowerBounds.Statistical.average_le_sup`. Alias /
re-export of the `(R₁ + R₂)/2 ≤ max(R₁, R₂)` step extracted from Bach's
Eq. 15.5 chain, also covered by `le-cam-average`. Provided as a named
anchor downstream of the Bayesian / "average risk" lower-bound
construction (§15.1.6).

> For real risks `R₁, R₂`,
>
>     (R₁ + R₂)/2  ≤  max(R₁, R₂)  =  sup{R₁, R₂}.

## Proof (verbatim)

Bach §15.1.6 (p. 438), Bayesian-style lower bound:

> "We can use a Bayesian analysis as outlined for least-squares
> regression in section 3.7. We consider a particular probability
> distribution q(θ*) on parameters θ*, whose support is included in Θ.
> Then we have, since the supremum is greater than the expectation,
>
>     inf_A sup_{θ* ∈ Θ} E_{θ*}[ δ(θ*, A(D))² ]
>       ≥ inf_A E_{q(θ*)}[ E_{θ*}[ δ(θ*, A(D))² ] ].
>
> This reasoning is particularly simple when the optimal algorithm A is
> easy to estimate (with no need for a packing argument)."

The carrier inequality "expectation ≤ supremum" is, in the finite
two-point case (q uniform on `{R₁, R₂}`), exactly `(R₁+R₂)/2 ≤ max(R₁,R₂)`.

## Notes

- **Bach's technique in one line:** `E_q[X] ≤ sup_{ω} X(ω)` always
  holds — applying it to a uniform two-point prior gives the named
  Lean alias.
- This anchor is provided as a *different name* for the same algebraic
  fact captured by `le-cam-average`; downstream registry users pick
  the alias that matches their context (Le Cam vs Bayesian narrative).
- Bach uses this inequality in both §15.1.2 (Eq. 15.5, frequentist
  reduction) and §15.1.6 (Bayesian reduction); the algebraic content
  is identical.

## Prerequisites (Bach's dependency graph)

- [`le-cam-average`](./le-cam-average.md) — Le Cam-style average ≤ max two-point inequality

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch15_LowerBounds/Statistical.lean`
- **Theorem/def name:** `average_le_sup`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

