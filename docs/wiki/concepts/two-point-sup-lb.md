# Two-point lower-bound template (sup ≥ min)

**ID:** `two-point-sup-lb`  
**Chapter:** Ch15 (Bach §15.1.4, p. 434)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/two-point-sup-lb/`](../../../tasks/two-point-sup-lb/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Two-point lower-bound template (sup ≥ min)

**Concept ID:** `two-point-sup-lb`
**Chapter:** Ch 15
**Section:** §15.1.2 (Reduction to a Hypothesis Test)
**Pages:** 429-431 (book) / 445-447 (PDF)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

The carrier theorem `LTFP.Ch15_LowerBounds.Statistical.twoPoint_sup_lower_bound`
is the **two-point specialization** of Bach's "reduction to a hypothesis
test" step (Eq. 15.4): selecting M = 2 distinguished points `θ₁, θ₂` in
the parameter set Θ, the supremum of testing error over Θ is bounded
below by the maximum over those two points (which in turn is ≥ their
average, ≥ their minimum). Project-internal name "two-point" matches
the classical Le Cam two-point method (Tsybakov, 2008, §2.3) which Bach
cites but does not spell out as a separate lemma.

> For real risks `R₁, R₂ ≥ 0`,
>
>     sup{R₁, R₂}  =  max(R₁, R₂)  ≥  (R₁ + R₂)/2.

## Proof (verbatim)

Bach §15.1.2 (p. 429-430), proving Eq. (15.4):

> "We consider θ₁, …, θ_M ∈ Θ such that
>
>     ∀ i ≠ j,  δ(θ_i, θ_j)² ≥ 4A,                              (15.3)
>
> and transform the estimation problem into a hypothesis test; that is,
> an algorithm going from data D to one of M potential outcomes (see
> the following illustration in two dimensions with the Euclidean
> geometry).
>
> Then, because we take the supremum over a smaller set,
>
>     sup_{θ* ∈ Θ} P_{θ*}( δ(θ*, A(D))² ≥ A )
>       ≥ max_{j ∈ {1,…,M}} P_{θ_j}( δ(θ_j, A(D))² ≥ A ).      (15.4)"

The two-point case is M = 2 in the above; the maximum of two terms
trivially upper-bounds their average, `max(R₁, R₂) ≥ (R₁ + R₂)/2` (used
implicitly by Bach throughout §15.1.4 when forming the
`(1/M) ∑ D_KL` average in Cor 15.1).

## Notes

- **Naming map (FLAG):** Bach does not use the term "two-point method"
  in Ch 15. Our registry imports the standard Tsybakov (2008) name. The
  Lean carrier captures only the *algebraic* `max ≥ avg` step (M = 2
  case of Eq. 15.4); the full Le Cam two-point recipe (find `θ₁, θ₂`
  with `δ(θ₁,θ₂)² ≥ 4A` and small KL, then apply Pinsker / BH) is
  decomposed across `two-point-sup-lb`, `le-cam-average`, and
  `pinsker-bretagnolle-huber` in our registry.
- **Bach's technique in one line:** the supremum over Θ majorizes the
  supremum over a finite subset, and `max ≥ avg` is the immediate
  algebraic consequence used inside Fano (Eq. 15.5).
- **Intermediate lemmas Bach uses:** triangle inequality for δ
  (p. 430), packing condition (Eq. 15.3), Markov's inequality
  (p. 429, for the bridge from squared distance to probability of
  error).
- This is one of the foundational "algebraic anchors" of §15.1; the
  Lean proof is `by linarith` from `R₁, R₂ ≥ 0` and is essentially a
  definitional unfolding of `max`.

## Prerequisites (Bach's dependency graph)

- [`testing-error-nonneg`](./testing-error-nonneg.md) — Statistical lower-bound anchor: testing error nonneg

## Dependents (concepts that use this)

- [`le-cam-average`](./le-cam-average.md) — Le Cam-style average ≤ max two-point inequality

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch15_LowerBounds/Statistical.lean`
- **Theorem/def name:** `twoPoint_sup_lower_bound`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

