# Empirical and expected Rademacher complexity

**ID:** `rademacher-complexity-def`  
**Chapter:** Ch04 (Bach §4.5, p. 91)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** in_lean_rademacher  
**Topic tags:** `Rademacher`

## Statement

_See textbook excerpt below or [`tasks/rademacher-complexity-def/`](../../../tasks/rademacher-complexity-def/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Empirical and expected Rademacher complexity

**Concept ID:** `rademacher-complexity-def`
**Chapter:** Ch 4
**Section:** 4.5
**Pages:** 91-94
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
We consider n i.i.d. random variables z_1, …, z_n ∈ Z, and a class H of functions from Z
to R. In our context, the space of functions is related to the learning problem as z = (x, y),
and H = {(x, y) ↦ ℓ(y, f(x)), f ∈ F}.

We denote the data D = {z_1, …, z_n}, and define the Rademacher complexity of the class
of functions H from Z to R as follows:

$$R_n(H) = \mathbb{E}_{\varepsilon,D}\Big[\sup_{h \in H} \frac{1}{n} \sum_{i=1}^n \varepsilon_i h(z_i)\Big], \qquad (4.12)$$

where ε ∈ R^n is a vector of independent Rademacher random variables (i.e., taking values
−1 or 1 with equal probability), which is also independent of D. It is a deterministic
quantity that depends only on n, H, and the common distribution of all z_i's.

Stated in words, the Rademacher complexity is equal to the expectation of the maximal
dot product between values of function h at the observations z_i and random labels.
It measures the "capacity" of the set of functions H.

**Empirical Rademacher complexity.** The Rademacher complexity R_n(H) defined in
equation (4.12) is a deterministic quantity that depends on the distribution of inputs.
An empirical version can be defined that does not take the expectation with respect to
the data; that is,

$$\hat R_n(H) = \mathbb{E}_\varepsilon\Big[\sup_{h \in H} \frac{1}{n} \sum_{i=1}^n \varepsilon_i h(z_i)\Big], \qquad (4.13)$$

which is now a random quantity that is computable from the training data and the class
of functions.

## Proof (verbatim)
(Definition — no proof.) Bach adds: "Be careful with the two notations R_n(H) (Rademacher
complexity) and R(f) (risk of the prediction function f), not to be confused with the
feature norm R often used with linear models."

## Notes
- ε_i are i.i.d. Rademacher (uniform on {−1,+1}), independent of the data D.
- Two flavors: expected R_n(H) (deterministic) and empirical R̂_n(H) (data-dependent).
- Properties listed in Exercise 4.9: monotone under H ⊂ H', additive on sums, |α|-homogeneous,
  invariant under adding a fixed function, and equal on convex hulls.
- Provides the central capacity-of-class quantity for the symmetrization argument in 4.5.1.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

- [`bounded-difference-rademacher`](./bounded-difference-rademacher.md) — Bounded-differences for the uniform deviation
- [`dudley-entropy-bound`](./dudley-entropy-bound.md) — Dudley entropy integral bound for Rademacher complexity
- [`symmetrization`](./symmetrization.md) — Symmetrization argument
- [`uniform-deviation-rademacher`](./uniform-deviation-rademacher.md) — E[uniform deviation] ≤ 2 · Rademacher complexity

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = in_lean_rademacher`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/Defs.lean`
- **Theorem/def name:** `empiricalRademacherComplexity`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

