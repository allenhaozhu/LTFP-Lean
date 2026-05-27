# E[uniform deviation] ≤ 2 · Rademacher complexity

**ID:** `uniform-deviation-rademacher`  
**Chapter:** Ch04 (Bach §4.5, p. 91)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** in_lean_rademacher  
**Topic tags:** `Rademacher`

## Statement

_See textbook excerpt below or [`tasks/uniform-deviation-rademacher/`](../../../tasks/uniform-deviation-rademacher/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — E[uniform deviation] ≤ 2 · Rademacher complexity

**Concept ID:** `uniform-deviation-rademacher`
**Chapter:** Ch 4
**Section:** 4.5 / 4.5.1 (Proposition 4.2)
**Pages:** 91-93
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
**Proposition 4.2 (Symmetrization)** — applied direction. Given the Rademacher complexity
of H defined in equation (4.12), the expected uniform deviation is bounded by twice the
Rademacher complexity:

$$\mathbb{E}\Big[\sup_{h\in H}\Big(\tfrac{1}{n}\sum_{i=1}^n h(z_i)-\mathbb{E}[h(z)]\Big)\Big]\le 2 R_n(H),$$
$$\mathbb{E}\Big[\sup_{h\in H}\Big(\mathbb{E}[h(z)]-\tfrac{1}{n}\sum_{i=1}^n h(z_i)\Big)\Big]\le 2 R_n(H).$$

For supervised learning with H = {(x,y) ↦ ℓ(y,f(x)), f ∈ F}, this controls
E[ sup_{f ∈ F} (R(f) − R̂(f)) ] ≤ 2 R_n(H).

## Proof (verbatim)
Same proof as `symmetrization`: introduce an independent copy D' = (z'_i), insert ε_i by
symmetry of h(z'_i) − h(z_i), then split into two identical Rademacher averages giving
the factor 2. Bach concludes: "Proposition 4.2 only bounds the expectation of the
deviation between the empirical average and the expectation by the Rademacher average.
Together with concentration inequalities from section 1.2, we can obtain high-probability
bounds, as done in section 4.4.1 with McDiarmid's inequality."

## Notes
- Two directions: empirical − population and population − empirical, both bounded by 2 R_n(H).
- Identical proof technique works in either direction (sign flip absorbed by symmetry of ε).
- This is the carrier theorem that turns capacity (R_n(H)) into uniform generalization control.
- Combined with bounded-differences + McDiarmid gives the tail bound for countable / separable
  hypothesis classes.

## Prerequisites (Bach's dependency graph)

- [`rademacher-complexity-def`](./rademacher-complexity-def.md) — Empirical and expected Rademacher complexity
- [`symmetrization`](./symmetrization.md) — Symmetrization argument

## Dependents (concepts that use this)

- [`rademacher-tail-bound-countable`](./rademacher-tail-bound-countable.md) — Tail bound on uniform deviation, countable hypothesis class

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = in_lean_rademacher`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/Main.lean`
- **Theorem/def name:** `uniform_deviation_expectation_le_two_smul_rademacher_complexity`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

