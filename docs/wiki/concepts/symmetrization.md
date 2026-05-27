# Symmetrization argument

**ID:** `symmetrization`  
**Chapter:** Ch04 (Bach §4.5.1, p. 92)  
**Kind:** lemma  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** in_lean_rademacher  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/symmetrization/`](../../../tasks/symmetrization/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Symmetrization argument

**Concept ID:** `symmetrization`
**Chapter:** Ch 4
**Section:** 4.5.1
**Pages:** 92-93
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
**Proposition 4.2 (Symmetrization).** Given the Rademacher complexity of H defined
in equation (4.12), we have

$$\mathbb{E}\Big[\sup_{h\in H} \tfrac{1}{n}\sum_{i=1}^n h(z_i)-\mathbb{E}[h(z)]\Big] \le 2 R_n(H), \quad
  \mathbb{E}\Big[\sup_{h\in H} \mathbb{E}[h(z)]-\tfrac{1}{n}\sum_{i=1}^n h(z_i)\Big] \le 2 R_n(H).$$

## Proof (verbatim)
Let D' = {z'_1, …, z'_n} be an independent copy of the data D = {z_1, …, z_n}.
Let (ε_i)_{i ∈ {1,…,n}} be i.i.d. Rademacher random variables, which are also independent of
D and D'. Using that for all i in {1, …, n}, E[h(z'_i)|D] = E[h(z)] and E[h(z_i)|D] = h(z_i),
we have

$$\mathbb{E}\sup_{h\in H}\Big[\mathbb{E}[h(z)] - \tfrac{1}{n}\sum_i h(z_i)\Big] = \mathbb{E}\sup_{h\in H}\tfrac{1}{n}\sum_i \mathbb{E}\big[h(z'_i)-h(z_i)\big| D\big],$$

by definition of the independent copy D'. Then

$$\mathbb{E}\sup_{h\in H}\Big[\mathbb{E}[h(z)] - \tfrac{1}{n}\sum_i h(z_i)\Big] \le \mathbb{E}\Big[\mathbb{E}\sup_{h\in H}\tfrac{1}{n}\sum_i (h(z'_i)-h(z_i))\,\big|\, D\Big],$$

using that the supremum of the expectation is less than the expectation of the supremum.
Thus, by the towering law of expectation, we get

$$\mathbb{E}\sup_{h\in H}\Big[\mathbb{E}[h(z)] - \tfrac{1}{n}\sum_i h(z_i)\Big] \le \mathbb{E}\sup_{h\in H}\tfrac{1}{n}\sum_i (h(z'_i)-h(z_i)).$$

We can now use the symmetry of the laws of ε_i and h(z'_i) − h(z_i), to get

$$\mathbb{E}\sup_{h\in H}\Big[\mathbb{E}[h(z)] - \tfrac{1}{n}\sum_i h(z_i)\Big] \le \mathbb{E}\sup_{h\in H}\tfrac{1}{n}\sum_i \varepsilon_i\,(h(z'_i)-h(z_i))$$
$$\le \mathbb{E}\sup_{h\in H}\tfrac{1}{n}\sum_i \varepsilon_i h(z_i) + \mathbb{E}\sup_{h\in H}\tfrac{1}{n}\sum_i \varepsilon_i\,(-h(z_i)) = 2\,\mathbb{E}\sup_{h\in H}\tfrac{1}{n}\sum_i \varepsilon_i h(z_i) = 2 R_n(H).$$

The reasoning is identical for E sup_h ( (1/n) Σ h(z_i) − E[h(z)] ) ≤ 2 R_n(H). □

## Notes
- The proof relies on an independent ghost-sample D' = (z'_1,…,z'_n).
- Sub-step uses ε_i (h(z'_i) − h(z_i)) ≝ h(z'_i) − h(z_i) in distribution (symmetry).
- After expanding, splits into two identical Rademacher terms, yielding the factor 2.
- Together with concentration inequalities (McDiarmid), gives high-probability bounds.

## Prerequisites (Bach's dependency graph)

- [`rademacher-complexity-def`](./rademacher-complexity-def.md) — Empirical and expected Rademacher complexity

## Dependents (concepts that use this)

- [`uniform-deviation-rademacher`](./uniform-deviation-rademacher.md) — E[uniform deviation] ≤ 2 · Rademacher complexity

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = in_lean_rademacher`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/Symmetrization.lean`
- **Theorem/def name:** `abs_symmetrization_equation`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

