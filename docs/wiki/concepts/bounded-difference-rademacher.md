# Bounded-differences for the uniform deviation

**ID:** `bounded-difference-rademacher`  
**Chapter:** Ch04 (Bach §4.5)  
**Kind:** lemma  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** in_lean_rademacher  
**Topic tags:** `Rademacher`

## Statement

_See textbook excerpt below or [`tasks/bounded-difference-rademacher/`](../../../tasks/bounded-difference-rademacher/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Bounded-differences for the uniform deviation

**Concept ID:** `bounded-difference-rademacher`
**Chapter:** Ch 4
**Section:** 4.5 (uses 4.4.1)
**Pages:** 86-87, 93-94
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
Let H(z_1, …, z_n) = sup_{f ∈ F} (R(f) − R̂(f)), where the z_i = (x_i, y_i) are i.i.d.
and R̂(f) = (1/n) Σ_i ℓ(y_i, f(x_i)). Assume the loss functions for all (x,y) in the support
and f ∈ F are between 0 and some ℓ_∞.

"When changing a single z_i ∈ X × Y into z'_i ∈ X × Y, the deviation in H is almost surely
at most (1/n) ℓ_∞."

Symbolically, for any i and any z_1,…,z_n, z'_i:
$$|H(z_1,\dots,z_i,\dots,z_n) - H(z_1,\dots,z'_i,\dots,z_n)| \le \frac{\ell_\infty}{n}.$$

## Proof (verbatim)
"For a fixed function f ∈ F, only one term in the average is changed, with value in [0, ℓ_∞],
and thus a deviation of at most (1/n) ℓ_∞. This can be extended to the supremum by a simple
computation left as an exercise." (Footnote 6, p. 87.)

(Sketch.) Fix f ∈ F. The empirical average (1/n) Σ ℓ(y_i, f(x_i)) is changed by at most
(1/n)·(ℓ_∞ − 0) = ℓ_∞/n when one observation is swapped. Therefore R(f) − R̂(f) changes
by at most ℓ_∞/n. Taking the supremum over f ∈ F preserves the bound:
| sup_f g_1(f) − sup_f g_2(f) | ≤ sup_f |g_1(f) − g_2(f)| ≤ ℓ_∞/n.

This is exactly the bounded-differences hypothesis required by McDiarmid's inequality
(see 1.2.2), giving: with probability ≥ 1 − δ,
$$H(z_1,\dots,z_n) - \mathbb{E}[H(z_1,\dots,z_n)] \le \tfrac{\ell_\infty}{\sqrt{2n}}\sqrt{\log(1/\delta)}.$$

## Notes
- This is the bounded-differences "Lipschitz" hypothesis needed to invoke McDiarmid.
- Bach proves it for ℓ-bounded loss; standard step on the way from expectation bound to tail bound.
- Together with symmetrization (Prop. 4.2) gives the high-probability uniform-deviation bound.
- Exercise hint: sup is 1-Lipschitz in sup-norm; replacing one entry changes each f-summand
  by ≤ ℓ_∞/n, hence the same for sup_f.

## Prerequisites (Bach's dependency graph)

- [`rademacher-complexity-def`](./rademacher-complexity-def.md) — Empirical and expected Rademacher complexity

## Dependents (concepts that use this)

- [`rademacher-tail-bound-countable`](./rademacher-tail-bound-countable.md) — Tail bound on uniform deviation, countable hypothesis class

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = in_lean_rademacher`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/BoundedDifference.lean`
- **Theorem/def name:** `uniformDeviation_bounded_difference`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

