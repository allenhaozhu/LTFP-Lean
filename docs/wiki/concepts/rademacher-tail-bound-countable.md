# Tail bound on uniform deviation, countable hypothesis class

**ID:** `rademacher-tail-bound-countable`  
**Chapter:** Ch04 (Bach §4.5)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** in_lean_rademacher  
**Topic tags:** `Rademacher`

## Statement

_See textbook excerpt below or [`tasks/rademacher-tail-bound-countable/`](../../../tasks/rademacher-tail-bound-countable/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Tail bound on uniform deviation, countable hypothesis class

**Concept ID:** `rademacher-tail-bound-countable`
**Chapter:** Ch 4
**Section:** 4.5 (combines 4.4.1 + 4.5.1)
**Pages:** 86-87, 93-94
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
Combine bounded-differences (lemma above) and McDiarmid's inequality (section 1.2.2) with
symmetrization (Proposition 4.2). For any δ ∈ (0,1), with probability greater than 1 − δ:

$$H(z_1,\dots,z_n)-\mathbb{E}[H(z_1,\dots,z_n)]\le \tfrac{\ell_\infty}{\sqrt{2n}}\sqrt{\log(1/\delta)},$$

where H(z_1,…,z_n) = sup_{f ∈ F} (R(f) − R̂(f)). Since E[H] ≤ 2 R_n(H) by symmetrization,
with probability ≥ 1 − δ,

$$\sup_{f\in F}\big(R(f)-\hat R(f)\big)\le 2 R_n(H)+\tfrac{\ell_\infty}{\sqrt{2n}}\sqrt{\log(1/\delta)}.$$

By a union bound for the two symmetric tails, with probability ≥ 1 − δ,

$$\sup_{f\in F}\big|R(f)-\hat R(f)\big|\le 2 R_n(H)+\tfrac{\ell_\infty}{\sqrt{2n}}\sqrt{\log(2/\delta)}.$$

## Proof (verbatim)
"Such control can be extended beyond a single function f. When changing a single z_i ∈ X×Y
into z'_i ∈ X×Y, the deviation in H is almost surely at most (1/n) ℓ_∞. Thus, applying
McDiarmid's inequality (see section 1.2.2), with probability greater than 1 − δ, we have
H(z_1,…,z_n) − E[H(z_1,…,z_n)] ≤ (ℓ_∞/√(2n)) √log(1/δ).

We thus only need to bound the expectation of sup_{f ∈ F} (R(f) − R̂(f)) and of the similar
quantity sup_{f ∈ F} (R̂(f) − R(f)) (which will typically have the same bound), and add on
top of it (ℓ_∞/√(2n)) √log(2/δ), to ensure a high-probability bound."
(Bach also notes in fn. 7 that the union bound replaces 1/δ by 2/δ when combining two probability bounds.)

## Notes
- "Countable" really means: a class where uniform deviation is a measurable function of the
  data (and where the supremum-of-expectation step in symmetrization is valid). McDiarmid +
  bounded differences gives the tail.
- Cleaner statement obtained from Proposition 4.2 + McDiarmid.
- Constants: leading factor 2 in 2 R_n(H), tail factor ℓ_∞/√(2n) √log(2/δ).

## Prerequisites (Bach's dependency graph)

- [`bounded-difference-rademacher`](./bounded-difference-rademacher.md) — Bounded-differences for the uniform deviation
- [`mcdiarmid-inequality`](./mcdiarmid-inequality.md) — McDiarmid's bounded-differences inequality
- [`uniform-deviation-rademacher`](./uniform-deviation-rademacher.md) — E[uniform deviation] ≤ 2 · Rademacher complexity

## Dependents (concepts that use this)

- [`rademacher-tail-bound-separable`](./rademacher-tail-bound-separable.md) — Tail bound on uniform deviation, separable hypothesis class

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = in_lean_rademacher`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/Main.lean`
- **Theorem/def name:** `uniform_deviation_tail_bound_countable`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

