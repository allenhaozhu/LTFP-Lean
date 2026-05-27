# Dudley entropy integral bound for Rademacher complexity

**ID:** `dudley-entropy-bound`  
**Chapter:** Ch04 (Bach §4.5.6)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** in_lean_rademacher  
**Topic tags:** `Rademacher`

## Statement

_See textbook excerpt below or [`tasks/dudley-entropy-bound/`](../../../tasks/dudley-entropy-bound/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Dudley entropy integral bound for Rademacher complexity

**Concept ID:** `dudley-entropy-bound`
**Chapter:** Ch 4
**Section:** 4.5.6 (referenced via 4.4.4, "ε-net argument")
**Pages:** 89-91, 96 (also Wainwright 2019 reference)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
For a function class H equipped with the empirical L^2 metric (or an ambient metric on
which ‖·‖ controls the increments of the Rademacher process), the empirical Rademacher
complexity is bounded by the Dudley entropy integral:

$$\hat R_n(H) \le \frac{C}{\sqrt n} \int_0^{D} \sqrt{\log N(\varepsilon, H, \|\cdot\|_2)} \, d\varepsilon,$$

where N(ε, H, ‖·‖_2) is the covering number of H at radius ε and D is its diameter.

Bach motivates this via the ε-net argument: covering F by m(ε) = N(ε) functions and using
the bound on the supremum over a finite set; then optimizing over ε. He writes:

"if m(ε) ∼ ε^{−d}, ignoring constants, we need to upper-bound the quantity
ε + √(d log(1/ε) / n). The choice ε ∝ 1/√n leads to a rate proportional to √((d/n) log n),
which shows that the dependence in n is also close to 1/√n. Unfortunately, unless refined
computations of covering numbers or more advanced tools (such as 'chaining') are used,
this often leads to a nonoptimal dependence on dimension and/or number of observations
(see, e.g., Wainwright, 2019, for examples of these refinements)."

## Proof (verbatim)
Bach defers to Wainwright (2019) for the chaining argument that produces the Dudley
integral bound. In-chapter, he only proves the single-level ε-net version (4.4.4):

"Given a cover of F, for all f ∈ F, and with (f_i)_{i ∈ {1,…,m(ε)}} being the associated
cover elements, using that both R̂ and R are G-Lipschitz-continuous with respect to the
distance Δ, we have, for any i ∈ {1,…,m(ε)},
R̂(f) − R(f) ≤ R̂(f) − R̂(f_i) + R̂(f_i) − R(f_i) + R(f_i) − R(f)
            ≤ 2G · Δ(f, f_i) + sup_{j ∈ {1,…,m(ε)}} (R̂(f_j) − R(f_j)).

Taking the minimum with respect to i, and using the cover property, we get
R̂(f) − R(f) ≤ 2Gε + sup_{j} (R̂(f_j) − R(f_j)).

This implies, using section 4.4.3 that with probability greater than 1 − δ,
sup_{f∈F} (R̂(f) − R(f)) ≤ 2Gε + ℓ_∞ √(log(2m(ε))/(2n)) + (ℓ_∞/√(2n)) √log(1/δ)."

(Chaining replaces this single-scale ε with a geometric sequence and integrates, hence the Dudley form.)

## Notes
- In-book: ε-net (single-scale) bound only; full Dudley integral via chaining is deferred to
  Wainwright (2019).
- LTFP-Lean dudley-entropy-bound theorem aligns with the chaining statement, with constants
  abstracted into a covering-number signature.
- Two failure modes Bach flags: (a) "log(1/ε) inside the sqrt" gives suboptimal √log-n factor;
  (b) chaining is needed for sharp constants.

## Prerequisites (Bach's dependency graph)

- [`rademacher-complexity-def`](./rademacher-complexity-def.md) — Empirical and expected Rademacher complexity

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = in_lean_rademacher`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/Main.lean`
- **Theorem/def name:** `dudley_entropy_integral_bound`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

