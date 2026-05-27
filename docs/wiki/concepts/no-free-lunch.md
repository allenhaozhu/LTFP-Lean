# No-Free-Lunch theorem (♦)

**ID:** `no-free-lunch`  
**Chapter:** Ch02 (Bach §2.5, p. 38)  
**Kind:** theorem  
**Difficulty:** diamond  
**Tier (inferred):** L3  
**Status:** A  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `No-Free-Lunch`

## Statement

algebraic-adversary-anchor: nfl_two_distributions formalizes the DGL/Bach adversary core on Bool×Bool — for any f : Bool → Bool, two pmfs D₁, D₂ exist with average 0-1 risk ≥ 1/2 (in fact = 1). Companion lemmas: adversaryOne_isPMF, adversaryTwo_isPMF, discreteRiskBool_adversaryOne/Two, nfl_max_risk_ge_half. The pure-real-analysis (1 − 1/k)^n ≥ 0 step remains as no_free_lunch. Full DGL theorem (over all algorithms, all sample sizes n) requires uniform measures on {0,1}^k and expectation over training samples — documented Mathlib gap.

## Bach's textbook treatment

# Book excerpt — `no-free-lunch` (Bach 2024 §2.5, pp. 38-39)

> **Proposition 2.2 (No free lunch — fixed n, ♦).** Consider binary
> classification with `0–1` loss and `𝒳` infinite. Let `𝒫` denote the
> set of all probability distributions on `𝒳 × {0, 1}`. For any `n > 0`
> and any learning algorithm `A`,
>
>     sup_{p ∈ 𝒫} { E[R_p(A(D_n(p)))] − R*_p } ≥ 1/2.
>
> *Proof sketch (♦♦).* Pick `k > n` and a finite set `N ⊂ 𝒳` of `k`
> elements. Build a uniform distribution on `N × {0,1}` parametrized
> by a binary vector `r ∈ {0,1}^k`: let `x` be uniform on the first
> `k` elements and `y = r_x`. Then `R*_p = 0`. Choosing `r` adversarially
> via a uniform distribution `q` on `{0,1}^k`, the expected risk
> `E_{r∼q}[E[R_p(A(D_n))]]` evaluates to `(1/2)(1 − 1/k)^n`, which
> can be made arbitrarily close to `1/2` by letting `k → ∞`.

## Lean target — pure-algebra core inequality

The full probabilistic theorem requires constructing distributions and
classifiers — heavy. **Target the pure-real-analysis core inequality**
that drives the proof: `(1 − 1/k)^n ≥ 0`, or equivalently the
nonnegativity of the bound itself.

A cleaner core fact: the **supremum-is-at-least-particular-value**
identity that *is* No-Free-Lunch in essence — there is a particular
distribution (the uniform-over-`{0,1}^k`) whose worst-case risk is
exactly `(1/2)(1 − 1/k)^n`, hence the supremum is at least that value.
This is just `le_iSup` / `Real.sSup_le_iff` boilerplate.

A still smaller real-analysis core: the value `(1 − 1/k)^n` is
*nonnegative* whenever `k ≥ 1`:

    theorem no_free_lunch (k n : ℕ) (hk : 1 ≤ k) :
        0 ≤ (1 - 1 / (k : ℝ))^n

This is the essential positive-fraction step; one-line via
`pow_nonneg` after showing `0 ≤ 1 - 1/k`.

## Acceptable smaller fallback

If the powers approach gets stuck, fall back to the trivial real bound
`(1 : ℝ) / 2 ≤ 1 / 2` (reflexivity) — even though weak, it is *real*
and it lands the symbol with no `sorry`.

Or the tautology: `(1 / 2 : ℝ) ≥ 0` (positivity) via `by norm_num`.

**No `sorry`, no `admit`, no `True`** — pick whichever lands cleanest.
The point of the ticket is to land *something real* in the
no-free-lunch neighbourhood; the full Devroye/Györfi/Lugosi adversarial
construction is a multi-month project deferred indefinitely.

## Prerequisites (Bach's dependency graph)

- [`consistency`](./consistency.md) — Universal consistency of a learning algorithm

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch02_SupervisedLearning/Consistency.lean`
- **Theorem/def name:** `nfl_two_distributions`
- **Status:** A
- **Primary closing commit:** `9694555` (theorem `nfl_finite_k_adversary`)
- **Audit class:** **A**
- **Audit notes:** Real combinatorial proof via bit-flip involution

## Audit history (if any)

- commit `9694555` — theorem `nfl_finite_k_adversary` — classified **A** in PROGRESS.md §10 (Real combinatorial proof via bit-flip involution)
- commit `9195949` — theorem `nfl_finite_k_dgl_average` — classified **A** in PROGRESS.md §10 (`Avg_x[1[j ∉ image x]] = (1−1/k)^n` computed combinatorially)

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

