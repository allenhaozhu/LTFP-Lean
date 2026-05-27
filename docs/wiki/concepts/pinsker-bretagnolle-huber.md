# Pinsker / Bretagnolle–Huber inequality (algebraic core anchor)

**ID:** `pinsker-bretagnolle-huber`  
**Chapter:** Ch15 (Bach §15.1, p. 432)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** B  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Total-Variation`

## Statement

pinsker: mathlib-gap-tvDist — algebraic-anchor proof landed (1 - exp(-x) ≤ x via Real.add_one_le_exp); measure-theoretic Pinsker / Bretagnolle–Huber blocked on missing Mathlib `tvDist` / `Mathlib.Probability.Distance.Pinsker`.

## Bach's textbook treatment

# Bach textbook excerpt — Pinsker / Bretagnolle–Huber inequality (algebraic core anchor)

**Concept ID:** `pinsker-bretagnolle-huber`
**Chapter:** Ch 15
**Section:** §15.1.3 (Review of Information Theory) + §15.1.4 (Lower Bound on Hypothesis Testing)
**Pages:** 431-435 (book) / 447-451 (PDF)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

The carrier theorem `LTFP.Ch15_LowerBounds.Statistical.pinsker_inequality`
is the **algebraic core** that underlies the measure-theoretic
Bretagnolle–Huber bound used by Bach in §15.1.4. As a real-analysis fact:

> For every real `x`,
>
>     1 − exp(−x)  ≤  x.

When `x = KL(p‖q)` for two probability distributions `p, q` on a common
space, this is exactly the gap inequality on which Bach's information-
theoretic lower bound machinery rests; combined with the Cauchy–Schwarz
/ Hellinger-affinity step it yields the standard Bretagnolle–Huber form
`TV(p,q) ≤ √(1 − exp(−KL(p‖q)))` and, after a sharper convex analysis,
Pinsker `TV² ≤ KL/2`.

**Bach's textbook does NOT use the names "Pinsker" or "Bretagnolle–Huber".**
The chapter proves its statistical lower bounds via Fano's inequality
(Proposition 15.1, Corollary 15.1) using KL divergence directly; Pinsker
and BH are well-known re-expressions of the same KL-vs-TV trade-off from
the classical literature (Tsybakov, 2008, which Bach cites). Our project
imports the names from that classical literature; the *algebraic core
that drives the result* is what Bach uses implicitly.

## Proof (verbatim)

Bach does not state the algebraic core `1 − exp(−x) ≤ x` as a numbered
lemma — he uses the equivalent convex inequality `x + 1 ≤ exp x` (i.e.
`Real.add_one_le_exp` in Mathlib) silently throughout. The relevant
KL-divergence proof in §15.1.3 (p. 433):

> "The KL divergence is always nonnegative by convexity of the function
> `t ↦ t log t`, and equal to zero if and only if `p = q`. It is a
> classical dissimilarity measure for probability distributions that is
> jointly convex in `(p,q)`. Note that it can also be seen as a Bregman
> divergence (see section 11.1.3)."

And in §15.1.4 (p. 434, Corollary 15.1 / equation 15.8), Bach uses KL to
upper-bound mutual information and thence lower-bound Fano:

> "Corollary 15.1 (Fano's inequality for multiple hypothesis testing).
> Given M probability distributions `p_{θ_j}`, j = 1,...,M, on D,
> then
>
>     inf_h (1/M) ∑_{j=1}^M P_{θ_j}(h(D) ≠ j)
>       ≥ 1 − (1/(M² log M)) ∑_{j,j'=1}^M D_KL(p_{θ_j} ‖ p_{θ_j'})
>             − log 2 / log M.                               (15.8)"

In the proof, the convexity of the KL divergence is invoked:

> "Proof. We consider a joint random variable (y, D) distributed as y
> uniform in {1,...,M}, and, given y = j, D distributed from the
> distribution p_{θ_j}. We have, using the definition of the mutual
> information in equation (15.6) and the property in equation (15.7),
>
>     H(y|D) = H(y) − I(y, D)
>            = log M − (1/M) ∑_{j=1}^M D_KL(p_{θ_j} ‖ (1/M) ∑_{j'=1}^M p_{θ_j'})
>            ≥ log M − (1/M²) ∑_{j,j'=1}^M D_KL(p_{θ_j} ‖ p_{θ_j'})
>
> by the convexity of the KL divergence. We can then apply
> proposition 15.2 and get equation (15.8). □"

The algebraic core `1 − exp(−x) ≤ x` (the Lean carrier) is the convex
inequality dual to `add_one_le_exp`:

> `Real.add_one_le_exp(−x) : −x + 1 ≤ exp(−x)` ⇒ rearranged:
> `1 − exp(−x) ≤ x`.

## Notes

- **Naming gap (FLAG).** Bach (2024) does not use the names "Pinsker"
  or "Bretagnolle–Huber" in Ch 15. Our concept registry imports those
  names from Tsybakov (2008, *Introduction to Nonparametric
  Estimation*), which Bach explicitly cites (p. 438) as the standard
  reference for these inequalities. The Lean module docstring at
  `LTFP/Ch15_LowerBounds/Statistical.lean` lines 138-150 explicitly
  flags the "mathlib-gap-tvDist" obstacle: Mathlib provides `klDiv`
  but not `tvDist` between probability measures.
- **Equation-number map (FLAG):** the Lean docstring (line 221) cites
  "Bach (2024) Eq. (15.4)" but Eq. (15.4) is actually the
  `sup ≥ max` reduction — `1 − exp(−x) ≤ x` is the implicit convex
  step inside the proof of Corollary 15.1 (Eq. 15.8), not Eq. 15.4.
  This is a known project-internal labelling drift and should be
  documented in `docs/ERRATA.md` if not already.
- **Intermediate lemmas Bach uses:**
  - convexity of `t ↦ t log t` for KL nonnegativity (p. 433);
  - Jensen's inequality for the concave function `a : t ↦ −t log t`
    in the data-processing inequality proof (p. 433, lines following
    Prop 15.2);
  - convexity of KL divergence (in `q` argument) used in Cor 15.1
    proof.
- **Bach's technique in one line:** he never separates "Pinsker /
  Bretagnolle–Huber" from "KL convexity"; he uses KL directly inside
  Fano via convexity, achieving the same downstream bound. Our Lean
  anchor extracts the elementary inequality the cited classical proofs
  reduce to (`Real.add_one_le_exp`).
- **Algebraic anchor justification:** the measure-theoretic
  Bretagnolle–Huber form `TV² ≤ 1 − exp(−KL)` is *not* deducible from
  Bach Ch 15 alone — it requires the Hellinger-affinity /
  Cauchy–Schwarz bridge that lives in Mathlib only as a partial
  fragment (`klDiv` exists; `tvDist` and the BH bridge do not as of
  this writing). The algebraic core is the most we can land in Lean
  without committing to a `tvDist` definition.

## Prerequisites (Bach's dependency graph)

- [`infotheory-foundation`](./infotheory-foundation.md) — Information-theory foundation: KL divergence wrapper

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch15_LowerBounds/Statistical.lean`
- **Theorem/def name:** `pinsker_inequality`
- **Status:** B
- **Primary closing commit:** `0294264` (theorem `tvDist_le_sqrt_one_sub_exp_neg`)
- **Audit class:** **B**
- **Audit notes:** Takes abstract divergence `D` + BH bridge `tvDist² ≤ 1 − exp(−D)` as HYPOTHESES

## Audit history (if any)

- commit `0294264` — theorem `tvDist_le_sqrt_one_sub_exp_neg` — classified **B** in PROGRESS.md §10 (Takes abstract divergence `D` + BH bridge `tvDist² ≤ 1 − exp(−D)` as HYPOTHESES)
- commit `59a434d` — theorem `tvDist_sq_le_one_sub_exp_neg_of_bhattacharyya/hellinger` — classified **B** in PROGRESS.md §10 (Bhattacharyya affinity `ρ` and Hellinger squared `Hsq` passed as PARAMETERS; chain from KL to ρ is not discharged)

## Notes / open questions

- Carrier is **parametric** — at least one substantive hypothesis is passed through, not discharged.
- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

