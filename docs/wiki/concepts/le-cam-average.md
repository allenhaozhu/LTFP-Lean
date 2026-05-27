# Le Cam-style average ≤ max two-point inequality

**ID:** `le-cam-average`  
**Chapter:** Ch15 (Bach §15.1.4, p. 434)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** `Le Cam`

## Statement

_See textbook excerpt below or [`tasks/le-cam-average/`](../../../tasks/le-cam-average/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Le Cam-style average ≤ max two-point inequality

**Concept ID:** `le-cam-average`
**Chapter:** Ch 15
**Section:** §15.1.2 (Eq. 15.4-15.5) + §15.1.4 (Cor 15.1)
**Pages:** 430-434 (book) / 446-450 (PDF)
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

The carrier `LTFP.Ch15_LowerBounds.Statistical.leCam_average_le_max` is
the **average ≤ max** algebraic anchor that Bach uses (implicitly) in
two places: (i) Eq. 15.4 — passing from `sup` over Θ down to a finite
collection of distinguished points; (ii) Eq. 15.5 — passing from
`max_j` to `(1/M) ∑_j` of the per-hypothesis error, which is the form
required to apply Fano (Cor 15.1 / Eq. 15.8).

> For real risks `R₁, R₂`,
>
>     (R₁ + R₂)/2  ≤  max(R₁, R₂).

The classical "Le Cam two-point method" (Tsybakov 2008, §2.3) is named
after Lucien Le Cam, but Bach does NOT use the name "Le Cam" anywhere
in Ch 15. He uses the inequality silently in the chain (Eq. 15.5):

> `max_j P_{θ_j}(h(D) ≠ j) ≥ (1/M) ∑_j P_{θ_j}(h(D) ≠ j)`.

## Proof (verbatim)

Bach §15.1.2 (p. 430), the conclusion of the reduction:

> "P_{θ_j}( δ(θ_j, A(D))² ≥ A ) ≥ P_{θ_j}( g(A(D)) ≠ j ),
>
> which leads to, using equations (15.2) and (15.4),
>
>     inf_A sup_{θ* ∈ Θ} E_{θ*}[ δ(θ*, A(D))² ]
>       ≥ A · inf_h max_{j ∈ {1,…,M}} P_{θ_j}( h(D) ≠ j )
>       ≥ A · inf_h (1/M) ∑_{j=1}^M P_{θ_j}( h(D) ≠ j ),         (15.5)
>
> where h is any (measurable) function from the data D to {1,…,M}. We
> have thus lower-bounded the minimax statistical error by the minimax
> error of a hypothesis test h, which is a function that takes the data
> D to a value in {1,…,M}."

The step `max ≥ avg` is the **only** algebraic step on the second
line of Eq. (15.5). Bach does not name it, but it is the carrier our
Lean anchor formalizes.

## Notes

- **Naming map (FLAG):** project-internal "Le Cam" name is from
  Tsybakov (2008, §2). Bach Ch 15 uses Fano (Prop 15.1, 15.2,
  Cor 15.1) directly with the `max ≥ avg` step left implicit. We split
  it out as a named anchor because downstream concepts
  (`average-le-sup-anchor`, `three-point-average-le-max`,
  `min-le-avg-le-max`, etc.) cite it.
- **Bach's technique in one line:** `(R₁+R₂)/2 ≤ max(R₁,R₂)` is
  trivial; the *content* is using it as the bridge between the
  worst-case bound (Eq. 15.4) and the Fano-amenable average bound
  (Cor 15.1).
- **Equation alignment:** Eq. (15.5) is the carrier Bach equation; our
  Lean target captures only the algebraic last step of that derivation.
- The matching M-point statement (for arbitrary M, not just M = 2) is
  used in the proof of Cor 15.1 and in the volume / Varshamov–Gilbert
  packing arguments (Lemmas 15.1, 15.2 on p. 435-436).

## Prerequisites (Bach's dependency graph)

- [`two-point-sup-lb`](./two-point-sup-lb.md) — Two-point lower-bound template (sup ≥ min)

## Dependents (concepts that use this)

- [`average-le-sup-anchor`](./average-le-sup-anchor.md) — Average ≤ sup minimax anchor (alias of leCam)
- [`average-of-self`](./average-of-self.md) — Average of identical risks = the risk
- [`average-plus-half-le`](./average-plus-half-le.md) — (R₁+R₂)/2 + R₃/2 ≤ max(R₁,R₂) + R₃/2
- [`max-eq-avg-equal`](./max-eq-avg-equal.md) — max R R = average R R
- [`min-le-average`](./min-le-average.md) — Min ≤ average for two-point risks
- [`min-le-avg-le-max`](./min-le-avg-le-max.md) — Min ≤ average ≤ max sandwich
- [`three-point-average-le-max`](./three-point-average-le-max.md) — Three-point Le Cam: average ≤ max

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch15_LowerBounds/Statistical.lean`
- **Theorem/def name:** `leCam_average_le_max`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

