# McAllester PAC-Bayes bound (algebraic core anchor)

**ID:** `pac-bayes-mcallester`  
**Chapter:** Ch14 (Bach §14.4, p. 425)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** B  
**Mathlib status:** partial  
**Vendored status:** new  
**Topic tags:** `PAC-Bayes`

## Statement

Real / algebraic core proved (descent-ratio nonneg, canonical η=1/L collapse, quadratic instance with equality); abstract `LipschitzWith L (gradient f) ⇒ quadratic upper bound` chain is a Mathlib gap — promote when upstream lands.

## Bach's textbook treatment

# Bach textbook excerpt — McAllester PAC-Bayes bound (algebraic core anchor)

**Concept ID:** `pac-bayes-mcallester`
**Chapter:** Ch 14
**Section:** §14.4.2 "Uniformly Bounded Loss Functions"
**Pages:** 423-426 (book); PDF pages 439-442
**Source:** Bach (2024), *Learning Theory from First Principles*

## Reading notes

1. **Bach Ch 14 ends at Eq. (14.6).** There is no "Eq. 14.21" in Bach.
   All equations in Chapter 14 are: (14.1), (14.2), (14.3), (14.4),
   (14.5), (14.6). Synthesized equation labels can drift; verify
   against the canonical PDF before citing.
2. **Bach's PAC-Bayes proof in §14.4.2 uses, in order:**
   - per-θ Hoeffding linear MGF bound (cited back to §1.2.1),
   - integration against the prior `q`,
   - Donsker-Varadhan variational formula for the log-partition,
   - Chernoff bound (cited via exercise 1.10).
3. Bach does NOT use McDiarmid's bounded-difference moment bound, and
   does NOT use a Bernoulli method-of-types argument.

## Statement (verbatim)

Section §14.4.2, starting on book p.423:

> We assume that almost surely, for all θ ∈ Θ, we have ℓ(y, fθ(x)) ∈
> [0, ℓ∞] (e.g., with the 0–1 loss for binary classification or with
> bounded predictors for regression). Following the exposition of
> Alquier (2024) and Catoni (2003), in the proof of Hoeffding's
> inequality in section 1.2.1, we saw that for all θ ∈ Θ and s ∈ ℝ₊,
> we have
>
>     E exp(s(R(θ) − R̂(θ)))  ≤  exp( s² ℓ∞² / (8n) ).

(Bach p.424, top.) The final user-facing form is Bach's bound on the
average generalization error:

> with probability at least 1 − δ, for all ρ ∈ P(θ),
>
>     ∫ R(θ) dρ(θ)  ≤  ∫ R̂(θ) dρ(θ)  +  (1/s) D(ρ‖q)  +  (1/s) log(1/δ)  +  s ℓ∞² / (8n).

(Bach p.424, middle.) And the in-expectation form, **equation (14.6)**:

>     E[∫ R(θ) dρ̂s(θ)]  ≤  inf_{ρ ∈ P(Θ)} { ∫ R(θ) dρ(θ) + (1/s) D(ρ‖q) + s ℓ∞² / (8n) }.   (14.6)

(Bach p.425, after the "Beyond integrated risks" subhead.)

## Proof (verbatim)

Bach's full §14.4.2 derivation, reproduced verbatim from book p.423-425:

> Following the exposition of Alquier (2024) and Catoni (2003), in the
> proof of Hoeffding's inequality in section 1.2.1, we saw that for
> all θ ∈ Θ and s ∈ ℝ₊, we have
>
>     E exp(s(R(θ) − R̂(θ)))  ≤  exp(s² ℓ∞² / (8n)).
>
> Integrating over θ, we get
>
>     ∫_Θ E exp(s(R(θ) − R̂(θ))) dq(θ)  ≤  exp(s² ℓ∞² / (8n)).
>
> We now use the variational formulation of the log-partition function
> (also known as the "Donsker-Varadhan formula"), with
> h(θ) = s(R(θ) − R̂(θ)):
>
>     log ∫_Θ exp(h(θ)) dq(θ)  =  sup_{ρ ∈ P(θ)} [ ∫_Θ h(θ) dρ(θ) − D(ρ‖q) ],
>
> with P(θ) the set of probability distributions on Θ and D(ρ‖q) the
> Kullback-Leibler (KL) divergence between ρ and q, defined as follows
> (see also section 15.1.3):
>
>     D(ρ‖q)  =  ∫_Θ log(dρ/dq)(θ) dρ(θ).
>
> This leads to
>
>     E exp{ sup_{ρ ∈ P(θ)} [ ∫_Θ s(R(θ) − R̂(θ)) dρ(θ) − D(ρ‖q) ] }
>         ≤  exp(s² ℓ∞² / (8n)).                                                (14.5)
>
> Thus, using the Chernoff bound, we obtain that with a probability
> greater than 1 − δ,
>
>     sup_{ρ ∈ P(θ)} [ ∫_Θ s(R(θ) − R̂(θ)) dρ(θ) − D(ρ‖q) ]
>         ≤  s² ℓ∞² / (8n)  +  log(1/δ),
>
> or, in other words, with probability at least 1 − δ, for all ρ ∈ P(θ),
>
>     ∫_Θ R(θ) dρ(θ)  ≤  ∫_Θ R̂(θ) dρ(θ) + (1/s) D(ρ‖q)
>                       + (1/s) log(1/δ) + s ℓ∞² / (8n).
>
> [...] The scaling of the bound between empirical and population
> quantities is of form C s/n + C′/s for constants C, C′, thus leading
> to a natural choice of s ∝ √n, to obtain the traditional scaling in
> O(1/√n).

For the in-expectation form (Eq. 14.6), Bach continues (p.425):

> Moreover, by applying Jensen's inequality to equation (14.5), we
> can get a bound in expectation as for all ρ ∈ P(θ) (again, ρ may
> depend on the data):
>
>     E[∫_Θ R(θ) dρ(θ)]  ≤  E[∫_Θ R̂(θ) dρ(θ) + (1/s) D(ρ‖q)]
>                          + s ℓ∞² / (8n).
>
> Moreover, for the Gibbs posterior distribution, by applying Jensen's
> inequality, we get
>
>     E[∫_Θ R(θ) dρ̂s(θ)]  ≤  inf_{ρ ∈ P(Θ)} { ∫_Θ R(θ) dρ(θ)
>         + (1/s) D(ρ‖q) + s ℓ∞² / (8n) }.                                       (14.6)

## Notes

- **Three named ingredients, in this exact order:**
  1. Per-θ Hoeffding linear MGF: `E exp(s X) ≤ exp(s² ℓ∞² / (8n))` for
     `X = R(θ) − R̂(θ)` (this is the *only* concentration input — Bach
     reuses the Hoeffding MGF from §1.2.1, *not* McDiarmid).
  2. Donsker-Varadhan variational formula:
     `log ∫ exp(h) dq = sup_ρ [∫ h dρ − KL(ρ‖q)]`.
  3. Chernoff bound applied to the supremum random variable, with
     cross-reference to exercise 1.10 / the Wikipedia article on the
     Chernoff bound (Bach footnote 9, p.424).
- **No method-of-types, no Bernoulli KL.** A proof of this bound via
  "Bernoulli KL method-of-types" or "McDiarmid moment bound" follows
  neither what Bach writes nor a textbook-first proof path. The
  formalization should follow Bach's per-θ Hoeffding +
  Donsker-Varadhan + Chernoff chain.
- **Algebraic core anchor.** The B5 carrier is correctly named
  `pac_bayes_mcallester`; the McAllester-style bound in Bach's notation
  is the post-Chernoff inequality on p.424 (the line just before "We
  thus get a bound on the average generalization error..."). The
  algebraic core that drives this is the Hoeffding linear MGF bound
  from §1.2.1 plus the Donsker-Varadhan variational identity. Both
  are isolatable as standalone algebraic facts.
- **Bach's Eq. (14.5)** is the joint-event MGF-after-DV bound; **Eq.
  (14.6)** is its post-Jensen, in-expectation Gibbs form. Neither
  carries the McAllester `√(KL/n)` rate explicitly — that rate appears
  after the choice `s ∝ √n` discussed in prose on p.424 ("traditional
  scaling in O(1/√n)").
- **Flagged ambiguity:** Bach defers the Lipschitz-loss + Gaussian-prior
  Rademacher-style PAC-Bayes rate to Alquier (2024) (p.425 last
  paragraph "Lipschitz-continuous losses, linear predictions, and
  Gaussian priors"). For applications needing those tighter rates, the
  textbook-first protocol stops here and routes LITERATURE.
- **Cross-reference for KL definition:** Bach defers the full KL
  definition to §15.1.3 (info-theory review). See excerpt for
  `infotheory-foundation`.

## Prerequisites (Bach's dependency graph)

- [`pac-bayes-kl`](./pac-bayes-kl.md) — PAC-Bayes KL divergence wrapper

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = partial`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch14_Probabilistic/PACBayes.lean`
- **Theorem/def name:** `mcallester_bound_nonneg`
- **Status:** B
- **Primary closing commit:** `93ec201` (theorem `pac_bayes_mcallester`)
- **Audit class:** **B**
- **Audit notes:** Discharges *abstract* DV + concentration but takes *scalar shadow primitives* as new inputs (`expMGFp ≤ 2√n/δ`, `2n·EQgapSq - logMGFp ≤ D`); full measure-theoretic discharge via `klDiv` variational formula still upstream. **A-class successor `pac_bayes_mcallester_bach_path_a_class` (PACBayes.lean:1546, `6bbc9d9` + `54d34c9`) closes this for the Bach §14.4.2 in-expectation form via the per-θ Hoeffding linear MGF → DV → Chernoff chain; this scalar wrapper retained as alternative entry point.**

## Audit history (if any)

- commit `93ec201` — theorem `pac_bayes_mcallester` — classified **B** in PROGRESS.md §10 (Discharges *abstract* DV + concentration but takes *scalar shadow primitives* as new inputs (`expMGFp ≤ 2√n/δ`, `2n·EQgapSq - logMGFp ≤ D`); full measure-theoretic discharge via `klDiv` variational formula still upstream. **A-class successor `pac_bayes_mcallester_bach_path_a_class` (PACBayes.lean:1546, `6bbc9d9` + `54d34c9`) closes this for the Bach §14.4.2 in-expectation form via the per-θ Hoeffding linear MGF → DV → Chernoff chain; this scalar wrapper retained as alternative entry point.**)
- commit `a71d6d5` — theorem `pac_bayes_mcallester_abstract` — classified **B** in PROGRESS.md §10 (Abstract DV + function-class concentration are HYPOTHESES)

## Notes / open questions

- Carrier is **parametric** — at least one substantive hypothesis is passed through, not discharged.
- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

