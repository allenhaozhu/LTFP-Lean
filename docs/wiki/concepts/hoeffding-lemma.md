# Hoeffding's lemma (MGF bound for bounded variables)

**ID:** `hoeffding-lemma`  
**Chapter:** Ch01 (Bach §1.2.1, p. 10)  
**Kind:** lemma  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** in_lean_rademacher  
**Topic tags:** `Concentration`

## Statement

_See textbook excerpt below or [`tasks/hoeffding-lemma/`](../../../tasks/hoeffding-lemma/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Hoeffding's lemma (MGF bound for bounded variables)

**Concept ID:** `hoeffding-lemma`
**Chapter:** Ch 1
**Section:** 1.2.1
**Pages:** 10–11
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach states Hoeffding's lemma as part (1) of the proof of Hoeffding's inequality
(Proposition 1.2, page 10):

> **(1) Lemma:** If $Z \in [0,1]$ almost surely, then
> $$\mathbb{E}\!\bigl[\exp(s(Z - \mathbb{E}[Z]))\bigr] \;\le\; \exp(s^2/8) \quad \text{for any } s > 0.$$

The surrounding proposition (Proposition 1.2, "Hoeffding's inequality") reads:

> If $Z_1,\dots,Z_n$ are independent random variables such that $Z_i \in [0,1]$
> almost surely, then for any $t>0$,
> $$\mathbb{P}\!\left(\frac{1}{n}\sum_{i=1}^n Z_i - \frac{1}{n}\sum_{i=1}^n \mathbb{E}[Z_i] \ge t\right) \;\le\; \exp(-2nt^2). \quad (1.7)$$

## Proof (verbatim)

> **Proof:** We can compute the first two derivatives of the function $\varphi$ defined
> as $\varphi(s) = \log\bigl(\mathbb{E}\exp(s(Z - \mathbb{E}[Z]))\bigr)$, which is a
> "log-sum-exp" function, often referred to as the "cumulant generating function."
> We can compute the derivatives of $\varphi$ as
> $$\varphi'(s) = \frac{\mathbb{E}\!\bigl[(Z - \mathbb{E}[Z]) e^{s(Z-\mathbb{E}[Z])}\bigr]}{\mathbb{E}\!\bigl[e^{s(Z-\mathbb{E}[Z])}\bigr]}$$
> $$\varphi''(s) = \frac{\mathbb{E}\!\bigl[(Z - \mathbb{E}[Z])^2 e^{s(Z-\mathbb{E}[Z])}\bigr]}{\mathbb{E}\!\bigl[e^{s(Z-\mathbb{E}[Z])}\bigr]} - \left(\frac{\mathbb{E}\!\bigl[(Z - \mathbb{E}[Z]) e^{s(Z-\mathbb{E}[Z])}\bigr]}{\mathbb{E}\!\bigl[e^{s(Z-\mathbb{E}[Z])}\bigr]}\right)^2.$$
> We thus get $\varphi(0) = \varphi'(0) = 0$, and $\varphi''(s)$ is the variance of some
> random variable $\tilde{Z} \in [0,1]$, with distribution with density
> $z \mapsto e^{s(z - \mathbb{E}[Z])}/\mathbb{E}\!\bigl[e^{s(Z-\mathbb{E}[Z])}\bigr]$ with
> respect to the distribution of $Z$. We recall that the variance of $\tilde{Z}$ is
> the minimum squared deviation to a constant and can thus bound this variance as
> $$\operatorname{var}(\tilde{Z}) = \inf_{\nu \in [0,1]} \mathbb{E}[(\tilde{Z} - \nu)^2] \le \mathbb{E}[(\tilde{Z} - 1/2)^2] = \tfrac{1}{4}\mathbb{E}[(2\tilde{Z}-1)^2] \le \tfrac{1}{4},$$
> since $2\tilde{Z} - 1 \in [-1,1]$ almost surely. Thus, for all $s > 0$,
> $\varphi''(s) \le 1/4$, and by Taylor's formula,
> $\varphi(s) \le \varphi(0) + \varphi'(0) s + \tfrac{1}{4} \cdot \tfrac{s^2}{2} = \tfrac{s^2}{8}.$

## Notes

- Bach proves the lemma inline as step (1) of Proposition 1.2's proof; this is the
  classical "log-MGF Taylor bound" form rather than the more common Hoeffding-original
  $b - a$ form (which would give $\exp(s^2(b-a)^2/8)$).
- Bach's proof technique: differentiate the cumulant generating function $\varphi$ twice,
  reinterpret $\varphi''(s)$ as a variance under a tilted distribution, bound that
  variance by $1/4$ via $\inf_\nu \mathbb{E}[(\tilde{Z}-\nu)^2] \le \mathbb{E}[(\tilde{Z}-1/2)^2]$,
  then apply Taylor's formula to integrate the second-derivative bound.
- Step (2) of the proof then exponentiates, applies Markov's inequality (equation 1.5),
  uses independence to factor the MGF over $i$, and optimizes over $s$ (giving $s = 4nt$).
- For the general $Z \in [a,b]$ form ($\mathbb{E}\exp(s(Z-\mathbb{E}Z)) \le \exp(s^2(b-a)^2/8)$),
  Bach defers to the standard literature; he treats only the unit-interval case directly.
- The vendored `LTFP/Foundations/Hoeffding.lean` corresponds to the general bounded form
  (`ProbabilityTheory.hoeffding`), which agrees with Bach's lemma after rescaling
  $Z \mapsto (Z-a)/(b-a)$.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

- [`bernstein-inequality`](./bernstein-inequality.md) — Bernstein's inequality (♦)
- [`max-expectation-bound`](./max-expectation-bound.md) — Expected maximum of sub-Gaussian variables ≤ √(2 σ² log n)
- [`mcdiarmid-inequality`](./mcdiarmid-inequality.md) — McDiarmid's bounded-differences inequality
- [`ntk-concentration-scalar-hoeffding`](./ntk-concentration-scalar-hoeffding.md) — Empirical NTK concentration via scalar Hoeffding + union bound (N4 alt)

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = in_lean_rademacher`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/Hoeffding.lean`
- **Theorem/def name:** `ProbabilityTheory.hoeffding`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

