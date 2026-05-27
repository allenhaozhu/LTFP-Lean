# Markov's inequality (real probabilistic statement)

**ID:** `markov-inequality`  
**Chapter:** Ch01 (Bach §F9)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/markov-inequality/`](../../../tasks/markov-inequality/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Markov's inequality

**Concept ID:** `markov-inequality`
**Chapter:** Ch 1
**Section:** 1.2 (foundational F9 alias)
**Pages:** 8
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach introduces Markov's inequality as equation (1.5) in the opening paragraphs of
§1.2 (page 8):

> From moments to deviation bounds. Given an inequality on the moments of a
> random variable, deviation bounds can be derived. Markov's inequality (see the proof
> in exercise 1.9 below) states that
> $$\mathbb{P}(Y \ge \varepsilon) \;\le\; \tfrac{1}{\varepsilon} \mathbb{E}[Y], \qquad (1.5)$$
> for all nonnegative random variables $Y$ with finite expectation and any scalar
> $\varepsilon > 0$.

## Proof (verbatim)

Bach does not give the proof inline; he defers to Exercise 1.9 (page 9):

> **Exercise 1.9.** Let $Y$ be a nonnegative random variable with finite expectation,
> and $\varepsilon > 0$. Show that $\varepsilon \mathbf{1}_{Y \ge \varepsilon} \le Y$
> almost surely and prove Markov's inequality in equation (1.5).

The expected solution chain: pointwise $\varepsilon \mathbf{1}_{Y \ge \varepsilon} \le Y$
(case analysis on whether $Y \ge \varepsilon$); take expectations on both sides to get
$\varepsilon \, \mathbb{P}(Y \ge \varepsilon) \le \mathbb{E}[Y]$; divide by $\varepsilon$.

## Notes

- Bach uses Markov's inequality as the workhorse for every Chernoff-style argument
  in the chapter: it is invoked in the proof of Hoeffding's inequality (Proposition 1.2),
  McDiarmid's inequality (Proposition 1.3), and Bernstein's inequality (Proposition 1.4).
- Immediately after stating (1.5), Bach derives Chebyshev's inequality as the
  $Y = (X - \mathbb{E}X)^2$ instance:
  $\mathbb{P}(|X - \mathbb{E}X| \ge \varepsilon) = \mathbb{P}(|X - \mathbb{E}X|^2 \ge \varepsilon^2)
  \le \tfrac{1}{\varepsilon^2} \operatorname{var}[X]$.
- Bach also states the closely related Chernoff bound as Exercise 1.10:
  $\mathbb{P}(X \ge t) \le e^{-st} \mathbb{E}[e^{sX}]$ for any $s > 0$.
- Proof technique: pointwise indicator bound + monotonicity of expectation. This is
  the canonical Mathlib statement `MeasureTheory.meas_ge_le_mul_pow_snorm` (real-valued
  form for nonneg random variables); Lean target is the standard real probabilistic
  form.

## Prerequisites (Bach's dependency graph)

- [`infotheory-foundation`](./infotheory-foundation.md) — Information-theory foundation: KL divergence wrapper

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/MeasureProb.lean`
- **Theorem/def name:** `markov_inequality`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

