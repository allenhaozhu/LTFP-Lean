# Variance is nonneg (real probabilistic statement)

**ID:** `variance-nonneg-real`  
**Chapter:** Ch01 (Bach §F9)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/variance-nonneg-real/`](../../../tasks/variance-nonneg-real/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Variance is nonneg (real probabilistic statement)

**Concept ID:** `variance-nonneg-real`
**Chapter:** Ch 1
**Section:** 1.2 (foundational F9 alias)
**Pages:** 7–8
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach does not give variance-nonnegativity as a named proposition; he uses it implicitly
when introducing variance at the top of §1.2 (page 7). The fact $\operatorname{var}(X) \ge 0$
is taken as immediate from the definition

$$\operatorname{var}(X) \;=\; \mathbb{E}\!\bigl[(X - \mathbb{E} X)^2\bigr],$$

an expectation of a nonnegative random variable.

In Bach's "variance of an average" calculation (§1.2, equation (1.4), page 8):

> $$\mathbb{E}\!\left[\left(\frac{1}{n}\sum_{i=1}^n Z_i - \mathbb{E}[Z]\right)^2\right] \;=\; \frac{\sigma^2}{n}, \qquad (1.4)$$
>
> which provides the simplest proof of the law of large numbers when variances exist
> and also highlights the convergence in the squared mean of the random variable
> $\tfrac{1}{n} \sum_{i=1}^{n} Z_i$ to the constant $\mathbb{E}[Z]$.

The nonnegativity of $\sigma^2$ underlies the whole "moments to deviation bounds"
machinery (Chebyshev, Bernstein) in the rest of §1.2.

## Proof (verbatim)

Bach gives no proof; he treats variance as a familiar object. The standard derivation
(which Lean targets) is:

- $(X - \mathbb{E} X)^2 \ge 0$ pointwise (square of a real is nonneg).
- $\mathbb{E}[\cdot]$ of a nonneg random variable is nonneg (monotonicity of integral).
- Therefore $\operatorname{var}(X) = \mathbb{E}[(X - \mathbb{E} X)^2] \ge 0$.

## Notes

- This is an "F9 alias" — Bach treats it as standard probability prerequisite, not
  a theorem of the book.
- Used (implicitly) in: §1.2 variance-of-average computation (eq. 1.4), Chebyshev's
  inequality derivation, the variance bound $\operatorname{var}(\tilde{Z}) \le 1/4$ in
  the Hoeffding lemma proof (Proposition 1.2, page 10).
- Standard Mathlib target: `ProbabilityTheory.variance_nonneg`.
- Proof technique: square of real is nonneg + monotonicity of expectation.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/MeasureProb.lean`
- **Theorem/def name:** `variance_nonneg_real`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

