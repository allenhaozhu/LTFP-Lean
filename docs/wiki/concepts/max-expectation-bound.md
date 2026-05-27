# Expected maximum of sub-Gaussian variables ≤ √(2 σ² log n)

**ID:** `max-expectation-bound`  
**Chapter:** Ch01 (Bach §1.2.4, p. 16)  
**Kind:** lemma  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** in_lean_rademacher  
**Topic tags:** `Gaussian`, `Sub-Gaussian`

## Statement

_See textbook excerpt below or [`tasks/max-expectation-bound/`](../../../tasks/max-expectation-bound/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Expected maximum of sub-Gaussian variables ≤ √(2 σ² log n)

**Concept ID:** `max-expectation-bound`
**Chapter:** Ch 1
**Section:** 1.2.4
**Pages:** 16–17
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

> **Proposition 1.5 (Expectation of the maximum)** If $Z_1, \dots, Z_n$ are
> (potentially dependent) zero-mean real random variables that are sub-Gaussian
> with constant $\tau^2$, then
> $$\mathbb{E}\!\bigl[\max\{Z_1, \dots, Z_n\}\bigr] \;\le\; \sqrt{2 \tau^2 \log n}.$$

Bach also flags as a margin remark:

> ! The variables do not need to be independent.

## Proof (verbatim)

> **Proof.** We have
> $$\mathbb{E}\!\bigl[\max\{Z_1, \dots, Z_n\}\bigr] \;\le\; \tfrac{1}{t} \log \mathbb{E}\!\bigl[e^{t \max\{Z_1,\dots,Z_n\}}\bigr] \quad \text{by Jensen's inequality,}$$
> $$= \tfrac{1}{t} \log \mathbb{E}\!\bigl[\max\{e^{tZ_1}, \dots, e^{tZ_n}\}\bigr]$$
> $$\le \tfrac{1}{t} \log \mathbb{E}\!\bigl[e^{tZ_1} + \cdots + e^{tZ_n}\bigr] \quad \text{bounding the max by the sum,}$$
> $$\le \tfrac{1}{t} \log\!\bigl(n e^{\tau^2 t^2/2}\bigr) \;=\; \tfrac{\log n}{t} + \tau^2 \tfrac{t}{2} \;=\; \sqrt{2 \tau^2 \log n} \quad \text{with } t = \tau^{-1} \sqrt{2 \log n},$$
> using the definition of sub-Gaussianity in section 1.2.1 (and the fact that the
> variables have zero means).

## Notes

- Key intermediate input: each $Z_i$ is $\tau^2$-sub-Gaussian, i.e.,
  $\mathbb{E}[e^{tZ_i}] \le e^{\tau^2 t^2/2}$ for all $t \in \mathbb{R}$ (defined
  in §1.2.1 as a consequence of Hoeffding's lemma).
- Bach's proof technique: Jensen's inequality on the convex function $z \mapsto e^{tz}$
  to push $\mathbb{E}$ inside the log, max-by-sum to linearize, sub-Gaussian MGF bound,
  then optimize $t$ analytically (the optimum is $t = \tau^{-1}\sqrt{2 \log n}$).
- Bach notes the bound holds even WITHOUT independence — this is the key advantage
  of the Laplace-transform/sub-Gaussian argument over union-bound approaches.
- Bach contrasts this with the alternative union-bound + Gaussian-tail proof, which
  he writes informally: $\mathbb{P}(\max U_i > t) \le \sum_i \mathbb{P}(U_i > t)$.
  The two routes give the same $\sqrt{\log n}$ rate.
- Bach references this lemma as the source of the ubiquitous "$\sqrt{\log n}$"
  logarithmic factor that appears throughout the book in connection with
  Rademacher complexities (§4.5) and supremum bounds.
- Exercise 1.22 extends to $\mathbb{E}[\max |Z_i|] \le \sqrt{2\tau^2 \log(2n)}$.

## Prerequisites (Bach's dependency graph)

- [`hoeffding-lemma`](./hoeffding-lemma.md) — Hoeffding's lemma (MGF bound for bounded variables)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = in_lean_rademacher`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/MaximalInequality.lean`
- **Theorem/def name:** `maximal_inequality_supR`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

