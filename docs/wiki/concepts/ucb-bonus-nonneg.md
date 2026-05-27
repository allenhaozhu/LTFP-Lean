# UCB bonus is nonnegative

**ID:** `ucb-bonus-nonneg`  
**Chapter:** Ch11 (Bach §11.3.3, p. 336)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** `Online/Bandits`

## Statement

_See textbook excerpt below or [`tasks/ucb-bonus-nonneg/`](../../../tasks/ucb-bonus-nonneg/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — UCB bonus is nonnegative

**Concept ID:** `ucb-bonus-nonneg`
**Chapter:** Ch 11
**Section:** §11.3.3
**Pages:** 336 (book) / PDF p. 352
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Algebraic anchor extracted from §11.3.3: the bonus $\nu_t^{(i)} = \sqrt{2\rho\sigma^2 \log t / n_t^{(i)}}$ is nonnegative whenever the radicand is nonnegative, i.e. when $\rho \ge 0$, $\log t \ge 0$ (so $t \ge 1$), and $n > 0$.

> "For the first $k$ rounds, select each arm exactly once … with $\nu_k^{(i)} = \sqrt{2\rho \sigma^2 \log(k)}$, with $\rho > 0$." (p. 336)

Bach does not state $\nu \ge 0$ as a numbered lemma; it is automatic from $\sqrt{\cdot} \ge 0$.

## Proof (verbatim)

Bach defers: square roots of reals are nonnegative by definition. In Lean this is `Real.sqrt_nonneg`. The textbook never makes this a lemma — it is one of the "obvious" sanity facts the analysis depends on (the bonus widens the upper confidence interval, never narrows it).

## Notes

- One-line proof: `Real.sqrt_nonneg _`.
- Used wherever the algorithm's upper confidence bound $\hat\mu_t^{(i)} + \nu_t^{(i)}$ needs to be compared against $\hat\mu_t^{(i)}$ as a baseline (e.g., "optimism" framing on p. 336).
- Status `in_mathlib`: discharged via `Real.sqrt_nonneg` from Mathlib's `Mathlib.Analysis.SpecialFunctions.Pow.Real`.

## Prerequisites (Bach's dependency graph)

- [`ucb-bonus`](./ucb-bonus.md) — UCB confidence bonus √(2 log t / n)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch11_OnlineBandits/UCB.lean`
- **Theorem/def name:** `ucbBonus_nonneg`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

