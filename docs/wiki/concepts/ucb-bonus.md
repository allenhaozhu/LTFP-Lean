# UCB confidence bonus √(2 log t / n)

**ID:** `ucb-bonus`  
**Chapter:** Ch11 (Bach §11.3.3, p. 336)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Online/Bandits`

## Statement

_See textbook excerpt below or [`tasks/ucb-bonus/`](../../../tasks/ucb-bonus/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — UCB exploration bonus ν_t

**Concept ID:** `ucb-bonus`
**Chapter:** Ch 11
**Section:** §11.3.3 "Optimism in the Face of Uncertainty"
**Pages:** 335-336 (book) / PDF pp. 351-352
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

From §11.3.3, p. 336:

> "The precise algorithm is as follows (assuming that $\sigma$ is known):
> • For the first $k$ rounds, select each arm exactly once and form $\hat\mu_k^{(i)}$ as the reward received for arm $i$, with $\nu_k^{(i)} = \sqrt{2\rho \sigma^2 \log(k) / n_k^{(i)}} = \sqrt{2\rho \sigma^2 \log(k)}$, with $\rho > 0$ to be determined later.
> • For all other $t > k$, select the arm $i_t$ that maximizes $\hat\mu_{t-1}^{(i)} + \nu_{t-1}^{(i)}$, receive the reward, and update, for all $i$, $\hat\mu_t^{(i)}$ as the average reward received for all arms $i \in \{1,\dots,k\}$, with the interval width
> $$\nu_t^{(i)} = \sqrt{2\rho \sigma^2 \log(t) / n_t^{(i)}}.$$"

Lean carrier `ucbBonus (ρ σ : ℝ) (t n : ℕ) : ℝ := Real.sqrt (2 * ρ * σ^2 * Real.log t / n)` packages the radical $\sqrt{2\rho\sigma^2 \log(t)/n}$ as the per-arm confidence interval half-width.

## Proof (verbatim)

Definition, no proof. The bound on $\mathbb{P}(\hat\mu_{u-1}^{(i^\star)} + \nu_{u-1}^{(i^\star)} \le \mu^{(i^\star)})$ (eq. (11.26)) uses the bonus to control the optimal arm's underestimation probability — leading to the $1/s^\rho$ summand on p. 337.

## Notes

- The factor $2\rho$ inside the radical: sub-Gaussian tail $\mathbb{P}(\hat\mu - \mu \le -\sqrt{2\rho \sigma^2 \log t / n}) \le \exp(-\rho \log t) = t^{-\rho}$, which is summable for $\rho > 1$ (Bach uses $\rho = 2$ at p. 338, eq. (11.28)).
- Confidence interval: $[\hat\mu_t^{(i)} - \nu_t^{(i)}, \hat\mu_t^{(i)} + \nu_t^{(i)}]$ on p. 336.
- Optimism: the algorithm pulls the arm with maximal *upper* confidence bound (the figure on p. 336 illustrates with $k=4$ arms).

## Prerequisites (Bach's dependency graph)

- [`bandit-foundation`](./bandit-foundation.md) — Multi-armed bandit foundation: cumulative regret

## Dependents (concepts that use this)

- [`ucb-bonus-nonneg`](./ucb-bonus-nonneg.md) — UCB bonus is nonnegative

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch11_OnlineBandits/UCB.lean`
- **Theorem/def name:** `ucbBonus`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

