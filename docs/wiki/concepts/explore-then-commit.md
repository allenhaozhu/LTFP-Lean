# Explore-then-commit exploration phase predicate

**ID:** `explore-then-commit`  
**Chapter:** Ch11 (Bach §11.3.2)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/explore-then-commit/`](../../../tasks/explore-then-commit/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Explore-then-commit phase indicator

**Concept ID:** `explore-then-commit`
**Chapter:** Ch 11
**Section:** §11.3.2 "Explore-Then-Commit"
**Pages:** 333-334 (book) / PDF pp. 349-350
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

From §11.3.2, p. 333:

> "If we consider $mk$ steps where we select exactly each arm $m$ times, we can build $m$ estimates $\hat\mu^{(1)},\dots,\hat\mu^{(k)}$, which are all independent random variables with means $\mu^{(1)},\dots,\mu^{(k)}$ and sub-Gaussian parameters $\sigma^2/m$. Let $i^\star$ be the optimal arm.
> We then select the arm with maximal $\hat\mu_{mk}^{(j)}$ for all remaining $t - km$ steps."

The Lean carrier `isExplorationPhase (m k t : ℕ) : Prop := t ≤ m * k` packages the *exploration phase* indicator — the first $mk$ time steps where each arm is pulled $m$ times.

## Proof (verbatim)

Definition (a `Prop`-valued predicate); no proof. Bach uses it implicitly when decomposing the regret bound (eq. (11.20), p. 333) as

$$R_t = \underbrace{m \sum_{j=1}^{k} \Delta^{(j)}}_{\text{exploration contribution}} + \underbrace{(t - mk) \sum_{j=1}^{k} \Delta^{(j)} \mathbb{P}(\hat\mu_{mk}^{(j)} > \hat\mu_{mk}^{(i)}, \forall i \neq j)}_{\text{commit phase}}.$$

The Lean predicate `t ≤ m*k` captures "we are still in the explore phase at time $t$".

## Notes

- Boundary case: at $t = mk$, the algorithm switches modes — Bach treats $t > mk$ as the commit phase (p. 333, "for all remaining $t - km$ steps").
- Decisions in the explore phase are independent of empirical means (round-robin); decisions in the commit phase greedy on $\arg\max_j \hat\mu_{mk}^{(j)}$.
- Used as a setup definition for the regret bound (11.24), but not for any downstream Lean theorem in this Wave (it's an organizational anchor).

## Prerequisites (Bach's dependency graph)

- [`bandit-foundation`](./bandit-foundation.md) — Multi-armed bandit foundation: cumulative regret

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch11_OnlineBandits/UCB.lean`
- **Theorem/def name:** `isExplorationPhase`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

