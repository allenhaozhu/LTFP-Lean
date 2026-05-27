# Online-convex foundation: regret definition

**ID:** `online-convex-foundation`  
**Chapter:** Ch11 (Bach §F8a)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Convex`, `Online/Bandits`

## Statement

Required prereq for Ch 11.

## Bach's textbook treatment

# Bach textbook excerpt — Online convex optimization foundation: regret functional

**Concept ID:** `online-convex-foundation`
**Chapter:** Ch 11
**Section:** §11.1 (foundation F8a — algebraic anchor)
**Pages:** 315-316 (book) / PDF pp. 331-332
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

From §11.1, p. 315:

> "In this section, we consider a sequence of arbitrary deterministic real-valued convex functions $F_s : \mathbb{R}^d \to \mathbb{R}$, $s \ge 1$, and a compact convex set $C$. The goal of online convex optimization is, starting from a certain $\theta_0 \in C$, to obtain a sequence $(\theta_s)_{s \ge 1}$ so the regret at time $t$, defined as
> $$\frac{1}{t}\sum_{s=1}^{t} F_s(\theta_{s-1}) - \inf_{\theta \in C} \frac{1}{t}\sum_{s=1}^{t} F_s(\theta), \tag{11.1}$$
> is as small as possible."

The Lean anchor (`regret`) drops the convexity / domain hypotheses and the `1/t` normalization (Bach studies the *normalized* regret; the Lean form is the unnormalized sum). The carrier is the algebraic identity

$$R_T(\theta_\star) \;=\; \sum_{t=1}^{T} F_t(\theta_{t-1}) \;-\; \sum_{t=1}^{T} F_t(\theta_\star).$$

## Proof (verbatim)

No proof — this is a definition (the regret functional). Bach later instantiates it for SGD via Proposition 11.1 (p. 316-317).

## Notes

- Bach normalizes by $1/t$ ("the *normalized* regret … to make comparisons with the usual stochastic framework easier", p. 314, footnote-style aside). The Lean carrier uses the unnormalized sum because division by $T$ trivially divides both sides of every downstream inequality.
- The play sequence `xs : Fin T → E` plays `xs t` at time `t` AFTER seeing `f_0,…,f_{t-1}`. The comparator `xstar : E` is a fixed action that gets to see the whole sequence.
- Used as the prerequisite for `regret-cumloss-diff`, `cum-loss`, and the OCO part of Wave VIII.

## Prerequisites (Bach's dependency graph)

- [`convex-foundation`](./convex-foundation.md) — Convex analysis foundation: L-smooth alias + Mathlib re-exports

## Dependents (concepts that use this)

- [`cum-loss`](./cum-loss.md) — OCO cumulative loss L_T(x) = ∑_t f_t(x)

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/OnlineConvex.lean`
- **Theorem/def name:** `regret`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

