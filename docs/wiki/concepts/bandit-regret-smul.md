# Bandit regret rewriting in scaled mu_star

**ID:** `bandit-regret-smul`  
**Chapter:** Ch11 (Bach §F8b)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Online/Bandits`

## Statement

_See textbook excerpt below or [`tasks/bandit-regret-smul/`](../../../tasks/bandit-regret-smul/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Bandit regret scales linearly with µ⋆ rescaling

**Concept ID:** `bandit-regret-smul`
**Chapter:** Ch 11
**Section:** §11.3 (foundation F8b)
**Pages:** 332 (book) / PDF p. 348
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Algebraic shell statement extracted from Bach's regret definition:

$$R_T = T \mu^\star - \sum_{t=1}^{T} \mu(a_t).$$

Linearity in $\mu^\star$: if we replace $\mu^\star$ with $c \cdot \mu^\star$ in the *first* term only (the trivial "linearity-of-the-multiplicative-constant" sanity check Bach uses implicitly when normalizing rewards), the contribution scales as $c \cdot T \cdot \mu^\star$ — i.e., scaling the optimal mean by $c$ scales the first regret term by $c$.

Lean carrier `banditRegret_smul_mu_star`: a `smul` (scalar-multiplication) compatibility law on the carrier.

## Proof (verbatim)

Bach defers — this is a structural shell property, not a numbered result in the book. The regret is defined as $T \mu^\star - (\text{sum of pulled rewards})$, and substituting $c \mu^\star$ for $\mu^\star$ in the first term gives $c T \mu^\star - \sum \mu(a_t)$. In Lean it discharges by `unfold banditRegret; ring`.

## Notes

- One of the algebraic-shell sanity properties of `banditRegret` (alongside `bandit-regret-zero-horizon` and `bandit-regret-const-action`).
- Not used directly in any of Bach's stated theorems, but verifies the carrier's algebraic well-behavedness.
- No probability content.

## Prerequisites (Bach's dependency graph)

- [`bandit-foundation`](./bandit-foundation.md) — Multi-armed bandit foundation: cumulative regret

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/Bandit.lean`
- **Theorem/def name:** `banditRegret_smul_mu_star`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

