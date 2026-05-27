# Linear kernel self-evaluation = squared norm

**ID:** `linear-kernel-self`  
**Chapter:** Ch07 (Bach §F4a)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Kernel`, `Neural-network`

## Statement

_See textbook excerpt below or [`tasks/linear-kernel-self/`](../../../tasks/linear-kernel-self/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Linear kernel self-evaluation = squared norm

**Concept ID:** `linear-kernel-self`
**Chapter:** Ch 7
**Section:** §7.3.1 / Foundation F4a (derived corollary)
**Pages:** 186 (book) / PDF p. 202
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For the linear kernel $k(x, y) = x^\top y$ on $\mathbb{R}^d$ and any $x \in \mathbb{R}^d$,

$$k(x, x) = x^\top x = \|x\|_2^2.$$

## Proof (verbatim)

Not stated as a numbered lemma; Bach uses this identity implicitly throughout. The boundedness assumption in §7.4 (p. 196) writes:

"We assume that features are bounded; that is, for all $i \in \{1, \dots, n\}$, $k(x_i, x_i) = \|\phi(x_i)\|_\mathcal{H}^2 \le R^2$."

For the linear kernel with $\phi = \mathrm{id}$, $k(x,x) = x^\top x = \|x\|_2^2$ is the definition of the Euclidean squared norm. (Sketch.)

## Notes

- Lean form `linearKernel_self` in `LTFP/Foundations/Kernel.lean`.
- Used to bound the RKHS norm of feature vectors in generalization-error proofs (§7.5).
- Direct consequence: `linear-kernel-self-nonneg` ($\|x\|^2 \ge 0$).

## Prerequisites (Bach's dependency graph)

- [`linear-kernel`](./linear-kernel.md) — Linear kernel k(x,y) = ⟨x, y⟩ on ℝᵈ

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/Kernel.lean`
- **Theorem/def name:** `linearKernel_self`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

