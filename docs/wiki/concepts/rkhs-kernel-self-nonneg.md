# RKHS kernel self-evaluation is nonneg

**ID:** `rkhs-kernel-self-nonneg`  
**Chapter:** Ch07 (Bach §F4b)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** `RKHS`, `Kernel`, `Neural-network`

## Statement

_See textbook excerpt below or [`tasks/rkhs-kernel-self-nonneg/`](../../../tasks/rkhs-kernel-self-nonneg/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — RKHS kernel self-evaluation is nonneg

**Concept ID:** `rkhs-kernel-self-nonneg`
**Chapter:** Ch 7
**Section:** §7.3 (Kernels) / Foundation F4b
**Pages:** 183-184, 196 (book) / PDF pp. 199-200, 212
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

For any positive-definite kernel $k$ on $\mathcal{X}$ with feature map $\phi : \mathcal{X} \to \mathcal{H}$ and any $x \in \mathcal{X}$,

$$k(x, x) = \langle\phi(x), \phi(x)\rangle_\mathcal{H} = \|\phi(x)\|_\mathcal{H}^2 \ge 0.$$

## Proof (verbatim)

Bach uses this identity throughout but does not isolate it as a lemma. The boundedness assumption in §7.4 (p. 196) writes it explicitly:

"We assume that features are bounded; that is, for all $i \in \{1, \dots, n\}$, $k(x_i, x_i) = \|\phi(x_i)\|_\mathcal{H}^2 \le R^2$."

The chain $k(x,x) = \langle\phi(x),\phi(x)\rangle = \|\phi(x)\|^2 \ge 0$ uses (i) the kernel-feature-map identity (Proposition 7.3, p. 183), (ii) the definition of the Hilbert norm $\|v\|^2 = \langle v, v\rangle$, and (iii) positivity of the norm. (Sketch.)

## Notes

- Lean form `RKHS.kernel_self_nonneg` in `LTFP/Foundations/RKHS.lean`.
- Marked `mathlib_status: in_mathlib` in the registry — Mathlib's `inner_self_nonneg` gives this directly once the kernel is expressed via the feature map.
- This is the abstract version of `linear-kernel-self-nonneg`; both reduce to "$\|v\|^2 \ge 0$" once Aronszajn's representation is invoked.
- Used in §7.4 to make the boundedness assumption $k(x_i, x_i) \le R^2$ meaningful.

## Prerequisites (Bach's dependency graph)

- [`rkhs-foundation`](./rkhs-foundation.md) — RKHS foundation: real Hilbert space + feature map

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/RKHS.lean`
- **Theorem/def name:** `RKHS.kernel_self_nonneg`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

