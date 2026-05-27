# Kernel expansion definitional

**ID:** `kernel-expansion-eq`  
**Chapter:** Ch07 (Bach §7.2)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Kernel`

## Statement

_See textbook excerpt below or [`tasks/kernel-expansion-eq/`](../../../tasks/kernel-expansion-eq/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Kernel expansion definitional

**Concept ID:** `kernel-expansion-eq`
**Chapter:** Ch 7
**Section:** §7.2 (Representer Theorem)
**Pages:** 182 (book) / PDF p. 198
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Definitional rewrite for the kernel expansion: for any $\alpha \in \mathbb{R}^n$, training inputs $x_1, \dots, x_n$, kernel $k$, and test point $x$,

$$\text{kernelExpansion}(\alpha, k, (x_i), x) = \sum_{i=1}^n \alpha_i \, k(x, x_i).$$

## Proof (verbatim)

This is the **defining equation** of $f_\alpha$, taken straight from Bach p. 182:

"*Note that for any test point $x \in \mathcal{X}$, we have defined the prediction function as*
$f(x) = \langle\theta, \phi(x)\rangle = \sum_{i=1}^n \alpha_i \langle\phi(x_i), \phi(x)\rangle = \sum_{i=1}^n \alpha_i k(x, x_i).$"

(By definition.)

## Notes

- Lean form `kernelExpansion_eq` (or the `simp` lemma form) in `LTFP/Ch07_Kernels/Representer.lean`.
- "Sanity-check" definitional lemma; useful as a `simp` rule to unfold `kernelExpansion`.
- Underpins every other theorem about the predictor.

## Prerequisites (Bach's dependency graph)

- [`kernel-expansion`](./kernel-expansion.md) — Kernel-expansion predictor f(x) = ∑ᵢ αᵢ k(x, xᵢ)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch07_Kernels/Representer.lean`
- **Theorem/def name:** `kernelExpansion_eq`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

