# Cauchy-Schwarz reflexive anchor (a·a = a²)

**ID:** `cauchy-schwarz-anchor`  
**Chapter:** Ch05 (Bach §F9)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/cauchy-schwarz-anchor/`](../../../tasks/cauchy-schwarz-anchor/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Cauchy-Schwarz reflexive anchor (a·a = a²)

**Concept ID:** `cauchy-schwarz-anchor`
**Chapter:** Ch 5
**Section:** §5.4 / Foundation F9 (algebraic anchor)
**Pages:** N/A — used implicitly throughout proofs of 5.3, 5.5, 5.7
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

The trivial reflexive Cauchy-Schwarz identity in $\mathbb{R}$ (or in any
inner-product space, projected to the scalar case):
$$a \cdot a = a^2, \qquad \forall a \in \mathbb{R}.$$
This is the "anchor" instance of Cauchy-Schwarz $|\langle a,b\rangle| \le \|a\|\|b\|$
with $a = b$, which becomes equality.

Bach uses this implicitly whenever he expands an inner product
$F'(\theta)^\top F'(\theta) = \|F'(\theta)\|_2^2$ in convergence proofs — for
example in the descent inequality derivation
$F(\theta_t) \le F(\theta_{t-1}) - \tfrac{1}{2L}\|F'(\theta_{t-1})\|_2^2$
(PDF p. 138).

## Proof (verbatim)

Algebraic: in $\mathbb{R}$, $a \cdot a = a^2$ is a defining property of squaring;
in $\mathbb{R}^d$, $\langle v,v\rangle = \|v\|_2^2$ is the definition of the
$\ell_2$-norm.

## Notes

- This is a sanity-check / type-alignment lemma rather than a deep theorem.
- Lean form: `a * a = a^2` (or `inner v v = ‖v‖²` in the vector case).
- Used to rewrite $F'(\theta)^\top F'(\theta)$ to $\|F'(\theta)\|_2^2$ when
  matching Mathlib's `norm_sq` vs. inner-product spellings.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Foundations/MeasureProb.lean`
- **Theorem/def name:** `cauchy_schwarz_reflexive_anchor`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

