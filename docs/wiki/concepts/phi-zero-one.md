# Margin-based 0-1 surrogate Φ_{0-1}(u) = 1[u ≤ 0]

**ID:** `phi-zero-one`  
**Chapter:** Ch04 (Bach §4.1.4, p. 76)  
**Kind:** definition  
**Difficulty:** core  
**Tier (inferred):** L1  
**Status:** (unaudited)  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/phi-zero-one/`](../../../tasks/phi-zero-one/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — Margin-based 0-1 surrogate Φ_{0-1}(u) = 1[u ≤ 0]

**Concept ID:** `phi-zero-one`
**Chapter:** Ch 4
**Section:** 4.1 (eq. 4.1) — context 4.1.4 for "margin-based" name
**Pages:** 72-73, 76
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement
The 0–1 risk of function f = sign ∘ g, denoted R(g), equals

$$R(g) = \mathbb{P}(f(x) \ne y) = \mathbb{E}[\mathbf 1_{g(x)\ne 0}\mathbf 1_{f(x)\ne y}] + \tfrac{1}{2}\,\mathbb{E}[\mathbf 1_{g(x)=0}]
= \mathbb{E}\big[\Phi_{0-1}(y g(x))\big],$$

where the margin-based 0–1 loss Φ_{0-1} : R → R is defined by
$$\Phi_{0-1}(u) = \begin{cases} 1 & \text{if } u < 0, \\ \tfrac{1}{2} & \text{if } u = 0, \\ 0 & \text{if } u > 0. \end{cases} \qquad (4.1)$$

This is "called the 'margin-based' 0–1 loss function or simply the 0–1 loss function."

## Proof (verbatim)
"Note the slightly overloaded notation where the 0–1 loss function is defined on R, compared
to the 0–1 loss function from chapter 2, which is defined on {−1, 1} × {−1, 1}."

The derivation of R(g) = E[Φ_{0-1}(y g(x))]:
"The 0–1 risk of function f = sign ∘ g, still denoted as R(g), is then equal to, separating
between situations where g(x) = 0 or not,
R(g) = P(f(x) ≠ y) = E[1_{g(x) ≠ 0} 1_{f(x) ≠ y}] + E[1_{g(x) = 0} 1_{f(x) ≠ y}]
     = E[1_{yg(x) < 0}] + (1/2) E[1_{g(x) = 0}] = E[Φ_{0-1}(y g(x))]."

## Notes
- Three-valued: 1 for misclassified, 0 for well-classified, 1/2 at u = 0 (random tie-break).
- The 1/2 convention preserves symmetry between y = +1 and y = −1.
- Non-convex and non-continuous — motivates the convex surrogates Φ ∈ {square, hinge, logistic, exp}.
- Used as the right-hand side of "margin bounds" Φ_{0-1}(u) ≤ Φ(u) (e.g., `phi-zero-one-le-hinge`).

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

- [`phi-zero-one-le-hinge`](./phi-zero-one-le-hinge.md) — Hinge upper-bounds 0-1 surrogate (margin bound)

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch04_ERM/Convexification.lean`
- **Theorem/def name:** `phiZeroOne`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

