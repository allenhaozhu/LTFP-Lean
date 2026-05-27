# Lieb 1973 joint concavity of `(A,B) ↦ tr(K* A^p K B^q)` (L3)

**ID:** `lieb-concavity-joint`  
**Chapter:** Ch01 (Bach §1.2.6, p. 19)  
**Kind:** theorem  
**Difficulty:** double_diamond  
**Tier (inferred):** L3  
**Status:** pending  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Matrix/LinAlg`

## Statement

Node L3 of the B6 decomposition. The actual Lieb theorem: for `K` fixed and `p, q > 0` with `p+q ≤ 1`, the map `(A, B) ↦ tr(K* A^p K B^q)` is jointly concave on positive operators. Carlen 2010 surveys two proofs (Ando 1979 via operator means; Epstein 1973 via complex analysis); Ando route is the Mathlib-shaped target. Implies the trace-exponential form `(H, K) ↦ tr exp(H + log K)` jointly concave, which is what Tropp 2012 matrix-MGF subadditivity uses. The existing `liebScalar` placeholder in `LTFP/MathlibExt/MatrixAnalysis/Lieb.lean` is the scalar (dim-1) shadow of this; the joint multivariate form is the residual. Estimated ~2 weeks focused work on top of L1+L2.


## Bach's textbook treatment

_No book excerpt available._ See [`tasks/lieb-concavity-joint/`](../../../tasks/lieb-concavity-joint/) if a context kit has been built, or generate one with `python -m tools.context_kit`.

## Prerequisites (Bach's dependency graph)

- [`operator-monotone-fn`](./operator-monotone-fn.md) — Operator-monotone / operator-concave functions on Hermitian CFC (L1)

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `TBD`
- **Theorem/def name:** `lieb_concavity_joint`
- **Status:** pending
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.
- **No verified book excerpt** — verify before citing this concept by a textbook equation number; equation labels in synthesized notes can drift relative to the canonical Bach (2024) PDF.

