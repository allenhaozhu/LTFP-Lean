# ℓ₁ norm satisfies the triangle inequality

**ID:** `l1-triangle`  
**Chapter:** Ch08 (Bach §8.3, p. 231)  
**Kind:** theorem  
**Difficulty:** core  
**Tier (inferred):** L2  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** _(none)_

## Statement

_See textbook excerpt below or [`tasks/l1-triangle/`](../../../tasks/l1-triangle/) if available._

## Bach's textbook treatment

# Bach textbook excerpt — ℓ₁ norm satisfies the triangle inequality

**Concept ID:** `l1-triangle`
**Chapter:** Ch 8
**Section:** §8.3
**Pages:** 230 (definition page); used in lemma 8.4 proof p. 236, lemma 8.5 proof p. 238
**Source:** Bach (2024), *Learning Theory from First Principles*

## Statement

Bach uses the triangle inequality for ‖·‖₁ implicitly throughout §8.3.
Explicit usage in the proof of Lemma 8.4 (p. 236):

> Then, with the dual norm Ω*(z) = sup_{Ω(θ)≤1} zᵀθ, assuming that Ω*(Φᵀε) ≤ nλ/2 and **using the triangle inequality**,
>   ‖Φ(θ̂ − θ\*)‖₂² ≤ 2Ω*(Φᵀε)Ω(θ̂ − θ\*) + 2nλΩ(θ\*) − 2nλΩ(θ̂)
>                  ≤ nλΩ(θ̂ − θ\*) + 2nλΩ(θ\*) − 2nλΩ(θ̂)
>                  ≤ nλΩ(θ̂) + nλΩ(θ\*) + 2nλΩ(θ\*) − 2nλΩ(θ̂).

Here Ω = ‖·‖₁, and the triangle inequality Ω(θ̂ − θ\*) ≤ Ω(θ̂) + Ω(θ\*) is invoked.

Also used implicitly via the decomposability of ‖·‖₁ in the proof of Lemma 8.5 (p. 238):

> ‖θ\*‖₁ − ‖θ̂‖₁ = ‖(θ\*)_A‖₁ − ‖θ\* + ∆‖₁ = ‖(θ\*)_A‖₁ − ‖(θ\* + ∆)_A‖₁ − ‖∆_{Aᶜ}‖₁ ≤ ‖∆_A‖₁ − ‖∆_{Aᶜ}‖₁.

## Proof (verbatim)

(sketch) — Bach does not give a separate proof. Standard one-liner:
the triangle inequality for ‖·‖₁ reduces to |a + b| ≤ |a| + |b|
applied coordinate-wise and summed: ‖θ + φ‖₁ = Σⱼ |θⱼ + φⱼ| ≤
Σⱼ (|θⱼ| + |φⱼ|) = ‖θ‖₁ + ‖φ‖₁.

## Notes

- Foundational lemma, used silently throughout §8.3 (notably in the
  proof of Lemma 8.4 — the slow-rate Lasso bound).
- Bach's proof technique (n/a — standard).
- Lean target `LTFP/Ch08_Sparse/L1.lean#l1Norm_add_le`.
- Sister concept `l1-norm-triangle` is the named alias of the same
  statement.

## Prerequisites (Bach's dependency graph)

- [`l1-norm`](./l1-norm.md) — ℓ₁ norm: sum of absolute values

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch08_Sparse/L1.lean`
- **Theorem/def name:** `l1Norm_add_le`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

_(none flagged)_

