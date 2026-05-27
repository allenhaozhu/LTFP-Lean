# Block matrix inversion (Schur complement / Woodbury)

**ID:** `block-matrix-inversion`  
**Chapter:** Ch01 (Bach §1.1.3, p. 5)  
**Kind:** lemma  
**Difficulty:** core  
**Tier (inferred):** L3  
**Status:** (unaudited)  
**Mathlib status:** in_mathlib  
**Vendored status:** new  
**Topic tags:** `Matrix/LinAlg`

## Statement

_See textbook excerpt below or [`tasks/block-matrix-inversion/`](../../../tasks/block-matrix-inversion/) if available._

## Bach's textbook treatment

# Book excerpt — `block-matrix-inversion` (Bach 2024 §1.1.3, pp. 4-5)

> Given a 2×2 block matrix `M = [[A, B], [C, D]]` with `A` and `D`
> square and `A` invertible, write `M/A := D − C A⁻¹ B` (the Schur
> complement of `A`). If `M/A` is also invertible, then so is `M`
> and Gaussian elimination yields
>
>   `M⁻¹ = ⎡ A⁻¹ + A⁻¹ B (M/A)⁻¹ C A⁻¹    −A⁻¹ B (M/A)⁻¹ ⎤`
>          `⎣ −(M/A)⁻¹ C A⁻¹              (M/A)⁻¹       ⎦`
>
> Comparing this against the analogous formula obtained by first zeroing
> the upper-right block yields the **Woodbury identities**:
>
>   `(A − B D⁻¹ C)⁻¹ = A⁻¹ + A⁻¹ B (D − C A⁻¹ B)⁻¹ C A⁻¹`
>   `(D − C A⁻¹ B)⁻¹ = D⁻¹ + D⁻¹ C (A − B D⁻¹ C)⁻¹ B D⁻¹`
>
> A particularly common form arises with `C = Bᵀ`, `A = I`, `D = -I`:
>
>   `(I + B Bᵀ)⁻¹ = I − B (I + Bᵀ B)⁻¹ Bᵀ`,                 (1.3)
>
> and right-multiplying (1.3) by `B` yields the compact form
>
>   `(I + B Bᵀ)⁻¹ B = B (I + Bᵀ B)⁻¹`.

## Lean target

The compact identity is the cleanest core fact and easiest to formalize:

    theorem block_matrix_inv {m n : ℕ}
        (B : Matrix (Fin m) (Fin n) ℝ)
        (hL : IsUnit (1 + B * Bᵀ).det)
        (hR : IsUnit (1 + Bᵀ * B).det) :
        (1 + B * Bᵀ)⁻¹ * B = B * (1 + Bᵀ * B)⁻¹

## Acceptable smaller fallback

If the compact identity fights Mathlib too hard, fall back to either
- a fixed small dimension (e.g. `n = 1`) version of the same identity,
- a Schur-complement identity already in Mathlib's
  `Matrix.SchurComplement` family (re-state and re-prove with one
  `Matrix.fromBlocks*` lemma), OR
- the simple but real fact
    `(1 + B * Bᵀ)⁻¹ * (1 + B * Bᵀ) = 1`
  (under `IsUnit (1 + B * Bᵀ).det`), which is just
  `Matrix.nonsing_inv_mul`.

**No `sorry`, no `admit`, no `True`** — the body must contain real
Lean tactics or refer to a real Mathlib lemma.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = in_mathlib`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch01_Preliminaries/LinAlg.lean`
- **Theorem/def name:** `block_matrix_inv`
- **Status:** (unaudited)
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

