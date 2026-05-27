# Matrix Bernstein / matrix concentration (♦♦)

**ID:** `matrix-concentration`  
**Chapter:** Ch01 (Bach §1.2.6, p. 19)  
**Kind:** theorem  
**Difficulty:** double_diamond  
**Tier (inferred):** L3  
**Status:** Deferred  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Concentration`, `Matrix/LinAlg`

## Statement

Promoted from transpose-additivity placeholder to the real algebraic dimension-factor core of Tropp's matrix Bernstein bound (Bach 2024 Prop. 1.7, p. 19). We define `matrix_bernstein_bound d t σ² R := 2 d · exp(-(t²/2)/(σ² + R t / 3))` as the right-hand side of the tail bound and prove three structural properties: (a) the bound is pointwise nonnegative (`matrix_bernstein_bound_nonneg`), (b) it is monotone increasing in the ambient dimension `d` (`matrix_bernstein_bound_mono_d`), and (c) it reduces to the scalar Bernstein form `2 · exp(...)` at `d = 1` (`matrix_bernstein_bound_reduces_scalar_at_d_eq_one`), giving the consistency check with the scalar Bernstein bound earlier in §1.2.3. We also record `matrix_bernstein_exponent_nonneg`, the deterministic exponent-positivity skeleton mirroring `bernstein_inequality`. The Lieb-concavity-based MGF chain (Tropp 2015 §3-§6) connecting these algebraic facts to the probabilistic statement `P(‖∑ Xᵢ‖ ≥ t) ≤ matrix_bernstein_bound d t σ² R` remains a documented Mathlib gap; the legacy `matrix_bernstein` transpose identity is retained for backwards compatibility.

## Bach's textbook treatment

# Book excerpt — `matrix-concentration` (Bach 2024 §1.2.6, pp. 19-20)

> **Concentration Inequalities for Random Matrices (♦♦).** The
> concentration results of this chapter extend to symmetric matrices
> with the positive-semidefinite order. Notation: `λ_max(M)` is the
> largest eigenvalue of `M`; `‖M‖_op` is the largest singular value;
> `A ≼ B` iff `B − A` is PSD.
>
> **Proposition 1.6 (Matrix Hoeffding bound, Tropp 2012, thm 1.3).**
> Given `n` indep symmetric matrices `Mᵢ ∈ ℝᵈˣᵈ` with `E[Mᵢ] = 0`,
> `Mᵢ² ≼ Cᵢ²` a.s., and `σ² = λ_max((1/n) ∑ᵢ Cᵢ²)`. Then for `t ≥ 0`,
>
>     P(λ_max((1/n) ∑ᵢ Mᵢ) ≥ t) ≤ d · exp(- n t² / (8 σ²)).
>
> **Proposition 1.7 (Matrix Bernstein bound, Tropp 2012, thm 1.4).**
> Given `n` indep symmetric `Mᵢ ∈ ℝᵈˣᵈ` with `E[Mᵢ] = 0`,
> `λ_max(Mᵢ) ≤ c` a.s., and `σ² = λ_max((1/n) ∑ᵢ E[Mᵢ²])`. Then
>
>     P(λ_max((1/n) ∑ᵢ Mᵢ) ≥ t) ≤ d · exp(- n t² / 2 / (σ² + c t / 3)).

## Lean target — pure-algebra core (operator norm subadditivity)

The full Tropp matrix Bernstein/Hoeffding theorems require Mathlib
machinery that **does not exist** for matrix concentration. **Target
the pure-linear-algebra core fact** used implicitly throughout matrix
concentration: subadditivity of the operator norm
`‖A + B‖_op ≤ ‖A‖_op + ‖B‖_op`, which Mathlib has via the
`NormedAddGroup` instance.

    theorem matrix_bernstein {d : ℕ}
        (A B : Matrix (Fin d) (Fin d) ℝ) :
        ‖A + B‖ ≤ ‖A‖ + ‖B‖

This is just `norm_add_le` applied to the matrix's `NormedAddGroup`
instance — one line.

## Acceptable smaller fallback

If even the operator-norm subadditivity is awkward (typeclass
issues), fall back to the **deterministic algebraic identity**
`(M₁ + M₂)ᵀ = M₁ᵀ + M₂ᵀ` (transpose distributes over addition),
which Mathlib has as `Matrix.transpose_add`:

    theorem matrix_bernstein {d : ℕ}
        (A B : Matrix (Fin d) (Fin d) ℝ) :
        (A + B)ᵀ = Aᵀ + Bᵀ

Or even smaller — the trace identity `tr(A + B) = tr A + tr B`
via `Matrix.trace_add`.

**No `sorry`, no `admit`, no `True`** — pick whichever lands cleanest.
The point of the ticket is to land *something real* in the
matrix-concentration neighbourhood; the full Tropp theorems are a
multi-month project deferred indefinitely.

## Prerequisites (Bach's dependency graph)

- [`bernstein-inequality`](./bernstein-inequality.md) — Bernstein's inequality (♦)

## Dependents (concepts that use this)

- [`operator-monotone-fn`](./operator-monotone-fn.md) — Operator-monotone / operator-concave functions on Hermitian CFC (L1)

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch01_Preliminaries/Concentration.lean`
- **Theorem/def name:** `matrix_bernstein_bound`
- **Status:** Deferred
- **Closing commit:** _not recorded in PROGRESS.md §10 audit_

## Audit history (if any)

_No audit history recorded._

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

