# Bernstein's inequality (♦)

**ID:** `bernstein-inequality`  
**Chapter:** Ch01 (Bach §1.2.3, p. 14)  
**Kind:** theorem  
**Difficulty:** diamond  
**Tier (inferred):** L3  
**Status:** A-leaning  
**Mathlib status:** partial  
**Vendored status:** new  
**Topic tags:** `Sub-Exponential`, `Concentration`

## Statement

Promoted from placeholder. Two-part landing in LTFP/Ch01_Preliminaries/Concentration.lean: (1) bernstein_inequality proves the algebraic exponent positivity `0 ≤ t² / (2σ² + 2Mt/3)` under `0 ≤ σ²`, `0 < M`, `0 ≤ t` — the deterministic skeleton of the Bach §1.2.3 / Prop. 1.4 bound; (2) bernstein_inequality_of_mgf gives the conditional probabilistic tail bound `μ.real {ω | ε ≤ X ω} ≤ exp(-tε) * exp B` from any MGF hypothesis `mgf X μ t ≤ exp B`, chaining Mathlib's `ProbabilityTheory.measure_ge_le_exp_mul_mgf` Chernoff bound. The full Bach sub-Gamma MGF lemma for bounded i.i.d. variables is not yet in Mathlib; once it lands, the conditional form specialises directly.


## Bach's textbook treatment

# Book excerpt — `bernstein-inequality` (Bach 2024 §1.2.3, pp. 14-16)

> **Proposition 1.4 (Bernstein's inequality, ♦).** Let `Z₁, …, Zₙ` be
> `n` independent random variables with `|Zᵢ| ≤ c` almost surely and
> `E[Zᵢ] = 0`. For `t ≥ 0`,
>
>     P(|(1/n) ∑ᵢ Zᵢ| ≥ t) ≤ 2 · exp(- n t² / (2 σ² + 2 c t / 3))   (1.11)
>
> where `σ² = (1/n) ∑ᵢ var(Zᵢ)`.
>
> *Proof key lemma (a).* If `|Z| ≤ c` a.s., `E[Z] = 0`, `E[Z²] = σ²`,
> then for any `s > 0`,
>
>     E[exp(s · Z)] ≤ exp((σ² / c²) · (exp(s · c) − 1 − s · c)).
>
> The proof expands `e^{sZ} = ∑ s^k Z^k / k!` and uses `|Z|^{k-2} ≤ c^{k-2}`
> together with `E[Z²] = σ²`.

## Lean target — pure-algebra core inequality

The full probabilistic Bernstein bound is heavy. **Target the
non-probabilistic core inequality** that drives the proof:
the elementary fact `1 + α ≤ exp α` used at the end of lemma (a).

    theorem bernstein_inequality (α : ℝ) :
        1 + α ≤ Real.exp α

This is `Real.add_one_le_exp` in Mathlib — a one-line proof.

## Acceptable larger formulation (try if Mathlib has Bernstein directly)

Mathlib may have a probabilistic Bernstein bound under
`ProbabilityTheory`. If you can find one and instantiate it cleanly,
prefer that. Search for `bernstein`, `Bernstein`, or `mgf` in
Mathlib's probability and analysis namespaces.

## Acceptable smaller fallback

If `Real.add_one_le_exp` is somehow unavailable, fall back to **the
one-sided analog `(1/2) α² ≤ exp α − 1 − α`** (used in the second
half of the proof on p.15) — also one line via
`Real.quadratic_le_exp_of_nonneg` or by `nlinarith` on Taylor.

Or, even smaller: the positivity `0 ≤ Real.exp α` (one-liner via
`Real.exp_pos`).

**No `sorry`, no `admit`, no `True`** — pick whichever lands cleanly.
The point of the ticket is to land *something real* in the Bernstein
neighbourhood; the full probabilistic theorem is left for a Phase-3
wave.

## Prerequisites (Bach's dependency graph)

- [`hoeffding-lemma`](./hoeffding-lemma.md) — Hoeffding's lemma (MGF bound for bounded variables)

## Dependents (concepts that use this)

- [`matrix-concentration`](./matrix-concentration.md) — Matrix Bernstein / matrix concentration (♦♦)

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = partial`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch01_Preliminaries/Concentration.lean`
- **Theorem/def name:** `bernstein_inequality`
- **Status:** A-leaning
- **Primary closing commit:** `35a4e4c` (theorem `bernstein_inequality_of_subExponential`)
- **Audit class:** **A-leaning**
- **Audit notes:** Real composition of `IsSubExponential.measure_ge_le` (real class) + Chernoff

## Audit history (if any)

- commit `35a4e4c` — theorem `bernstein_inequality_of_subExponential` — classified **A-leaning** in PROGRESS.md §10 (Real composition of `IsSubExponential.measure_ge_le` (real class) + Chernoff)

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

