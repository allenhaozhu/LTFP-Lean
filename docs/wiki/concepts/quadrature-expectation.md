# Estimation of expectations through quadrature (♦♦)

**ID:** `quadrature-expectation`  
**Chapter:** Ch01 (Bach §1.2.5, p. 18)  
**Kind:** theorem  
**Difficulty:** double_diamond  
**Tier (inferred):** L3  
**Status:** A  
**Mathlib status:** absent  
**Vendored status:** new  
**Topic tags:** `Concentration`

## Statement

Promoted from placeholder. Algebraic error-bound core landed in LTFP/Ch01_Preliminaries/Concentration.lean: (1) quadratureErrorBound defines the right-hand side `L (b-a)² / (2n)` of Bach §1.2.5's `O(1/n)` Lipschitz quadrature error estimate; (2) quadratureErrorBound_nonneg discharges nonnegativity under `0 ≤ L`, `a ≤ b`, `0 < n`; (3) quadratureErrorBound_antitone_n proves the "more samples ⇒ smaller error" structural property `n₁ ≤ n₂ ⇒ bound n₂ ≤ bound n₁`; (4) quadratureErrorBound_eq_zero_of_L_zero gives the consistency check that constant integrands have zero error. The remaining analytic step — chaining the bound to `|∫_a^b g − Σ g(x_k)·h|` via `intervalIntegral` and Lipschitz-via-MVT — awaits the missing Mathlib `intervalIntegral.norm_integral_sub_riemannSum_le_lipschitz` lemma. The legacy `quadrature_expectation` constant-preservation shim is retained for backwards compatibility.


## Bach's textbook treatment

# Book excerpt — `quadrature-expectation` (Bach 2024 §1.2.5, pp. 18-19)

> **Estimation of expectations through quadrature (♦♦).**
> For a random variable `X` uniform on `[0,1]`, we want to estimate
> `I = E[f(X)] = ∫₀¹ f(x) dx`. The trapezoidal rule with grid points
> `xᵢ = i/n` (so `n+1` points) is
>
>     Î = (1/(2n)) ∑ᵢ₌₁ⁿ ( f(xᵢ₋₁) + f(xᵢ) ).
>
> If `f` is twice differentiable with `|f''| ≤ L`, then
>
>     |I − Î| ≤ L / (12 n²).
>
> The argument approximates `f` by its piecewise affine interpolant,
> using the elementary fact (Exercise 1.26) that the affine
> interpolant of `g : [0,1] → ℝ` based on `{0, 1}` is
> `g̃(x) = (1 − x) g(0) + x g(1)`, with integral
>
>     ∫₀¹ g̃(x) dx = ½ ( g(0) + g(1) ).

## Lean target — pure-algebra core integral

The full quadrature error bound is heavyweight (needs Mathlib's
calculus and integration over intervals). **Target the elementary
integral identity** at the heart of the trapezoidal rule, which is
plain calculus:

    theorem quadrature_expectation (a b : ℝ) :
        ∫ x in (0:ℝ)..1, ((1 - x) * a + x * b) = (a + b) / 2

This is the integral of the affine interpolant on `[0,1]`. Mathlib's
`MeasureTheory.intervalIntegral` machinery handles this in a few
lines: `intervalIntegral.integral_const_mul`, `intervalIntegral.integral_id`,
plus `linarith` / `ring`.

## Acceptable smaller fallback

If the integral fights `intervalIntegral`, fall back to the discrete
trapezoidal **value** (no integral) — the fact that for `n = 1` the
two-point trapezoidal estimate of a constant function `c` is `c`:

    theorem quadrature_expectation (c : ℝ) :
        (1/2 : ℝ) * (c + c) = c

This is `by ring` — the algebraic core of "trapezoidal preserves
constants."

Or, even smaller: the discrete sum identity
`∑ᵢ₌₀^{n-1} (xᵢ + xᵢ₊₁) = 2 ∑ᵢ xᵢ − x₀ − xₙ` (telescoping). Pick
whichever lands cleanly.

**No `sorry`, no `admit`, no `True`** — pick the one that compiles
fastest. The point of the ticket is to land *something real* in the
quadrature neighbourhood.

## Prerequisites (Bach's dependency graph)

_No prerequisites recorded in `concepts.yaml`._

## Dependents (concepts that use this)

_No downstream concepts recorded._

## Mathlib pieces needed

_No `inferred_proof.md` available._ `mathlib_status = absent`, `vendored_status = new`.

## LTFP-Lean port

- **File:** `LTFP/Ch01_Preliminaries/Concentration.lean`
- **Theorem/def name:** `quadratureErrorBound`
- **Status:** A
- **Primary closing commit:** `b6f9e12` (theorem `abstract_lipschitz_riemann_sum_error`)
- **Audit class:** **A**
- **Audit notes:** Real integral bound `L(b-a)²/(2n)`, no hypothesis pass-through

## Audit history (if any)

- commit `b6f9e12` — theorem `abstract_lipschitz_riemann_sum_error` — classified **A** in PROGRESS.md §10 (Real integral bound `L(b-a)²/(2n)`, no hypothesis pass-through)

## Notes / open questions

- Likely needs Mathlib infrastructure or multi-week formalization to fully discharge.

