/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.Moments.BernsteinTextbook

/-!
# LTlib example — Bach §1.2.3 Bernstein inequality (textbook-strict)

This file is a *worked walkthrough* of the textbook-strict Bernstein
tail bound carried by
`ProbabilityTheory.bach_bernstein_tail_one_sided` and its symmetric
companion `ProbabilityTheory.bach_bernstein_tail_two_sided`, both
landed in `LTFP/MathlibExt/Probability/Moments/BernsteinTextbook.lean`.

It is **pedagogical**: every `example` here unfolds the **named carrier
theorem** at a concrete shape, with rich inline commentary tying each
step back to Bach's textbook proof (Bach 2024, *Learning Theory from
First Principles*, §1.2.3, pp. 14-15).

## How to read this file

Open it in VS Code with the Lean 4 extension. Place the cursor on each
`example`, `#check`, or `exact` and the infoview shows the goal at that
step. The reading load is sized for one ≈1-hour session.

## Bach's proof of the Bernstein tail (book pp. 14-15)

Bach proves the Bernstein inequality from three textbook lemmas:

* **Lemma 1.2.3(a) — Taylor-expansion MGF** (`bach_taylor_mgf`).
  For a centered random variable `Z` with `|Z| ≤ c` almost surely and
  variance `σ² := ∫ Z² dμ`, and any real `s` with `|s|·c < 3`,
    `∫ exp(s·Z) dμ  ≤  exp( s² σ² / (2 (1 − |s|·c/3)) )`.
  *Proof sketch.* Apply the scalar Bennett-Bernstein remainder bound
  (`Real.exp_le_one_add_self_add_sq_div_of_abs_le`, formalised in
  `LTFP.MathlibExt.Analysis.Exp.BernsteinRemainder`) pointwise at
  `y := s·Z(ω)` and `b := |s|·c`. Integrate; centering kills the
  linear term, and `∫ Z² = σ²` gives the displayed RHS. Conclude with
  `1 + α ≤ exp α`.

* **iid Sum MGF** (`bach_taylor_mgf_iid_sum`). For iid centered `Zᵢ`
  with the same `c`, `σ²`, the MGF of the sum factors:
    `mgf (∑ Zᵢ, s)  ≤  exp( n · s² σ² / (2 (1 − |s|·c/3)) )`.

* **Chernoff optimisation.** Apply
  `ProbabilityTheory.measure_ge_le_exp_mul_mgf` (the Chernoff bound)
  and choose `s := ε / (n σ² + c ε/3)`. The exponent collapses to
    `−ε² / (2 (n σ² + c ε / 3))`.

The end product is `bach_bernstein_tail_one_sided` below; the
symmetric version applies it to `Z` and `−Z` plus a union bound.

## The carrier theorems used

```text
ProbabilityTheory.bach_bernstein_tail_one_sided
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n : ℕ} (hn : 0 < n) (Z : Fin n → Ω → ℝ)
  (h_indep : iIndepFun Z μ) (h_meas : ∀ i, Measurable (Z i))
  (c : ℝ) (hc : 0 ≤ c) (h_bdd : ∀ i, ∀ᵐ ω ∂μ, |Z i ω| ≤ c)
  (h_centered : ∀ i, ∫ ω, Z i ω ∂μ = 0)
  (sigma2 : ℝ) (hsigma2_pos : 0 < sigma2)
  (h_ident : ∀ i, sigma2 = ∫ ω, (Z i ω) ^ 2 ∂μ)
  (ε : ℝ) (hε : 0 < ε) :
    μ.real {ω | ε ≤ ∑ i : Fin n, Z i ω} ≤
      Real.exp (-ε ^ 2 / (2 * ((n : ℝ) * sigma2 + c * ε / 3)))
```

Read this as: "Under Bach's hypotheses, the probability that the
centered sum exceeds `ε` is at most the Bernstein-exponent
`exp(−ε² / (2(nσ² + cε/3)))`."

The two-sided version replaces `ε ≤ ∑ Zᵢ` with `ε ≤ |∑ Zᵢ|` and
multiplies the bound by `2`.

-/

open MeasureTheory ProbabilityTheory

namespace LTFP.Examples.Bernstein

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-! ### Step 1 — Sanity-check the named carriers exist with the
expected signature. -/

-- The per-summand textbook-strict Taylor MGF bound (Bach Lemma 1.2.3(a)).
#check @bach_taylor_mgf

-- The iid-sum upgrade (book Eq. between 1.2.3(a) and the Bernstein
-- displayed bound).
#check @bach_taylor_mgf_iid_sum

-- The Bernstein tail itself (one-sided).
#check @bach_bernstein_tail_one_sided

-- The symmetric two-sided form.
#check @bach_bernstein_tail_two_sided

/-! ### Step 2 — Concrete one-sided Bernstein tail.

We instantiate `bach_bernstein_tail_one_sided` at a generic
probability space, leaving the *quantitative* hypotheses (`c`, `σ²`,
`ε`, the `n` iid centered random variables) as `example` parameters.
The whole proof is one line — `exact` the carrier — because the
carrier already encapsulates Bach's full proof.

Read this `example` as the **statement** of Bach's Bernstein
inequality, with the proof outsourced to the named theorem.
-/

example
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n) (Z : Fin n → Ω → ℝ)
    (h_indep : iIndepFun Z μ) (h_meas : ∀ i, Measurable (Z i))
    (c : ℝ) (hc : 0 ≤ c)
    (h_bdd : ∀ i, ∀ᵐ ω ∂μ, |Z i ω| ≤ c)
    (h_centered : ∀ i, ∫ ω, Z i ω ∂μ = 0)
    (sigma2 : ℝ) (hsigma2_pos : 0 < sigma2)
    (h_ident : ∀ i, sigma2 = ∫ ω, (Z i ω) ^ 2 ∂μ)
    (ε : ℝ) (hε : 0 < ε) :
    μ.real {ω | (ε : ℝ) ≤ ∑ i : Fin n, Z i ω} ≤
      Real.exp (-ε ^ 2 /
        (2 * ((n : ℝ) * sigma2 + c * ε / 3))) := by
  -- The textbook proof — Taylor-expansion MGF → iid product → optimal
  -- Chernoff — is fully encapsulated by the named carrier. We invoke
  -- it in one line. Cursor on `bach_bernstein_tail_one_sided` and the
  -- infoview shows the exact 12-hypothesis signature documented above.
  exact bach_bernstein_tail_one_sided hn Z h_indep h_meas c hc h_bdd
    h_centered sigma2 hsigma2_pos h_ident ε hε

/-! ### Step 3 — Concrete two-sided Bernstein tail.

The two-sided version applies the one-sided form to `Z` and `(-Z)`,
each of which satisfies the same hypotheses up to negation of
centering and equality of variance. A union bound on
`{|S| ≥ ε} ⊆ {S ≥ ε} ∪ {−S ≥ ε}` doubles the bound — hence the
familiar factor of `2` in the textbook statement.

The carrier `bach_bernstein_tail_two_sided` does all of this; we again
discharge in one line.
-/

example
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n) (Z : Fin n → Ω → ℝ)
    (h_indep : iIndepFun Z μ) (h_meas : ∀ i, Measurable (Z i))
    (c : ℝ) (hc : 0 ≤ c)
    (h_bdd : ∀ i, ∀ᵐ ω ∂μ, |Z i ω| ≤ c)
    (h_centered : ∀ i, ∫ ω, Z i ω ∂μ = 0)
    (sigma2 : ℝ) (hsigma2_pos : 0 < sigma2)
    (h_ident : ∀ i, sigma2 = ∫ ω, (Z i ω) ^ 2 ∂μ)
    (ε : ℝ) (hε : 0 < ε) :
    μ.real {ω | (ε : ℝ) ≤ |∑ i : Fin n, Z i ω|} ≤
      2 * Real.exp (-ε ^ 2 /
        (2 * ((n : ℝ) * sigma2 + c * ε / 3))) := by
  -- Single-line discharge — note the `2 *` factor on the RHS
  -- corresponds to the union bound `μ{|S|≥ε} ≤ μ{S≥ε} + μ{-S≥ε}`.
  exact bach_bernstein_tail_two_sided hn Z h_indep h_meas c hc h_bdd
    h_centered sigma2 hsigma2_pos h_ident ε hε

/-! ### Step 4 — The textbook MGF lemma (Bach Lemma 1.2.3(a)).

For pedagogy we also walk through the **single-variable** MGF lemma
that underlies the tail bound. This is Bach's central per-summand
estimate; the iid product and Chernoff are routine on top of it.

Note the regime hypothesis `|s|·c < 3` — the `3` is Bach's relaxation
constant from the geometric `(m+2)! ≥ 2·3^m` tail bound used in
`BernsteinRemainder.lean`.
-/

example
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (hZ_meas : Measurable Z)
    (c : ℝ) (hc : 0 ≤ c)
    (h_bdd : ∀ᵐ ω ∂μ, |Z ω| ≤ c)
    (h_centered : ∫ ω, Z ω ∂μ = 0)
    (sigma2 : ℝ) (hsigma2_def : sigma2 = ∫ ω, (Z ω) ^ 2 ∂μ)
    (s : ℝ) (hsc : |s| * c < 3) :
    ∫ ω, Real.exp (s * Z ω) ∂μ ≤
      Real.exp (s ^ 2 * sigma2 / (2 * (1 - |s| * c / 3))) := by
  -- This is Bach's textbook-strict Lemma 1.2.3(a). The proof in
  -- `BernsteinTextbook.lean` is the textbook Taylor-expansion +
  -- Bochner-integrate + `1 + α ≤ exp α` argument.
  exact bach_taylor_mgf Z hZ_meas c hc h_bdd h_centered sigma2
    hsigma2_def s hsc

end LTFP.Examples.Bernstein
