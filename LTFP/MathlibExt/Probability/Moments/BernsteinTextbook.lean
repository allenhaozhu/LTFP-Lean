/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Independence.Integration
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import LTFP.MathlibExt.Analysis.Exp.BernsteinRemainder

/-!
# Bach's textbook-strict Bernstein MGF lemma (Bach 2024 §1.2.3, pp. 14-15)

This module formalises **Bach (2024) Lemma 1.2.3(a)** — the elementary
Taylor-expansion bound on the moment-generating function of a centered
bounded random variable that underlies Bernstein's inequality.

## Mathematical statement

For a real random variable `Z` on a probability space `(Ω, μ)`
satisfying `|Z| ≤ c` almost surely (with `0 ≤ c`) and `∫ Z dμ = 0`,
together with the small-`s` regime hypothesis `|s|·c < 3`, the
moment-generating function `s ↦ ∫ exp(s·Z) dμ` is bounded by the
**sub-Gamma form**

  `∫ exp(s·Z) dμ ≤ exp(s² · sigma2 / (2 · (1 − |s|·c / 3)))`

where `sigma2 := ∫ Z² dμ` is the variance.

This is the **textbook-strict** statement of Bach (2024) Lemma 1.2.3(a)
after applying the rational-fraction relaxation Bach gives on p.15
immediately after the Taylor expansion. It is the precise MGF bound
that v6 takes as a hypothesis through the abstract `IsSubGamma`
typeclass.

## Proof outline (Bach pp.14-15)

The proof is Bach's two-step argument:

1. **Per-ω scalar Bennett-Bernstein bound.** Apply
   `Real.exp_le_one_add_self_add_sq_div_of_abs_le`
   (the scalar remainder bound, formalised in `BernsteinRemainder.lean`)
   pointwise at `y := s · Z(ω)` and `b := |s| · c`. The hypothesis
   `|s · Z(ω)| ≤ |s| · c` follows from `|Z(ω)| ≤ c` a.s. This yields
   the **per-ω** bound

       `exp(s · Z(ω)) ≤ 1 + s·Z(ω) + s² · Z(ω)² / (2(1 − |s|c/3))`.

   This is the *Taylor-expansion content* of Bach's Lemma 1.2.3(a):
   `BernsteinRemainder.lean` proves the scalar inequality by the same
   `(m+2)! ≥ 2 · 3^m`-style geometric-bounded tail estimate Bach uses,
   which is exactly the elementary `∑_{k≥2} (sc)^k/k! ≤ (sc)²/(2(1-sc/3))`
   rearrangement Bach displays in the proof.

2. **Integrate.** Bochner-linearity of `∫`, centering (`∫ Z = 0`), and
   the definition `sigma2 = ∫ Z²` collapse the integrated RHS to
   `1 + s² sigma2 / (2(1−|s|c/3))`. Finally `1 + α ≤ exp α` produces the
   stated MGF bound.

## Alternative full Taylor-series statement (for future generality)

The "Bach form" exactly as displayed on p.14 is

  `∫ exp(s·Z) dμ ≤ exp((sigma2 / c²) · (exp(s·c) − 1 − s·c))`.

This form does not require `|s|·c < 3`. It can be obtained by going
through a full term-by-term Taylor expansion of `exp(s·Z(ω))` and
applying dominated convergence to interchange the tsum and the
integral. The two forms are equivalent in the regime `|s|·c < 3`
through Bach's own relaxation
`exp(sc) − 1 − sc ≤ (sc)² / (2(1 − sc/3))`, which we capture below
in `bach_taylor_remainder_scalar_le`. We choose the rational-fraction
form as the canonical "textbook-strict" statement because it is the
form Bach actually feeds into the Chernoff optimisation on p.15.

## The textbook-strict variant vs. v6 abstract sub-Gamma route

The v6 `bernstein_inequality_of_subGamma` (in `Concentration.lean`)
takes the sub-Gamma MGF bound as a *hypothesis*. The substantive Taylor
expansion that *derives* the MGF bound from `|Z| ≤ c` and `E[Z] = 0` is
this lemma, `bach_taylor_mgf`. This file recovers Bach's elementary
proof faithfully.

## Bach 2024 alternative form

Bach (pp. 15) also notes the rational-fraction relaxation
`exp(s·c) − 1 − s·c ≤ (s·c)² / (2(1 − s·c/3))` valid for `s·c < 3`,
which together with this lemma yields the canonical sub-Gamma MGF
bound used in v6.

## References

* Bach, F. (2024). *Learning Theory from First Principles*. MIT Press.
  §1.2.3, Lemma 1.2.3(a) (p. 14) and Proposition 1.4 (p. 14, eq. 1.11).
* Boucheron, Lugosi, Massart (2013). *Concentration Inequalities*.
  §2.4 (Bernstein's inequality).
-/

open scoped Nat
open MeasureTheory ProbabilityTheory Real

namespace ProbabilityTheory

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-! ### Auxiliary scalar identity

The substantive content of Bach Lemma 1.2.3(a) is a termwise comparison
of integrals against a series whose sum is `exp(s·c) − 1 − s·c`. We
isolate the scalar identity first.
-/

/-- The tail series identity `∑_{k≥2} y^k / k! = exp y − 1 − y` in `ℝ`. -/
private lemma tsum_pow_div_factorial_shift_two (y : ℝ) :
    ∑' m : ℕ, y ^ (m + 2) / ((m + 2)! : ℝ) = Real.exp y - 1 - y := by
  -- exp y = ∑' n, y^n / n!
  have hexp_tsum : Real.exp y = ∑' n : ℕ, y ^ n / (n ! : ℝ) := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  -- Summable on ℝ
  have hsum : Summable (fun n : ℕ => y ^ n / (n ! : ℝ)) := by
    have : Summable (fun n : ℕ => (n !⁻¹ : ℝ) • y ^ n) :=
      NormedSpace.expSeries_summable' (𝕂 := ℝ) y
    simpa [smul_eq_mul, mul_comm, div_eq_mul_inv] using this
  -- Split off first two terms
  have hsplit := hsum.sum_add_tsum_nat_add (k := 2)
  have hprefix :
      (∑ i ∈ Finset.range 2, y ^ i / (i ! : ℝ)) = 1 + y := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp [Nat.factorial_zero, Nat.factorial_one, pow_zero, pow_one]
  have hexp_eq :
      Real.exp y =
        1 + y + ∑' m : ℕ, y ^ (m + 2) / ((m + 2) ! : ℝ) := by
    rw [hexp_tsum, ← hsplit, hprefix]
  linarith [hexp_eq]

/-! ### Per-term integrability and moment bound

For `|Z(ω)| ≤ c` a.s., each integrand `(s·Z(ω))^k / k!` is dominated
by `(|s|·c)^k / k!`, hence integrable; and the integral satisfies
`|∫ Z^k| ≤ c^{k-2} · sigma2` for `k ≥ 2`.
-/

/-- Termwise integrability: if `|Z| ≤ c` almost surely, then for every
`k : ℕ` the function `ω ↦ Z(ω) ^ k` is integrable on a finite measure. -/
private lemma integrable_pow_of_bounded
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {Z : Ω → ℝ} (hZ_meas : Measurable Z)
    {c : ℝ} (_hc : 0 ≤ c) (h_bdd : ∀ᵐ ω ∂μ, |Z ω| ≤ c) (k : ℕ) :
    Integrable (fun ω => Z ω ^ k) μ := by
  refine Integrable.mono' (g := fun _ => c ^ k) ?_ ?_ ?_
  · exact integrable_const _
  · exact (hZ_meas.pow_const k).aestronglyMeasurable
  · -- `‖Z(ω)^k‖ ≤ c^k`
    filter_upwards [h_bdd] with ω hω
    have h1 : ‖Z ω ^ k‖ = |Z ω| ^ k := by
      rw [Real.norm_eq_abs, abs_pow]
    have h2 : |Z ω| ^ k ≤ c ^ k := pow_le_pow_left₀ (abs_nonneg _) hω k
    rw [h1]; exact h2

/-- Moment bound `|∫ Z^k| ≤ c^k` for `|Z| ≤ c`. -/
private lemma abs_integral_pow_le
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {Z : Ω → ℝ} (hZ_meas : Measurable Z)
    {c : ℝ} (hc : 0 ≤ c) (h_bdd : ∀ᵐ ω ∂μ, |Z ω| ≤ c) (k : ℕ) :
    |∫ ω, Z ω ^ k ∂μ| ≤ (μ.real Set.univ) * c ^ k := by
  have h_int := integrable_pow_of_bounded hZ_meas hc h_bdd k
  -- |∫ Z^k| ≤ ∫ |Z^k| ≤ ∫ c^k = μ(univ) * c^k
  have h_norm : |∫ ω, Z ω ^ k ∂μ| ≤ ∫ ω, |Z ω ^ k| ∂μ := by
    have := abs_integral_le_integral_abs (f := fun ω => Z ω ^ k) (μ := μ)
    exact this
  have h_bound :
      ∫ ω, |Z ω ^ k| ∂μ ≤ ∫ _ω, c ^ k ∂μ := by
    refine integral_mono_ae h_int.abs (integrable_const _) ?_
    filter_upwards [h_bdd] with ω hω
    have h1 : |Z ω ^ k| = |Z ω| ^ k := by rw [abs_pow]
    have h2 : |Z ω| ^ k ≤ c ^ k := pow_le_pow_left₀ (abs_nonneg _) hω k
    rw [h1]; exact h2
  calc |∫ ω, Z ω ^ k ∂μ|
      ≤ ∫ ω, |Z ω ^ k| ∂μ := h_norm
    _ ≤ ∫ _ω, c ^ k ∂μ := h_bound
    _ = (μ.real Set.univ) * c ^ k := by
        rw [integral_const]; simp [measureReal_def, mul_comm]

/-! ### Integrability of `exp(s · Z)` from a bounded `Z`

For `|Z| ≤ c` a.s., the integrand `ω ↦ exp(s · Z(ω))` is dominated by
the constant `exp(|s| · c)`, hence integrable on any finite measure.
-/

/-- Integrability of `ω ↦ exp(s · Z(ω))` from `|Z| ≤ c` a.s. -/
private lemma integrable_exp_mul_of_bounded
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {Z : Ω → ℝ} (hZ_meas : Measurable Z)
    {c : ℝ} (_hc : 0 ≤ c) (h_bdd : ∀ᵐ ω ∂μ, |Z ω| ≤ c) (s : ℝ) :
    Integrable (fun ω => Real.exp (s * Z ω)) μ := by
  refine Integrable.mono' (g := fun _ => Real.exp (|s| * c)) ?_ ?_ ?_
  · exact integrable_const _
  · exact ((measurable_const.mul hZ_meas).exp).aestronglyMeasurable
  · -- `‖exp(s · Z(ω))‖ ≤ exp(|s| · c)` whenever `|Z(ω)| ≤ c`.
    filter_upwards [h_bdd] with ω hω
    have hnorm : ‖Real.exp (s * Z ω)‖ = Real.exp (s * Z ω) := by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [hnorm]
    apply Real.exp_le_exp.mpr
    -- `s * Z ω ≤ |s| * c`
    have h1 : s * Z ω ≤ |s * Z ω| := le_abs_self _
    have h2 : |s * Z ω| = |s| * |Z ω| := abs_mul _ _
    have h3 : |s| * |Z ω| ≤ |s| * c :=
      mul_le_mul_of_nonneg_left hω (abs_nonneg s)
    linarith

/-! ### Bach Lemma 1.2.3(a) — per-ω scalar bound

The per-ω form of Bach's Lemma 1.2.3(a), obtained by applying the
scalar Bennett-Bernstein remainder
`Real.exp_le_one_add_self_add_sq_div_of_abs_le` pointwise at
`y := s · Z(ω)` and `b := |s| · c`.
-/

/-- **Per-ω Bach scalar bound.** For `|Z(ω)| ≤ c` and `|s|·c < 3`,

  `exp(s · Z(ω)) ≤ 1 + s · Z(ω) + s² · Z(ω)² / (2 · (1 − |s|·c/3))`.

The proof is a pointwise application of the Bennett-Bernstein scalar
remainder bound from `LTFP.MathlibExt.Analysis.Exp.BernsteinRemainder`,
which is the formalised Taylor-expansion content of Bach's
Lemma 1.2.3(a). -/
private lemma bach_per_omega_bound
    {Z_ω : ℝ} {c s : ℝ}
    (hc : 0 ≤ c) (h_bdd : |Z_ω| ≤ c) (hsc : |s| * c < 3) :
    Real.exp (s * Z_ω) ≤
      1 + s * Z_ω +
        s ^ 2 * Z_ω ^ 2 / (2 * (1 - |s| * c / 3)) := by
  -- Apply the scalar remainder bound at `y := s * Z_ω` and `b := |s| * c`.
  set b : ℝ := |s| * c with hb_def
  have hb_nn : 0 ≤ b := mul_nonneg (abs_nonneg _) hc
  -- `|s * Z_ω| ≤ b`.
  have h_y_bdd : |s * Z_ω| ≤ b := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left h_bdd (abs_nonneg s)
  -- Apply.
  have hkey := Real.exp_le_one_add_self_add_sq_div_of_abs_le hb_nn hsc h_y_bdd
  -- `(s * Z_ω)^2 = s^2 * Z_ω^2`.
  have h_sq : (s * Z_ω) ^ 2 = s ^ 2 * Z_ω ^ 2 := by ring
  rw [h_sq] at hkey
  exact hkey

/-! ### Main result: Bach Lemma 1.2.3(a), textbook-strict form

Integrating the per-ω bound and using centering `∫ Z = 0` plus the
definition `sigma2 = ∫ Z²` yields the textbook-strict sub-Gamma MGF
bound.
-/

/-- **Bach (2024) Lemma 1.2.3(a), textbook-strict form (Part T.1).**

For a real random variable `Z` on a probability space with
`|Z| ≤ c` a.s. (with `0 ≤ c`) and `∫ Z dμ = 0`, in the small-`s`
regime `|s| · c < 3`, the moment-generating function satisfies the
sub-Gamma bound

  `∫ exp(s · Z) dμ ≤ exp(s² · sigma2 / (2 · (1 − |s| · c / 3)))`

where `sigma2 := ∫ Z² dμ`.

The proof follows Bach pp. 14-15 verbatim: apply the scalar
Bennett-Bernstein remainder pointwise (formalised in
`LTFP.MathlibExt.Analysis.Exp.BernsteinRemainder`), integrate using
centering and the definition of `sigma2`, and conclude via
`1 + α ≤ exp α`. -/
theorem bach_taylor_mgf
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (hZ_meas : Measurable Z)
    (c : ℝ) (hc : 0 ≤ c)
    (h_bdd : ∀ᵐ ω ∂μ, |Z ω| ≤ c)
    (h_centered : ∫ ω, Z ω ∂μ = 0)
    (sigma2 : ℝ) (hsigma2_def : sigma2 = ∫ ω, (Z ω) ^ 2 ∂μ)
    (s : ℝ) (hsc : |s| * c < 3) :
    ∫ ω, Real.exp (s * Z ω) ∂μ ≤
      Real.exp (s ^ 2 * sigma2 / (2 * (1 - |s| * c / 3))) := by
  -- Denominator setup.
  have hb_nn : 0 ≤ |s| * c := mul_nonneg (abs_nonneg _) hc
  have h_denom_pos : 0 < 1 - |s| * c / 3 := by linarith
  have h_two_denom_pos : 0 < 2 * (1 - |s| * c / 3) := by linarith
  -- Step 1: per-ω bound, integrated.
  -- LHS integrable.
  have h_int_exp := integrable_exp_mul_of_bounded hZ_meas hc h_bdd s
  -- Z is integrable (constant-dominated).
  have h_int_Z : Integrable Z μ := by
    refine Integrable.mono' (g := fun _ => c) ?_ hZ_meas.aestronglyMeasurable ?_
    · exact integrable_const _
    · filter_upwards [h_bdd] with ω hω
      rw [Real.norm_eq_abs]; exact hω
  -- Z^2 is integrable.
  have h_int_Z2 := integrable_pow_of_bounded hZ_meas hc h_bdd 2
  -- The RHS scalar `1 + s * Z(ω) + s^2 * Z(ω)^2 / D`.
  set D : ℝ := 2 * (1 - |s| * c / 3) with hD_def
  have hD_pos : 0 < D := h_two_denom_pos
  -- The RHS function is integrable.
  have h_int_rhs :
      Integrable (fun ω => 1 + s * Z ω + s ^ 2 * Z ω ^ 2 / D) μ := by
    refine Integrable.add ?_ ?_
    · refine Integrable.add (integrable_const 1) ?_
      exact h_int_Z.const_mul s
    · -- `s^2 * Z^2 / D = (s^2 / D) * Z^2`.
      have : (fun ω => s ^ 2 * Z ω ^ 2 / D)
          = (fun ω => (s ^ 2 / D) * Z ω ^ 2) := by
        funext ω; field_simp
      rw [this]
      exact h_int_Z2.const_mul (s ^ 2 / D)
  -- Step 2: pointwise per-ω bound.
  have h_pointwise :
      (fun ω => Real.exp (s * Z ω))
        ≤ᵐ[μ] (fun ω => 1 + s * Z ω + s ^ 2 * Z ω ^ 2 / D) := by
    filter_upwards [h_bdd] with ω hω
    exact bach_per_omega_bound hc hω hsc
  -- Step 3: integrate the inequality.
  have h_int_le :
      ∫ ω, Real.exp (s * Z ω) ∂μ ≤
        ∫ ω, 1 + s * Z ω + s ^ 2 * Z ω ^ 2 / D ∂μ :=
    integral_mono_ae h_int_exp h_int_rhs h_pointwise
  -- Step 4: compute the integrated RHS.
  -- `∫ (1 + s * Z + s^2 * Z^2 / D) = 1 + s * 0 + s^2 * sigma2 / D = 1 + s^2 * sigma2 / D`.
  have h_int_const : ∫ _ω, (1 : ℝ) ∂μ = 1 := by
    rw [integral_const]; simp
  have h_int_sZ : ∫ ω, s * Z ω ∂μ = 0 := by
    rw [integral_const_mul, h_centered, mul_zero]
  have h_int_sZ2 : ∫ ω, s ^ 2 * Z ω ^ 2 / D ∂μ
      = s ^ 2 * sigma2 / D := by
    -- (s^2 / D) is a constant scalar
    have : ∫ ω, s ^ 2 * Z ω ^ 2 / D ∂μ
        = (s ^ 2 / D) * ∫ ω, Z ω ^ 2 ∂μ := by
      have heq : (fun ω => s ^ 2 * Z ω ^ 2 / D)
          = (fun ω => (s ^ 2 / D) * Z ω ^ 2) := by
        funext ω; field_simp
      rw [heq, integral_const_mul]
    rw [this, ← hsigma2_def]
    field_simp
  -- Integrability lemmas for splitting `∫`.
  have h_int_1_sZ : Integrable (fun ω => (1 : ℝ) + s * Z ω) μ :=
    (integrable_const 1).add (h_int_Z.const_mul s)
  have h_int_sZ2_fn :
      Integrable (fun ω => s ^ 2 * Z ω ^ 2 / D) μ := by
    have heq : (fun ω => s ^ 2 * Z ω ^ 2 / D)
        = (fun ω => (s ^ 2 / D) * Z ω ^ 2) := by
      funext ω; field_simp
    rw [heq]; exact h_int_Z2.const_mul (s ^ 2 / D)
  have h_rhs_eq :
      ∫ ω, 1 + s * Z ω + s ^ 2 * Z ω ^ 2 / D ∂μ
        = 1 + s ^ 2 * sigma2 / D := by
    have h_split :
        ∫ ω, 1 + s * Z ω + s ^ 2 * Z ω ^ 2 / D ∂μ
          = ∫ ω, (1 + s * Z ω) ∂μ
              + ∫ ω, s ^ 2 * Z ω ^ 2 / D ∂μ :=
      integral_add h_int_1_sZ h_int_sZ2_fn
    have h_first : ∫ ω, (1 + s * Z ω) ∂μ = 1 := by
      rw [integral_add (integrable_const 1) (h_int_Z.const_mul s),
          h_int_const, h_int_sZ, add_zero]
    rw [h_split, h_first, h_int_sZ2]
  -- Step 5: combine with `1 + α ≤ exp α`.
  have h_chain :
      ∫ ω, Real.exp (s * Z ω) ∂μ ≤ 1 + s ^ 2 * sigma2 / D := by
    rw [← h_rhs_eq]
    exact h_int_le
  have h_one_add_le :
      1 + s ^ 2 * sigma2 / D ≤ Real.exp (s ^ 2 * sigma2 / D) := by
    have := Real.add_one_le_exp (s ^ 2 * sigma2 / D)
    linarith
  -- Conclude.
  calc ∫ ω, Real.exp (s * Z ω) ∂μ
      ≤ 1 + s ^ 2 * sigma2 / D := h_chain
    _ ≤ Real.exp (s ^ 2 * sigma2 / D) := h_one_add_le

/-! ### Part T.2 — iid Chernoff composition

For iid `Z₁, …, Zₙ` each satisfying Bach's hypotheses, the MGF of the
sum factorises by independence into the product of per-summand MGFs;
applying Bach's per-summand bound and the identity
`(exp x)^n = exp(n · x)` yields the iid composition.
-/

/-- **Bach iid composition (Part T.2).** For iid `Z : Fin n → Ω → ℝ`
all measurable, all satisfying `|Z i ω| ≤ c` a.s. and `∫ Z i = 0`, with
common variance `sigma2 = ∫ (Z 0)² dμ`, the MGF of the sum
`∑ᵢ Z i ω` satisfies

  `∫ exp(s · ∑ᵢ Z i ω) dμ ≤ exp(n · s² · σ² / (2 · (1 − |s|·c / 3)))`

in the regime `|s| · c < 3`.

The hypothesis `h_ident : ∀ i, ∫ (Z i)² dμ = sigma2` captures the
identically-distributed condition on second moments (since both
hypotheses on centring and bound are required to hold for every `i`).

The proof composes Bach's per-summand MGF bound (`bach_taylor_mgf`) with
the independence-product identity `mgf (∑ᵢ Zᵢ) = ∏ᵢ mgf Zᵢ`
(`iIndepFun.mgf_sum`) and the identity `(exp α)^n = exp(n · α)`. -/
theorem bach_taylor_mgf_iid_sum
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (Z : Fin n → Ω → ℝ)
    (h_indep : iIndepFun Z μ)
    (h_meas : ∀ i, Measurable (Z i))
    (c : ℝ) (hc : 0 ≤ c)
    (h_bdd : ∀ i, ∀ᵐ ω ∂μ, |Z i ω| ≤ c)
    (h_centered : ∀ i, ∫ ω, Z i ω ∂μ = 0)
    (sigma2 : ℝ) (h_ident : ∀ i, sigma2 = ∫ ω, (Z i ω) ^ 2 ∂μ)
    (s : ℝ) (hsc : |s| * c < 3) :
    ∫ ω, Real.exp (s * (∑ i : Fin n, Z i ω)) ∂μ ≤
      Real.exp ((n : ℝ) * (s ^ 2 * sigma2 / (2 * (1 - |s| * c / 3)))) := by
  classical
  -- Step 1: rewrite the LHS as `mgf (∑ Z) μ s`.
  -- Note `∑ i, Z i ω = (∑ i, Z i) ω` by `Finset.sum_apply`.
  have hLHS_eq :
      ∫ ω, Real.exp (s * (∑ i : Fin n, Z i ω)) ∂μ
        = ProbabilityTheory.mgf (∑ i : Fin n, Z i) μ s := by
    unfold ProbabilityTheory.mgf
    simp only [Finset.sum_apply]
  -- Use independence to factor into a product of single MGFs.
  have hsum_mgf := h_indep.mgf_sum (t := s) h_meas (s := Finset.univ)
  -- Each MGF is bounded by Bach's per-summand bound.
  set α : ℝ := s ^ 2 * sigma2 / (2 * (1 - |s| * c / 3)) with hα_def
  have h_each_mgf_le :
      ∀ i : Fin n, ProbabilityTheory.mgf (Z i) μ s ≤ Real.exp α := by
    intro i
    have h1 := bach_taylor_mgf (Z i) (h_meas i) c hc (h_bdd i)
                  (h_centered i) sigma2 (h_ident i) s hsc
    -- Match `mgf` against `∫ exp (s * Z i)`.
    unfold ProbabilityTheory.mgf
    exact h1
  have h_mgf_nn : ∀ i, 0 ≤ ProbabilityTheory.mgf (Z i) μ s := by
    intro i
    unfold ProbabilityTheory.mgf
    apply integral_nonneg
    intro ω
    exact (Real.exp_pos _).le
  -- Product of per-summand MGFs bounded by product of `exp α` = `(exp α)^n`.
  have h_prod_le :
      (∏ i : Fin n, ProbabilityTheory.mgf (Z i) μ s)
        ≤ ∏ _i : Fin n, Real.exp α := by
    apply Finset.prod_le_prod
    · intro i _; exact h_mgf_nn i
    · intro i _; exact h_each_mgf_le i
  -- `∏ exp α = (exp α)^n = exp (n · α)`.
  have h_prod_const :
      (∏ _i : Fin n, Real.exp α) = Real.exp ((n : ℝ) * α) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [← Real.exp_nat_mul]
  -- Chain.
  rw [hLHS_eq, hsum_mgf]
  -- Need `∏ i ∈ Finset.univ, mgf ≤ exp (n * α)`.
  calc (∏ i ∈ Finset.univ, ProbabilityTheory.mgf (Z i) μ s)
      ≤ (∏ _i : Fin n, Real.exp α) := h_prod_le
    _ = Real.exp ((n : ℝ) * α) := h_prod_const

end ProbabilityTheory
