/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# The standard normal cumulative distribution function

This file defines the standard normal (Gaussian) probability density function
`Real.stdGaussianPDF` and cumulative distribution function `Real.stdGaussianCDF`
directly as an improper Lebesgue integral over `Set.Iic x`, and develops the
basic analytic properties that downstream theorems (NTK smoothness, sub-Gaussian
tail bounds) rely on:

* pointwise positivity of the PDF;
* integrability of the PDF over `ℝ`;
* the total-mass identity `∫ pdf = 1`;
* monotonicity, continuity, and differentiability of the CDF;
* the reference values `CDF 0 = 1/2` and the complementary identity
  `CDF x + CDF (-x) = 1`;
* the range bounds `0 ≤ CDF x ≤ 1` and the limits at `±∞`.

## Design notes

We define the PDF using the standard normalization `(√(2π))⁻¹ * exp(-x²/2)`,
matching Bach's *Learning Theory from First Principles* Chapter 2 conventions.
The Gaussian integral `∫ exp(-(1/2) x²) = √(2π)` follows from Mathlib's
`integral_gaussian` instantiated at `b = 1/2`.

The FTC differentiability statement `hasDerivAt_stdGaussianCDF` is obtained by
rewriting the `Iic x` integral as `∫ Iic a + ∫ a..x` in a neighborhood of `x`
for some `a < x`, then applying `integral_hasDerivAt_right`. Reflection symmetry
`CDF 0 = 1/2` uses `integral_comp_neg_Iic` on the even integrand `exp(-x²/2)`.

## Main declarations

* `Real.stdGaussianPDF`, `Real.stdGaussianCDF` — the definitions.
* `Real.stdGaussianPDF_pos`, `Real.stdGaussianPDF_integrable`,
  `Real.stdGaussianPDF_total_integral` — PDF invariants.
* `Real.stdGaussianCDF_monotone`, `Real.stdGaussianCDF_continuous`,
  `Real.hasDerivAt_stdGaussianCDF` — CDF regularity.
* `Real.stdGaussianCDF_zero`, `Real.stdGaussianCDF_complementary` — reference
  values.
* `Real.stdGaussianCDF_nonneg`, `Real.stdGaussianCDF_le_one`,
  `Real.tendsto_stdGaussianCDF_atTop`, `Real.tendsto_stdGaussianCDF_atBot` —
  range bounds and asymptotics.
-/

open MeasureTheory Set Filter Topology intervalIntegral

namespace Real

/-! ### Basic constants -/

/-- The normalising constant `√(2π)` is positive. -/
theorem sqrt_two_pi_pos : 0 < Real.sqrt (2 * Real.pi) :=
  Real.sqrt_pos.mpr Real.two_pi_pos

/-- The normalising constant `√(2π)` is nonzero. -/
theorem sqrt_two_pi_ne_zero : Real.sqrt (2 * Real.pi) ≠ 0 :=
  ne_of_gt sqrt_two_pi_pos

/-- `√(π / (1/2)) = √(2π)`. -/
theorem sqrt_pi_div_half : Real.sqrt (Real.pi / (1 / 2)) = Real.sqrt (2 * Real.pi) := by
  congr 1
  ring

/-! ### The standard Gaussian PDF -/

/-- The standard normal probability density function
`x ↦ (√(2π))⁻¹ * exp(-x²/2)`. -/
noncomputable def stdGaussianPDF (x : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (- x ^ 2 / 2)

/-- The standard Gaussian PDF is strictly positive at every point. -/
theorem stdGaussianPDF_pos (x : ℝ) : 0 < stdGaussianPDF x := by
  unfold stdGaussianPDF
  have h1 : 0 < (Real.sqrt (2 * Real.pi))⁻¹ := inv_pos.mpr sqrt_two_pi_pos
  have h2 : 0 < Real.exp (- x ^ 2 / 2) := Real.exp_pos _
  exact mul_pos h1 h2

/-- The standard Gaussian PDF is nonnegative. -/
theorem stdGaussianPDF_nonneg (x : ℝ) : 0 ≤ stdGaussianPDF x :=
  le_of_lt (stdGaussianPDF_pos x)

/-- Rewrite the PDF's exponent as `-(1/2) * x²`. -/
theorem stdGaussianPDF_eq (x : ℝ) :
    stdGaussianPDF x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1/2) * x ^ 2) := by
  unfold stdGaussianPDF
  congr 1
  congr 1
  ring

/-- The kernel `exp(-x²/2)` is integrable on `ℝ`. -/
theorem integrable_exp_neg_half_sq :
    Integrable (fun x : ℝ => Real.exp (-(1/2) * x ^ 2)) := by
  exact integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)

/-- The standard Gaussian PDF is integrable on `ℝ`. -/
theorem stdGaussianPDF_integrable : Integrable stdGaussianPDF := by
  have h : Integrable (fun x : ℝ =>
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1/2) * x ^ 2)) :=
    integrable_exp_neg_half_sq.const_mul _
  refine h.congr ?_
  filter_upwards with x
  exact (stdGaussianPDF_eq x).symm

/-- The Gaussian kernel `exp(-x²/2)` integrates to `√(2π)` on `ℝ`. -/
theorem integral_exp_neg_half_sq :
    ∫ x : ℝ, Real.exp (-(1/2) * x ^ 2) = Real.sqrt (2 * Real.pi) := by
  have h := integral_gaussian (1/2)
  rw [h, sqrt_pi_div_half]

/-- The standard Gaussian PDF has total mass one. -/
theorem stdGaussianPDF_total_integral :
    ∫ x : ℝ, stdGaussianPDF x = 1 := by
  have hrw : ∀ x : ℝ, stdGaussianPDF x =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1/2) * x ^ 2) := stdGaussianPDF_eq
  calc ∫ x : ℝ, stdGaussianPDF x
      = ∫ x : ℝ, (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1/2) * x ^ 2) := by
        refine integral_congr_ae ?_
        filter_upwards with x using hrw x
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * ∫ x : ℝ, Real.exp (-(1/2) * x ^ 2) := by
        exact integral_const_mul _ _
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * Real.sqrt (2 * Real.pi) := by
        rw [integral_exp_neg_half_sq]
    _ = 1 := inv_mul_cancel₀ sqrt_two_pi_ne_zero

/-- The PDF is integrable on every set (in particular on every `Iic x`). -/
theorem stdGaussianPDF_integrableOn (s : Set ℝ) :
    IntegrableOn stdGaussianPDF s := stdGaussianPDF_integrable.integrableOn

/-! ### The standard Gaussian CDF -/

/-- The standard normal cumulative distribution function,
`CDF(x) = ∫_{-∞}^x pdf(t) dt`. -/
noncomputable def stdGaussianCDF (x : ℝ) : ℝ :=
  ∫ t in Iic x, stdGaussianPDF t

/-- The CDF is nonnegative. -/
theorem stdGaussianCDF_nonneg (x : ℝ) : 0 ≤ stdGaussianCDF x := by
  unfold stdGaussianCDF
  exact integral_nonneg (fun t => stdGaussianPDF_nonneg t)

/-- The CDF is monotone. -/
theorem stdGaussianCDF_monotone : Monotone stdGaussianCDF := by
  intro a b hab
  unfold stdGaussianCDF
  have hIic : Iic a ⊆ Iic b := Iic_subset_Iic.mpr hab
  refine setIntegral_mono_set stdGaussianPDF_integrable.integrableOn ?_ ?_
  · filter_upwards with t using stdGaussianPDF_nonneg t
  · exact Filter.Eventually.of_forall hIic

/-- The whole line splits as `Iic x ∪ Ioi x`, so the CDF plus the tail integral
sum to the total mass `1`. -/
theorem stdGaussianCDF_add_integral_Ioi (x : ℝ) :
    stdGaussianCDF x + ∫ t in Ioi x, stdGaussianPDF t = 1 := by
  unfold stdGaussianCDF
  have hIic := integral_add_compl (μ := MeasureTheory.volume)
    (measurableSet_Iic (a := x)) stdGaussianPDF_integrable
  have hcompl : (Iic x)ᶜ = Ioi x := by
    ext t; simp [Set.mem_Ioi]
  rw [hcompl] at hIic
  rw [stdGaussianPDF_total_integral] at hIic
  exact hIic

/-- The CDF is bounded above by `1`. -/
theorem stdGaussianCDF_le_one (x : ℝ) : stdGaussianCDF x ≤ 1 := by
  have h := stdGaussianCDF_add_integral_Ioi x
  have h_tail : 0 ≤ ∫ t in Ioi x, stdGaussianPDF t := by
    exact integral_nonneg (fun t => stdGaussianPDF_nonneg t)
  linarith

/-! ### Symmetry: `CDF 0 = 1/2` -/

/-- The Gaussian kernel is even (as a function of `t`). -/
theorem exp_neg_half_sq_even (t : ℝ) :
    Real.exp (-(1/2) * (-t) ^ 2) = Real.exp (-(1/2) * t ^ 2) := by
  congr 1
  ring

/-- The PDF is symmetric about `0`. -/
theorem stdGaussianPDF_neg (t : ℝ) : stdGaussianPDF (-t) = stdGaussianPDF t := by
  simp only [stdGaussianPDF_eq]
  congr 1
  exact exp_neg_half_sq_even t

/-- Reflection: the integral of the PDF over `Iic 0` equals the integral over
`Ioi 0`. -/
theorem stdGaussianPDF_integral_Iic_zero_eq_Ioi_zero :
    ∫ t in Iic (0 : ℝ), stdGaussianPDF t = ∫ t in Ioi (0 : ℝ), stdGaussianPDF t := by
  have key : ∫ t in Iic (0 : ℝ), stdGaussianPDF (-t) = ∫ t in Ioi (-0 : ℝ), stdGaussianPDF t :=
    integral_comp_neg_Iic (0 : ℝ) stdGaussianPDF
  have heq : ∀ t, stdGaussianPDF (-t) = stdGaussianPDF t := stdGaussianPDF_neg
  have hlhs : ∫ t in Iic (0 : ℝ), stdGaussianPDF (-t) = ∫ t in Iic (0 : ℝ), stdGaussianPDF t := by
    refine integral_congr_ae ?_
    filter_upwards with t using heq t
  rw [hlhs] at key
  simpa using key

/-- The CDF at `0` equals `1/2`. -/
theorem stdGaussianCDF_zero : stdGaussianCDF 0 = 1 / 2 := by
  unfold stdGaussianCDF
  have hsplit := stdGaussianCDF_add_integral_Ioi (0 : ℝ)
  unfold stdGaussianCDF at hsplit
  have hsym := stdGaussianPDF_integral_Iic_zero_eq_Ioi_zero
  -- After substitution: 2 * (∫ Iic 0, pdf) = 1
  rw [hsym] at hsplit
  linarith

/-! ### Complementary identity -/

/-- The integral over `Ioi x` equals the integral over `Iic (-x)` by reflection. -/
theorem stdGaussianPDF_integral_Ioi_eq_Iic_neg (x : ℝ) :
    ∫ t in Ioi x, stdGaussianPDF t = ∫ t in Iic (-x), stdGaussianPDF t := by
  have hrefl : ∫ t in Ioi x, stdGaussianPDF (-t) = ∫ t in Iic (-x), stdGaussianPDF t :=
    integral_comp_neg_Ioi x stdGaussianPDF
  have hcong : ∫ t in Ioi x, stdGaussianPDF (-t) = ∫ t in Ioi x, stdGaussianPDF t := by
    refine integral_congr_ae ?_
    filter_upwards with t using stdGaussianPDF_neg t
  rw [hcong] at hrefl
  exact hrefl

/-- Complementary identity: `CDF x + CDF (-x) = 1`. -/
theorem stdGaussianCDF_complementary (x : ℝ) :
    stdGaussianCDF x + stdGaussianCDF (-x) = 1 := by
  have hsplit := stdGaussianCDF_add_integral_Ioi x
  have hrefl := stdGaussianPDF_integral_Ioi_eq_Iic_neg x
  unfold stdGaussianCDF
  rw [hrefl] at hsplit
  exact hsplit

/-! ### Continuity and the Fundamental Theorem of Calculus -/

/-- The PDF, as a function of `t`, is continuous. -/
theorem continuous_stdGaussianPDF : Continuous stdGaussianPDF := by
  unfold stdGaussianPDF
  exact continuous_const.mul (Real.continuous_exp.comp
    ((continuous_pow 2).neg.div_const 2))

/-- The interval integral of the PDF from `a` to `x` equals the CDF at `x` minus
the CDF at `a` (when `a ≤ x`, so that we can split the `Iic x` integral). -/
theorem stdGaussianCDF_sub_stdGaussianCDF (a x : ℝ) (hax : a ≤ x) :
    stdGaussianCDF x - stdGaussianCDF a = ∫ t in a..x, stdGaussianPDF t := by
  unfold stdGaussianCDF
  have h_int_Iic_a : IntegrableOn stdGaussianPDF (Iic a) :=
    stdGaussianPDF_integrable.integrableOn
  have h_int_Ioc : IntegrableOn stdGaussianPDF (Ioc a x) :=
    stdGaussianPDF_integrable.integrableOn
  have h_disj : Disjoint (Iic a) (Ioc a x) := Iic_disjoint_Ioc le_rfl
  have h_union : ∫ t in Iic a ∪ Ioc a x, stdGaussianPDF t
      = (∫ t in Iic a, stdGaussianPDF t) + ∫ t in Ioc a x, stdGaussianPDF t :=
    setIntegral_union h_disj measurableSet_Ioc h_int_Iic_a h_int_Ioc
  have h_eq_set : Iic a ∪ Ioc a x = Iic x := Iic_union_Ioc_eq_Iic hax
  have h_ioc_eq : ∫ t in Ioc a x, stdGaussianPDF t = ∫ t in a..x, stdGaussianPDF t :=
    (intervalIntegral.integral_of_le hax).symm
  rw [h_eq_set] at h_union
  rw [← h_ioc_eq]
  linarith [h_union]

/-- FTC: the CDF is differentiable at every point with derivative the PDF. -/
theorem hasDerivAt_stdGaussianCDF (x : ℝ) :
    HasDerivAt stdGaussianCDF (stdGaussianPDF x) x := by
  -- Local strategy: on a neighborhood of x (specifically Ici (x-1)), we have
  -- stdGaussianCDF u = stdGaussianCDF (x-1) + ∫ t in (x-1)..u, pdf t.
  -- The interval-integral part has derivative pdf x at u = x by FTC-right;
  -- the constant part has derivative 0. Sum: pdf x.
  set a := x - 1 with ha_def
  have hax : a < x := by simp [ha_def]
  have hInt : IntervalIntegrable stdGaussianPDF MeasureTheory.volume a x :=
    stdGaussianPDF_integrable.intervalIntegrable
  have hcont : ContinuousAt stdGaussianPDF x := continuous_stdGaussianPDF.continuousAt
  have hmeas : StronglyMeasurableAtFilter stdGaussianPDF (𝓝 x) :=
    continuous_stdGaussianPDF.stronglyMeasurable.stronglyMeasurableAtFilter
  have hFTC : HasDerivAt (fun u => ∫ t in a..u, stdGaussianPDF t) (stdGaussianPDF x) x :=
    integral_hasDerivAt_right hInt hmeas hcont
  -- Shift by the constant stdGaussianCDF a: this doesn't change the derivative.
  have hShift : HasDerivAt (fun u => stdGaussianCDF a + ∫ t in a..u, stdGaussianPDF t)
      (stdGaussianPDF x) x := by
    simpa using hFTC.const_add (stdGaussianCDF a)
  -- Show that stdGaussianCDF and (u ↦ CDF a + ∫ a..u, pdf) agree on Ici a,
  -- hence eventually equal near x.
  have h_eventuallyEq : stdGaussianCDF =ᶠ[𝓝 x]
      (fun u => stdGaussianCDF a + ∫ t in a..u, stdGaussianPDF t) := by
    have hnhds : Ioi a ∈ 𝓝 x := Ioi_mem_nhds hax
    refine Filter.eventuallyEq_iff_exists_mem.mpr ⟨Ioi a, hnhds, ?_⟩
    intro u hu
    have hau : a ≤ u := le_of_lt hu
    have := stdGaussianCDF_sub_stdGaussianCDF a u hau
    linarith
  exact hShift.congr_of_eventuallyEq h_eventuallyEq

/-- The CDF is differentiable. -/
theorem differentiable_stdGaussianCDF : Differentiable ℝ stdGaussianCDF :=
  fun x => (hasDerivAt_stdGaussianCDF x).differentiableAt

/-- The CDF is continuous. -/
theorem continuous_stdGaussianCDF : Continuous stdGaussianCDF :=
  differentiable_stdGaussianCDF.continuous

/-- The derivative of the CDF is the PDF. -/
theorem deriv_stdGaussianCDF (x : ℝ) : deriv stdGaussianCDF x = stdGaussianPDF x :=
  (hasDerivAt_stdGaussianCDF x).deriv

/-! ### Asymptotic behavior -/

/-- As `x → +∞`, the CDF tends to `1`. -/
theorem tendsto_stdGaussianCDF_atTop :
    Tendsto stdGaussianCDF atTop (𝓝 1) := by
  -- Rewrite CDF x = ∫ Iic x, pdf, and note ∫ 0..x, pdf → ∫ Ioi 0, pdf as x → ∞.
  -- Then stdGaussianCDF x = stdGaussianCDF 0 + ∫ 0..x, pdf for x ≥ 0.
  have h_split : ∀ x, 0 ≤ x →
      stdGaussianCDF x = stdGaussianCDF 0 + ∫ t in (0:ℝ)..x, stdGaussianPDF t := by
    intro x hx
    have h := stdGaussianCDF_sub_stdGaussianCDF 0 x hx
    linarith
  have h_tail_int : IntegrableOn stdGaussianPDF (Ioi (0 : ℝ)) :=
    stdGaussianPDF_integrable.integrableOn
  have h_lim_int : Tendsto (fun x : ℝ => ∫ t in (0:ℝ)..x, stdGaussianPDF t) atTop
      (𝓝 (∫ t in Ioi (0:ℝ), stdGaussianPDF t)) :=
    intervalIntegral_tendsto_integral_Ioi 0 h_tail_int tendsto_id
  have h_tail_val : ∫ t in Ioi (0:ℝ), stdGaussianPDF t = 1/2 := by
    have hsplit := stdGaussianCDF_add_integral_Ioi (0 : ℝ)
    rw [stdGaussianCDF_zero] at hsplit
    linarith
  rw [h_tail_val] at h_lim_int
  -- Target: (fun x => (1/2) + ∫ 0..x, pdf) tends to 1.
  have h_target : Tendsto (fun x : ℝ => (1/2 : ℝ) + ∫ t in (0:ℝ)..x, stdGaussianPDF t)
      atTop (𝓝 ((1/2 : ℝ) + 1/2)) :=
    tendsto_const_nhds.add h_lim_int
  have h_val : (1/2 : ℝ) + 1/2 = 1 := by norm_num
  rw [h_val] at h_target
  -- Transfer via eventual equality (for x ≥ 0), noting CDF 0 = 1/2.
  refine h_target.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
  rw [← stdGaussianCDF_zero]
  exact (h_split x hx).symm

/-- As `x → -∞`, the CDF tends to `0`. -/
theorem tendsto_stdGaussianCDF_atBot :
    Tendsto stdGaussianCDF atBot (𝓝 0) := by
  -- Use the complementary identity: CDF x + CDF(-x) = 1, so CDF x = 1 - CDF(-x).
  -- As x → -∞, -x → +∞, so CDF(-x) → 1, hence CDF x → 0.
  have h_neg : Tendsto (fun x : ℝ => -x) atBot atTop := Filter.tendsto_neg_atBot_atTop
  have h_comp : Tendsto (fun x : ℝ => stdGaussianCDF (-x)) atBot (𝓝 1) :=
    tendsto_stdGaussianCDF_atTop.comp h_neg
  have h_eq : ∀ x : ℝ, stdGaussianCDF x = 1 - stdGaussianCDF (-x) := by
    intro x
    have := stdGaussianCDF_complementary x
    linarith
  have h_rw : Tendsto (fun x : ℝ => 1 - stdGaussianCDF (-x)) atBot (𝓝 (1 - 1)) :=
    tendsto_const_nhds.sub h_comp
  have h_final : (1 : ℝ) - 1 = 0 := by norm_num
  rw [h_final] at h_rw
  refine h_rw.congr ?_
  intro x
  exact (h_eq x).symm

/-! ### Numerical sanity: `Float` variant

For compile-time / user-facing sanity checks, we provide a `Float` version
`stdGaussianCDF_float` that approximates `stdGaussianCDF` via a Taylor-series
expansion of `erf`. This is NOT used in any theorem — it exists purely for
`#eval` verification that our conventions match the standard textbook. -/

/-- Float approximation of the error function via its Taylor series
`erf(x) = (2/√π) * Σ_{n=0}^{N} (-1)^n * x^{2n+1} / (n! * (2n+1))`. -/
def erf_float (x : Float) : Float := Id.run do
  let mut sum : Float := 0.0
  let mut term : Float := x
  let mut n : Nat := 0
  while n < 60 do
    sum := sum + term / (2.0 * n.toFloat + 1.0)
    term := -term * x * x / (n.toFloat + 1.0)
    n := n + 1
  return (2.0 / Float.sqrt 3.141592653589793) * sum

/-- Float approximation of the standard Gaussian CDF via `Φ(x) = (1 + erf(x/√2))/2`. -/
def stdGaussianCDF_float (x : Float) : Float :=
  0.5 * (1.0 + erf_float (x / Float.sqrt 2.0))

/-! ### Sanity checks (evaluated at compile time)
The reader can check the following numerical approximations:

* `#eval stdGaussianCDF_float 0.0`   → `0.5`
* `#eval stdGaussianCDF_float 1.0`   → `≈ 0.8413`
* `#eval stdGaussianCDF_float (-1.0)` → `≈ 0.1587`

These match the well-known values `Φ(0) = 1/2`, `Φ(1) ≈ 0.8413`, and
`Φ(-1) ≈ 0.1587` from any standard-normal table, providing informal evidence
that our formal definition matches the intended convention. -/

end Real
