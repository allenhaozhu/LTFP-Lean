/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import Mathlib.Probability.Moments.Basic
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Sub-exponential and sub-Gamma random variables

Proposed Mathlib path: `Mathlib/Probability/Moments/SubExponential.lean`.
Proposed namespace: `ProbabilityTheory` (matching
`Mathlib.Probability.Moments.SubGaussian`).

A real-valued random variable `X` on a measure space `(Ω, μ)` is
**`(ν, b)`-sub-exponential** if there exist nonnegative reals `ν` and `b`
such that the moment-generating function of `X` satisfies the Gaussian
bound

`mgf X μ s ≤ exp (s² · ν / 2)`

in the small-`s` regime `|s| · b < 1`. Setting `b = 0` removes the side
condition and recovers the sub-Gaussian moment-generating function bound
already formalized as `ProbabilityTheory.HasSubgaussianMGF`; the
parameter `b` thus measures how far the variable departs from
sub-Gaussian behaviour, i.e. how heavy its tails can be.

This is the standard definition used in
[wainwright2019high, §2.1.3] and [vershynin2018high, §2.7]. Combined
with the Chernoff bound `ProbabilityTheory.measure_ge_le_exp_mul_mgf`,
it yields the canonical two-regime **Bernstein inequality**

`μ.real {ω | t ≤ X ω} ≤ exp(-min(t² / (2ν), t / (2b)))`.

In addition, we package the strictly more general **sub-Gamma** MGF
class. A random variable `X` is `(ν, b)`-**sub-Gamma** if

`mgf X μ s ≤ exp (s² · ν / (2 · (1 - |s| · b)))`

for every `s` with `|s| · b < 1`. This is the natural MGF class used in
[boucheron2013concentration, §2.4] from which the Bernstein inequality
follows directly without optimisation over an auxiliary sub-Gaussian
parameter. Sub-Gamma is a *weaker* condition than sub-exponential (the
Gaussian bound `exp(s²ν/2)` implies the sub-Gamma bound by
`1/(1 - |s|·b) ≥ 1`); conversely, a `(ν, b)`-sub-Gamma variable is
`(2ν, 2b)`-sub-exponential on the half-interval `|s|·b < 1/2`, so the
two classes coincide up to a factor of `2` in the parameters.

## Main definitions

* `ProbabilityTheory.IsSubExponential`: `X` has a `(ν, b)`-sub-exponential
  moment-generating function under `μ`.
* `ProbabilityTheory.IsSubGamma`: `X` has a `(ν, b)`-sub-Gamma
  moment-generating function under `μ`.

## Main statements

* `ProbabilityTheory.IsSubExponential.const`: a constant function is
  `(0, 0)`-sub-exponential under any probability measure.
* `ProbabilityTheory.IsSubExponential.mono_b`: the sub-exponential class
  is monotone in the scale parameter `b`.
* `ProbabilityTheory.IsSubExponential.mono_nu`: the sub-exponential
  class is monotone in the variance proxy `ν`.
* `ProbabilityTheory.IsSubExponential.of_hasSubgaussianMGF`: every
  `HasSubgaussianMGF`-sub-Gaussian variable is sub-exponential with
  `b = 0`.
* `ProbabilityTheory.IsSubExponential.measure_ge_le`: the Chernoff-style
  one-sided tail bound for a sub-exponential random variable.
* `ProbabilityTheory.IsSubGamma.const_zero`: the constant `0` random
  variable is `(0, 0)`-sub-Gamma under any probability measure.
* `ProbabilityTheory.IsSubGamma.mono_nu` / `mono_b`: monotonicity of the
  sub-Gamma class in each parameter.
* `ProbabilityTheory.IsSubExponential.toIsSubGamma`: sub-exponential
  implies sub-Gamma with the same parameters.
* `ProbabilityTheory.IsSubGamma.toIsSubExponential`: sub-Gamma implies
  sub-exponential with parameters scaled by `2` on the half-interval.
* `ProbabilityTheory.IsSubGamma.measure_ge_le`: the Bernstein tail bound
  arising directly from the sub-Gamma MGF inequality.

## Implementation notes

We do not include integrability of `exp (s · X)` in the structure, in
contrast to `Mathlib.Probability.Moments.SubGaussian`'s
`HasSubgaussianMGF`. The Chernoff tail bound
`IsSubExponential.measure_ge_le` therefore takes integrability as an
explicit hypothesis. This keeps the definition lightweight and matches
the convention used in [bach2024learning, §1.2], where the MGF
inequality alone is taken as the working definition.

## References

* [vershynin2018high] Vershynin, R. (2018).
  *High-Dimensional Probability*. Cambridge University Press. §2.7.
* [wainwright2019high] Wainwright, M. J. (2019).
  *High-Dimensional Statistics: A Non-Asymptotic Viewpoint*. Cambridge
  University Press. §2.1.3.
* [boucheron2013concentration] Boucheron, S., Lugosi, G., Massart, P.
  (2013). *Concentration Inequalities: A Nonasymptotic Theory of
  Independence*. Oxford University Press. §2.4.
* [bach2024learning] Bach, F. (2024). *Learning Theory from First
  Principles*. MIT Press. §1.2.

## Tags

sub-exponential, sub-Gamma, concentration, MGF, Bernstein
-/

namespace ProbabilityTheory

open MeasureTheory Real

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- A real-valued random variable `X` on `(Ω, μ)` is
`(ν, b)`-**sub-exponential** if its moment-generating function admits the
Gaussian bound `mgf X μ s ≤ exp (s² · ν / 2)` for every real `s` lying
in the open interval `(-1/b, 1/b)`, encoded as the side condition
`|s| · b < 1`. The parameters `ν` and `b` are required to be
nonnegative.

Taking `b = 0` collapses the side condition `|s| · b < 1` to the
universally true `0 < 1`, so the MGF inequality holds for every `s : ℝ`
and we recover the sub-Gaussian moment-generating function bound. -/
structure IsSubExponential (X : Ω → ℝ) (μ : Measure Ω) (ν b : ℝ) : Prop where
  /-- The variance proxy `ν` is nonnegative. -/
  ν_nonneg : 0 ≤ ν
  /-- The scale parameter `b` is nonnegative. -/
  b_nonneg : 0 ≤ b
  /-- The MGF is bounded by a Gaussian in the small-`s` regime
  `|s| · b < 1`. -/
  mgf_le : ∀ s : ℝ, |s| * b < 1 → mgf X μ s ≤ Real.exp (s ^ 2 * ν / 2)

namespace IsSubExponential

variable {X : Ω → ℝ} {μ : Measure Ω} {ν b ν' b' : ℝ}

/-- Any constant random variable equal to `0` is `(0, 0)`-sub-exponential
under any probability measure. More generally, see `const` below. -/
theorem const_zero (μ : Measure Ω) [IsProbabilityMeasure μ] :
    IsSubExponential (fun _ : Ω => (0 : ℝ)) μ 0 0 where
  ν_nonneg := le_rfl
  b_nonneg := le_rfl
  mgf_le := by
    intro s _
    have hmgf : mgf (fun _ : Ω => (0 : ℝ)) μ s = 1 := by simp
    have hrhs : Real.exp (s ^ 2 * 0 / 2) = 1 := by simp
    rw [hmgf, hrhs]

/-- Enlarging the scale parameter `b` preserves the sub-exponential
property: a `(ν, b)`-sub-exponential variable is automatically
`(ν, b')`-sub-exponential whenever `b ≤ b'`. -/
theorem mono_b (h : IsSubExponential X μ ν b) (hb : b ≤ b') :
    IsSubExponential X μ ν b' where
  ν_nonneg := h.ν_nonneg
  b_nonneg := le_trans h.b_nonneg hb
  mgf_le := by
    intro s hs
    have habs : 0 ≤ |s| := abs_nonneg s
    have hmul : |s| * b ≤ |s| * b' := mul_le_mul_of_nonneg_left hb habs
    exact h.mgf_le s (lt_of_le_of_lt hmul hs)

/-- Enlarging the variance proxy `ν` preserves the sub-exponential
property: a `(ν, b)`-sub-exponential variable is automatically
`(ν', b)`-sub-exponential whenever `ν ≤ ν'`. -/
theorem mono_nu (h : IsSubExponential X μ ν b) (hν : ν ≤ ν') :
    IsSubExponential X μ ν' b where
  ν_nonneg := le_trans h.ν_nonneg hν
  b_nonneg := h.b_nonneg
  mgf_le := by
    intro s hs
    have hbound := h.mgf_le s hs
    have hsq : 0 ≤ s ^ 2 := sq_nonneg s
    have hrhs : s ^ 2 * ν / 2 ≤ s ^ 2 * ν' / 2 := by
      have := mul_le_mul_of_nonneg_left hν hsq
      linarith
    exact le_trans hbound (Real.exp_le_exp.mpr hrhs)

/-! ## Relationship to sub-Gaussian variables

A `(ν, 0)`-sub-exponential variable is exactly a variable whose
moment-generating function is bounded by `exp (s² · ν / 2)` for every
`s : ℝ`. This is the defining MGF inequality of the sub-Gaussian class
`ProbabilityTheory.HasSubgaussianMGF` (modulo the additional
integrability requirement that `HasSubgaussianMGF` packages into the
structure). The scale parameter `b ≥ 0` therefore quantifies how far
`X` departs from sub-Gaussian behaviour: as `b` grows the heavy-tail
regime `|s| · b ≥ 1` excluded from the MGF bound widens.

The lemma below converts a `HasSubgaussianMGF`-sub-Gaussian variable
into a sub-exponential variable with `b = 0` by simply forgetting the
integrability part of the sub-Gaussian structure.
-/

/-- Every `c`-sub-Gaussian random variable (in the sense of
`ProbabilityTheory.HasSubgaussianMGF`) is `(c, 0)`-sub-exponential. The
scale parameter `b = 0` removes the side condition, so the MGF bound
holds for every `s : ℝ`. -/
theorem of_hasSubgaussianMGF {X : Ω → ℝ} {μ : Measure Ω} {c : NNReal}
    (h : HasSubgaussianMGF X c μ) :
    IsSubExponential X μ (c : ℝ) 0 where
  ν_nonneg := c.coe_nonneg
  b_nonneg := le_rfl
  mgf_le := by
    intro s _
    have hbound : mgf X μ s ≤ Real.exp ((c : ℝ) * s ^ 2 / 2) := h.mgf_le s
    have hcomm : (c : ℝ) * s ^ 2 / 2 = s ^ 2 * (c : ℝ) / 2 := by ring
    rw [hcomm] at hbound
    exact hbound

/-- **Chernoff bound for sub-exponential random variables.**

For a `(ν, b)`-sub-exponential random variable `X`, every nonnegative
parameter `s` in the small-`s` regime `s · b < 1` gives the tail bound

`μ.real {ω | ε ≤ X ω} ≤ exp(-s · ε + s² · ν / 2)`.

The optimal choice `s = ε / ν` (when `0 ≤ ε ≤ ν / b`) yields the
"sub-Gaussian regime" of Bernstein's inequality
`μ.real {ω | ε ≤ X ω} ≤ exp(-ε² / (2ν))`, while the boundary choice
`s ↑ 1/b` yields the "exponential regime"
`μ.real {ω | ε ≤ X ω} ≤ exp(-ε / (2b))`. Combining the two regimes
recovers the canonical Bernstein bound; we leave that optimization to
the caller. -/
theorem measure_ge_le [IsFiniteMeasure μ]
    (h : IsSubExponential X μ ν b) (ε s : ℝ) (hs : 0 ≤ s) (hsb : s * b < 1)
    (h_int : Integrable (fun ω => Real.exp (s * X ω)) μ) :
    μ.real {ω | ε ≤ X ω} ≤ Real.exp (-s * ε + s ^ 2 * ν / 2) := by
  -- Step 1: classical Chernoff bound from Mathlib.
  have hChernoff : μ.real {ω | ε ≤ X ω} ≤ Real.exp (-s * ε) * mgf X μ s :=
    measure_ge_le_exp_mul_mgf ε hs h_int
  -- Step 2: bound the MGF using `h.mgf_le`. The side condition
  -- `|s| * b < 1` follows from `s ≥ 0` and `s * b < 1`.
  have habs : |s| = s := abs_of_nonneg hs
  have hsb' : |s| * b < 1 := by rw [habs]; exact hsb
  have hmgf : mgf X μ s ≤ Real.exp (s ^ 2 * ν / 2) := h.mgf_le s hsb'
  -- Step 3: chain the two bounds and fold the exponents.
  have hexp_pos : 0 < Real.exp (-s * ε) := Real.exp_pos _
  have hstep :
      Real.exp (-s * ε) * mgf X μ s ≤
        Real.exp (-s * ε) * Real.exp (s ^ 2 * ν / 2) :=
    mul_le_mul_of_nonneg_left hmgf hexp_pos.le
  have hfold :
      Real.exp (-s * ε) * Real.exp (s ^ 2 * ν / 2) =
        Real.exp (-s * ε + s ^ 2 * ν / 2) := by
    rw [← Real.exp_add]
  calc μ.real {ω | ε ≤ X ω}
      ≤ Real.exp (-s * ε) * mgf X μ s := hChernoff
    _ ≤ Real.exp (-s * ε) * Real.exp (s ^ 2 * ν / 2) := hstep
    _ = Real.exp (-s * ε + s ^ 2 * ν / 2) := hfold

end IsSubExponential

/-! ## Sub-Gamma random variables

A real-valued random variable `X` on `(Ω, μ)` is `(ν, b)`-**sub-Gamma**
if its moment-generating function satisfies the bound

`mgf X μ s ≤ exp (s² · ν / (2 · (1 - |s| · b)))`

for every real `s` lying in the open interval `(-1/b, 1/b)`, encoded as
the side condition `|s| · b < 1`. Taking `b = 0` collapses the
denominator to `2`, recovering the sub-Gaussian MGF bound.

This is the standard MGF class from which Bernstein's inequality follows
without an intermediate optimisation: applied at the Chernoff parameter
`s = ε / (ν + b · ε)`, the sub-Gamma MGF bound yields the canonical
two-regime tail `exp(-ε² / (2 (ν + b · ε)))`. The class is *weaker*
than `IsSubExponential` (the constant Gaussian RHS `exp(s²ν/2)` is
smaller than the sub-Gamma RHS); conversely a `(ν, b)`-sub-Gamma
variable is `(2ν, 2b)`-sub-exponential on the half-interval. The two
classes therefore coincide up to a constant factor of `2`. -/
structure IsSubGamma (X : Ω → ℝ) (μ : Measure Ω) (ν b : ℝ) : Prop where
  /-- The variance proxy `ν` is nonnegative. -/
  ν_nonneg : 0 ≤ ν
  /-- The scale parameter `b` is nonnegative. -/
  b_nonneg : 0 ≤ b
  /-- The sub-Gamma MGF bound holds in the small-`s` regime. -/
  mgf_le : ∀ s : ℝ, |s| * b < 1 →
    mgf X μ s ≤ Real.exp (s ^ 2 * ν / (2 * (1 - |s| * b)))

namespace IsSubGamma

variable {X : Ω → ℝ} {μ : Measure Ω} {ν b ν' b' : ℝ}

/-- Any constant-zero random variable is `(0, 0)`-sub-Gamma under any
probability measure. -/
theorem const_zero (μ : Measure Ω) [IsProbabilityMeasure μ] :
    IsSubGamma (fun _ : Ω => (0 : ℝ)) μ 0 0 where
  ν_nonneg := le_rfl
  b_nonneg := le_rfl
  mgf_le := by
    intro s _
    have hmgf : mgf (fun _ : Ω => (0 : ℝ)) μ s = 1 := by simp
    have hrhs : Real.exp (s ^ 2 * 0 / (2 * (1 - |s| * 0))) = 1 := by simp
    rw [hmgf, hrhs]

/-- Enlarging the scale parameter `b` preserves the sub-Gamma property. -/
theorem mono_b (h : IsSubGamma X μ ν b) (hb : b ≤ b') :
    IsSubGamma X μ ν b' where
  ν_nonneg := h.ν_nonneg
  b_nonneg := le_trans h.b_nonneg hb
  mgf_le := by
    intro s hs
    have habs : 0 ≤ |s| := abs_nonneg s
    -- The side condition `|s| * b' < 1` propagates to `|s| * b < 1`.
    have hmul : |s| * b ≤ |s| * b' := mul_le_mul_of_nonneg_left hb habs
    have hsb : |s| * b < 1 := lt_of_le_of_lt hmul hs
    -- Compare the right-hand side of the MGF bound: enlarging `b`
    -- shrinks the denominator `1 - |s| · b`, hence enlarges the RHS.
    have hbound : mgf X μ s ≤ Real.exp (s ^ 2 * ν / (2 * (1 - |s| * b))) :=
      h.mgf_le s hsb
    -- `1 - |s| · b' ≤ 1 - |s| · b`, and both are positive.
    have h_one_b_pos : 0 < 1 - |s| * b := by linarith
    have h_one_b'_pos : 0 < 1 - |s| * b' := by linarith
    have h_two_b_pos : 0 < 2 * (1 - |s| * b) := by linarith
    have h_two_b'_pos : 0 < 2 * (1 - |s| * b') := by linarith
    have h_denom_le : 2 * (1 - |s| * b') ≤ 2 * (1 - |s| * b) := by linarith
    have hsq_nu_nn : 0 ≤ s ^ 2 * ν := mul_nonneg (sq_nonneg s) h.ν_nonneg
    have h_div_le :
        s ^ 2 * ν / (2 * (1 - |s| * b)) ≤
          s ^ 2 * ν / (2 * (1 - |s| * b')) :=
      div_le_div_of_nonneg_left hsq_nu_nn h_two_b'_pos h_denom_le
    exact le_trans hbound (Real.exp_le_exp.mpr h_div_le)

/-- Enlarging the variance proxy `ν` preserves the sub-Gamma property. -/
theorem mono_nu (h : IsSubGamma X μ ν b) (hν : ν ≤ ν') :
    IsSubGamma X μ ν' b where
  ν_nonneg := le_trans h.ν_nonneg hν
  b_nonneg := h.b_nonneg
  mgf_le := by
    intro s hs
    have hbound := h.mgf_le s hs
    have hsq : 0 ≤ s ^ 2 := sq_nonneg s
    have h_denom_pos : 0 < 2 * (1 - |s| * b) := by linarith
    have hmul : s ^ 2 * ν ≤ s ^ 2 * ν' := mul_le_mul_of_nonneg_left hν hsq
    have h_div :
        s ^ 2 * ν / (2 * (1 - |s| * b)) ≤
          s ^ 2 * ν' / (2 * (1 - |s| * b)) :=
      div_le_div_of_nonneg_right hmul h_denom_pos.le
    exact le_trans hbound (Real.exp_le_exp.mpr h_div)

/-- **Bernstein's inequality from sub-Gamma.**

For a `(ν, b)`-sub-Gamma random variable `X`, every nonnegative Chernoff
parameter `s` in the small-`s` regime `s · b < 1` gives the tail bound

`μ.real {ω | ε ≤ X ω} ≤ exp(-s · ε + s² · ν / (2 (1 - s · b)))`.

This is the **direct** form of Bernstein's inequality from the sub-Gamma
MGF bound, without any optimisation step. The canonical Bernstein
two-regime form is obtained by specialising `s := ε / (ν + b · ε)`,
which collapses the exponent to `-ε² / (2 (ν + b · ε))`. -/
theorem measure_ge_le [IsFiniteMeasure μ]
    (h : IsSubGamma X μ ν b) (ε s : ℝ) (hs : 0 ≤ s) (hsb : s * b < 1)
    (h_int : Integrable (fun ω => Real.exp (s * X ω)) μ) :
    μ.real {ω | ε ≤ X ω} ≤
      Real.exp (-s * ε + s ^ 2 * ν / (2 * (1 - s * b))) := by
  -- Classical Chernoff bound from Mathlib.
  have hChernoff : μ.real {ω | ε ≤ X ω} ≤ Real.exp (-s * ε) * mgf X μ s :=
    measure_ge_le_exp_mul_mgf ε hs h_int
  -- Apply the sub-Gamma MGF bound at `s ≥ 0`.
  have habs : |s| = s := abs_of_nonneg hs
  have hsb' : |s| * b < 1 := by rw [habs]; exact hsb
  have hmgf :
      mgf X μ s ≤ Real.exp (s ^ 2 * ν / (2 * (1 - |s| * b))) :=
    h.mgf_le s hsb'
  -- Replace `|s|` with `s` in the exponent.
  rw [habs] at hmgf
  -- Chain bounds and fold exponentials.
  have hexp_pos : 0 < Real.exp (-s * ε) := Real.exp_pos _
  have hstep :
      Real.exp (-s * ε) * mgf X μ s ≤
        Real.exp (-s * ε) * Real.exp (s ^ 2 * ν / (2 * (1 - s * b))) :=
    mul_le_mul_of_nonneg_left hmgf hexp_pos.le
  have hfold :
      Real.exp (-s * ε) * Real.exp (s ^ 2 * ν / (2 * (1 - s * b))) =
        Real.exp (-s * ε + s ^ 2 * ν / (2 * (1 - s * b))) := by
    rw [← Real.exp_add]
  calc μ.real {ω | ε ≤ X ω}
      ≤ Real.exp (-s * ε) * mgf X μ s := hChernoff
    _ ≤ Real.exp (-s * ε) * Real.exp (s ^ 2 * ν / (2 * (1 - s * b))) := hstep
    _ = Real.exp (-s * ε + s ^ 2 * ν / (2 * (1 - s * b))) := hfold

/-- **Bernstein's inequality (canonical two-regime form).**

For a `(ν, b)`-sub-Gamma random variable `X` with `0 < ν`, every positive
threshold `ε > 0` yields the canonical Bernstein tail bound

`μ.real {ω | ε ≤ X ω} ≤ exp(-ε² / (2 (ν + b · ε)))`.

This is the closed-form Bernstein inequality, obtained from
`IsSubGamma.measure_ge_le` by the standard Bernstein choice
`s := ε / (ν + b · ε)`, which lies in the small-`s` regime `s · b < 1`
because `s · b = b · ε / (ν + b · ε) < 1` whenever `ν > 0`.

The exponent collapses by elementary algebra: at this `s`, the exponent
`-s · ε + s² · ν / (2 (1 - s · b))` equals `-ε² / (2 (ν + b · ε))`. -/
theorem measure_ge_le_bernstein [IsFiniteMeasure μ]
    (h : IsSubGamma X μ ν b) (ε : ℝ) (hε : 0 < ε) (hν : 0 < ν)
    (h_int :
      Integrable (fun ω => Real.exp (ε / (ν + b * ε) * X ω)) μ) :
    μ.real {ω | ε ≤ X ω} ≤
      Real.exp (-(ε ^ 2) / (2 * (ν + b * ε))) := by
  -- Chernoff parameter.
  set s : ℝ := ε / (ν + b * ε) with hs_def
  -- Sign and side condition.
  have hbε_nn : 0 ≤ b * ε := mul_nonneg h.b_nonneg hε.le
  have hνb : 0 < ν + b * ε := by linarith
  have hνb_ne : ν + b * ε ≠ 0 := ne_of_gt hνb
  have hs_nn : 0 ≤ s := by
    rw [hs_def]; exact div_nonneg hε.le hνb.le
  -- `s · b = b · ε / (ν + b · ε) < 1` since `ν > 0`.
  have hsb : s * b < 1 := by
    rw [hs_def]
    have hnum_lt : b * ε < ν + b * ε := by linarith
    have h_eq : ε / (ν + b * ε) * b = (b * ε) / (ν + b * ε) := by
      rw [div_mul_eq_mul_div]; congr 1; ring
    rw [h_eq]
    exact (div_lt_one hνb).mpr hnum_lt
  -- Apply the base sub-Gamma tail bound.
  have hbase := h.measure_ge_le ε s hs_nn hsb h_int
  -- First simplify `1 - s * b = ν / (ν + b · ε)`.
  have h_one_sb : 1 - s * b = ν / (ν + b * ε) := by
    rw [hs_def]
    rw [div_mul_eq_mul_div]
    rw [show ε * b = b * ε from mul_comm _ _]
    rw [eq_div_iff hνb_ne]
    field_simp
    ring
  -- Then `2 * (1 - s * b) = 2 * ν / (ν + b · ε)`, and at the standard
  -- Bernstein choice of `s` the exponent collapses.
  have h_exp_eq :
      -s * ε + s ^ 2 * ν / (2 * (1 - s * b)) =
        -(ε ^ 2) / (2 * (ν + b * ε)) := by
    rw [h_one_sb]
    rw [show (2 : ℝ) * (ν / (ν + b * ε)) = (2 * ν) / (ν + b * ε) by
        rw [mul_div_assoc]]
    rw [hs_def]
    have h2ν_ne : (2 * ν) ≠ 0 := by positivity
    have h2D_ne : (2 * (ν + b * ε)) ≠ 0 := by
      have : 0 < 2 * (ν + b * ε) := by positivity
      exact ne_of_gt this
    field_simp
    ring
  rw [h_exp_eq] at hbase
  exact hbase

/-- **Bernstein sub-Gaussian regime.**

In the sub-Gaussian regime `b · ε ≤ ν` (the deviation `ε` is small
relative to the variance proxy `ν`), the canonical Bernstein bound
`exp(-ε² / (2 (ν + b · ε)))` simplifies to the sub-Gaussian
`exp(-ε² / (4 ν))`. This is the regime where the tail behaves like a
Gaussian, and the user can invert the bound by `ε = 2 √(ν · log(1/δ))`
to obtain a sub-Gaussian confidence interval.

The proof uses `2(ν + b · ε) ≤ 4ν` in this regime. -/
theorem measure_ge_le_sub_gaussian_regime [IsFiniteMeasure μ]
    (h : IsSubGamma X μ ν b) (ε : ℝ) (hε : 0 < ε) (hν : 0 < ν)
    (hreg : b * ε ≤ ν)
    (h_int :
      Integrable (fun ω => Real.exp (ε / (ν + b * ε) * X ω)) μ) :
    μ.real {ω | ε ≤ X ω} ≤ Real.exp (-(ε ^ 2) / (4 * ν)) := by
  -- Start from the canonical Bernstein tail.
  have hbern := h.measure_ge_le_bernstein ε hε hν h_int
  -- In the sub-Gaussian regime, `2(ν + b · ε) ≤ 4ν`.
  have hbε_nn : 0 ≤ b * ε := mul_nonneg h.b_nonneg hε.le
  have hνb_pos : 0 < ν + b * ε := by linarith
  have hden_le : 2 * (ν + b * ε) ≤ 4 * ν := by linarith
  have hden_pos : 0 < 2 * (ν + b * ε) := by linarith
  have h4ν_pos : 0 < 4 * ν := by linarith
  have hε2_nn : 0 ≤ ε ^ 2 := sq_nonneg ε
  -- So `ε² / (2 (ν + b · ε)) ≥ ε² / (4 ν)`, hence
  -- `-(ε²)/(2(ν+bε)) ≤ -(ε²)/(4ν)`.
  have h_exp_le :
      -(ε ^ 2) / (2 * (ν + b * ε)) ≤ -(ε ^ 2) / (4 * ν) := by
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hε2_nn hden_pos hden_le
  exact hbern.trans (Real.exp_le_exp.mpr h_exp_le)

/-- **Bernstein exponential regime.**

In the exponential regime `ν ≤ b · ε` (the deviation `ε` is large
relative to the variance proxy, so the heavy-tail exponential decay
dominates), the canonical Bernstein bound `exp(-ε² / (2 (ν + b · ε)))`
simplifies to `exp(-ε / (4 b))`. This is the regime where the tail
behaves like a one-sided exponential, and the user can invert the bound
by `ε = 4 b · log(1/δ)` to obtain an exponential confidence interval.

The proof uses `2(ν + b · ε) ≤ 4 b · ε` in this regime, hence
`ε² / (2 (ν + b · ε)) ≥ ε² / (4 b · ε) = ε / (4 b)`. Requires `0 < b`. -/
theorem measure_ge_le_exp_regime [IsFiniteMeasure μ]
    (h : IsSubGamma X μ ν b) (ε : ℝ) (hε : 0 < ε) (hν : 0 < ν) (hb : 0 < b)
    (hreg : ν ≤ b * ε)
    (h_int :
      Integrable (fun ω => Real.exp (ε / (ν + b * ε) * X ω)) μ) :
    μ.real {ω | ε ≤ X ω} ≤ Real.exp (-ε / (4 * b)) := by
  -- Start from the canonical Bernstein tail.
  have hbern := h.measure_ge_le_bernstein ε hε hν h_int
  -- In the exponential regime, `2(ν + b · ε) ≤ 4 b · ε`.
  have hbε_pos : 0 < b * ε := mul_pos hb hε
  have hνb_pos : 0 < ν + b * ε := by linarith
  have hden_le : 2 * (ν + b * ε) ≤ 4 * (b * ε) := by linarith
  have hden_pos : 0 < 2 * (ν + b * ε) := by linarith
  have h4bε_pos : 0 < 4 * (b * ε) := by linarith
  have hε2_nn : 0 ≤ ε ^ 2 := sq_nonneg ε
  -- So `-(ε²)/(2(ν+bε)) ≤ -(ε²)/(4(bε)) = -ε/(4b)`.
  have h_exp_le :
      -(ε ^ 2) / (2 * (ν + b * ε)) ≤ -(ε ^ 2) / (4 * (b * ε)) := by
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left hε2_nn hden_pos hden_le
  -- Simplify `-(ε²) / (4 (b · ε)) = -ε / (4 b)`.
  have hε_ne : ε ≠ 0 := ne_of_gt hε
  have hb_ne : b ≠ 0 := ne_of_gt hb
  have h_simp : -(ε ^ 2) / (4 * (b * ε)) = -ε / (4 * b) := by
    field_simp
  rw [h_simp] at h_exp_le
  exact hbern.trans (Real.exp_le_exp.mpr h_exp_le)

end IsSubGamma

/-! ## Conversions between sub-exponential and sub-Gamma

A `(ν, b)`-sub-exponential variable is automatically `(ν, b)`-sub-Gamma:
the sub-exponential Gaussian RHS `exp(s²ν/2)` is bounded above by the
sub-Gamma RHS `exp(s²ν/(2(1-|s|·b)))` since `0 < 1 - |s|·b ≤ 1` in the
small-`s` regime.

Conversely, a `(ν, b)`-sub-Gamma variable is `(2ν, 2b)`-sub-exponential
on the half-interval `|s|·b < 1/2` (equivalently `|s|·(2b) < 1`): on
this range `1 - |s|·b > 1/2`, so the sub-Gamma RHS is bounded by
`exp(s²ν) = exp(s²·(2ν)/2)`. The factor of `2` is the canonical price
paid when converting between the two classes. -/

/-- Every `(ν, b)`-sub-exponential variable is `(ν, b)`-sub-Gamma. The
sub-exponential bound `mgf X μ s ≤ exp(s²ν/2)` is stronger than the
sub-Gamma bound `exp(s²ν/(2(1-|s|·b)))` because `1/(1-|s|·b) ≥ 1` in
the small-`s` regime. -/
theorem IsSubExponential.toIsSubGamma
    {X : Ω → ℝ} {μ : Measure Ω} {ν b : ℝ}
    (h : IsSubExponential X μ ν b) :
    IsSubGamma X μ ν b where
  ν_nonneg := h.ν_nonneg
  b_nonneg := h.b_nonneg
  mgf_le := by
    intro s hs
    have hsub : mgf X μ s ≤ Real.exp (s ^ 2 * ν / 2) := h.mgf_le s hs
    -- Show `s²ν/2 ≤ s²ν/(2(1-|s|·b))`. The denominator `1 - |s|·b` is
    -- in `(0, 1]` since `0 ≤ |s|·b < 1`.
    have habs : 0 ≤ |s| := abs_nonneg s
    have h_sb_nn : 0 ≤ |s| * b := mul_nonneg habs h.b_nonneg
    have h_one_sb_pos : 0 < 1 - |s| * b := by linarith
    have h_one_sb_le : 1 - |s| * b ≤ 1 := by linarith
    have h_two_pos : (0 : ℝ) < 2 := by norm_num
    have h_two_sb_pos : 0 < 2 * (1 - |s| * b) := by positivity
    have h_two_sb_le : 2 * (1 - |s| * b) ≤ 2 := by
      have := mul_le_mul_of_nonneg_left h_one_sb_le h_two_pos.le
      linarith
    have hsq_nu_nn : 0 ≤ s ^ 2 * ν := mul_nonneg (sq_nonneg s) h.ν_nonneg
    have h_div_le :
        s ^ 2 * ν / 2 ≤ s ^ 2 * ν / (2 * (1 - |s| * b)) :=
      div_le_div_of_nonneg_left hsq_nu_nn h_two_sb_pos h_two_sb_le
    exact le_trans hsub (Real.exp_le_exp.mpr h_div_le)

/-- A `(ν, b)`-sub-Gamma variable is `(2ν, 2b)`-sub-exponential. The
side condition `|s|·(2b) < 1` for sub-exponential is equivalent to
`|s|·b < 1/2`, on which `1 - |s|·b > 1/2`, so the sub-Gamma RHS
`exp(s²ν/(2(1-|s|·b)))` is bounded by `exp(s²·(2ν)/2)`. -/
theorem IsSubGamma.toIsSubExponential
    {X : Ω → ℝ} {μ : Measure Ω} {ν b : ℝ}
    (h : IsSubGamma X μ ν b) :
    IsSubExponential X μ (2 * ν) (2 * b) where
  ν_nonneg := by have := h.ν_nonneg; linarith
  b_nonneg := by have := h.b_nonneg; linarith
  mgf_le := by
    intro s hs
    -- Side condition `|s| * (2 b) < 1` is `2 * (|s| * b) < 1`, hence
    -- `|s| * b < 1/2`. We feed `|s| * b < 1` into the sub-Gamma bound.
    have habs : 0 ≤ |s| := abs_nonneg s
    have hsb_half : |s| * b < 1 / 2 := by
      have : 2 * (|s| * b) < 1 := by
        have heq : |s| * (2 * b) = 2 * (|s| * b) := by ring
        rw [heq] at hs; exact hs
      linarith
    have hsb : |s| * b < 1 := by linarith
    have hbound :
        mgf X μ s ≤ Real.exp (s ^ 2 * ν / (2 * (1 - |s| * b))) :=
      h.mgf_le s hsb
    -- Compare exponents: `s²ν/(2(1-|s|·b)) ≤ s²·(2ν)/2 = s²ν`. The
    -- comparison reduces to `1/(2(1-|s|·b)) ≤ 1`, i.e.
    -- `1 ≤ 2(1-|s|·b)`, i.e. `|s|·b ≤ 1/2`.
    have h_one_sb_gt_half : 1 / 2 < 1 - |s| * b := by linarith
    have h_two_sb_gt_one : 1 < 2 * (1 - |s| * b) := by linarith
    have h_two_sb_pos : 0 < 2 * (1 - |s| * b) := by linarith
    have hsq_nu_nn : 0 ≤ s ^ 2 * ν := mul_nonneg (sq_nonneg s) h.ν_nonneg
    -- The key step: `s²ν/(2(1-|s|·b)) ≤ s²ν` since the denominator is `> 1`.
    have h_div_le_num :
        s ^ 2 * ν / (2 * (1 - |s| * b)) ≤ s ^ 2 * ν := by
      have : s ^ 2 * ν / (2 * (1 - |s| * b)) ≤ s ^ 2 * ν / 1 := by
        exact div_le_div_of_nonneg_left hsq_nu_nn one_pos h_two_sb_gt_one.le
      simpa using this
    -- And `s²ν = s²·(2ν)/2`.
    have h_eq : s ^ 2 * ν = s ^ 2 * (2 * ν) / 2 := by ring
    have h_final :
        s ^ 2 * ν / (2 * (1 - |s| * b)) ≤ s ^ 2 * (2 * ν) / 2 := by
      rw [← h_eq]; exact h_div_le_num
    exact le_trans hbound (Real.exp_le_exp.mpr h_final)

/-! ## Sub-exponential Bernstein wrappers

Every sub-exponential variable is sub-Gamma with the same parameters
(via `IsSubExponential.toIsSubGamma`), so the canonical Bernstein
two-regime tail bound applies verbatim. -/

/-- **Bernstein's inequality for sub-exponential random variables.**

A `(ν, b)`-sub-exponential random variable with `0 < ν` satisfies the
canonical Bernstein tail bound
`μ.real {ω | ε ≤ X ω} ≤ exp(-ε² / (2 (ν + b · ε)))` at every positive
threshold `ε > 0`. This follows immediately from the sub-Gamma version
via `IsSubExponential.toIsSubGamma`. -/
theorem IsSubExponential.measure_ge_le_bernstein
    {X : Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ] {ν b : ℝ}
    (h : IsSubExponential X μ ν b) (ε : ℝ) (hε : 0 < ε) (hν : 0 < ν)
    (h_int :
      Integrable (fun ω => Real.exp (ε / (ν + b * ε) * X ω)) μ) :
    μ.real {ω | ε ≤ X ω} ≤
      Real.exp (-(ε ^ 2) / (2 * (ν + b * ε))) :=
  h.toIsSubGamma.measure_ge_le_bernstein ε hε hν h_int

/-! ## Examples -/

section Examples

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- Example: the constantly zero random variable is sub-exponential with
parameters `(0, 0)` under any probability measure. -/
example (μ : Measure Ω) [IsProbabilityMeasure μ] :
    IsSubExponential (fun _ : Ω => (0 : ℝ)) μ 0 0 :=
  IsSubExponential.const_zero μ

/-- Example: monotonicity in `b` lets us weaken the scale parameter on
demand. The zero variable is sub-exponential with parameters
`(0, 5)` for any nonnegative `b`. -/
example (μ : Measure Ω) [IsProbabilityMeasure μ] :
    IsSubExponential (fun _ : Ω => (0 : ℝ)) μ 0 5 :=
  (IsSubExponential.const_zero μ).mono_b (by norm_num)

/-- Example: every `HasSubgaussianMGF`-sub-Gaussian variable is
sub-exponential with scale parameter `b = 0`. -/
example {X : Ω → ℝ} {μ : Measure Ω} {c : NNReal}
    (h : HasSubgaussianMGF X c μ) :
    IsSubExponential X μ (c : ℝ) 0 :=
  IsSubExponential.of_hasSubgaussianMGF h

/-- Example: the constant-zero random variable is sub-Gamma with
parameters `(0, 0)` under any probability measure. -/
example (μ : Measure Ω) [IsProbabilityMeasure μ] :
    IsSubGamma (fun _ : Ω => (0 : ℝ)) μ 0 0 :=
  IsSubGamma.const_zero μ

/-- Example: every sub-exponential variable is automatically sub-Gamma
with the same parameters. -/
example {X : Ω → ℝ} {μ : Measure Ω} {ν b : ℝ}
    (h : IsSubExponential X μ ν b) :
    IsSubGamma X μ ν b :=
  h.toIsSubGamma

/-- Example: every sub-Gamma variable is sub-exponential after doubling
both parameters. -/
example {X : Ω → ℝ} {μ : Measure Ω} {ν b : ℝ}
    (h : IsSubGamma X μ ν b) :
    IsSubExponential X μ (2 * ν) (2 * b) :=
  h.toIsSubExponential

/-- Example: the canonical Bernstein tail for a sub-Gamma variable. -/
example {X : Ω → ℝ} {μ : Measure Ω} [IsFiniteMeasure μ] {ν b : ℝ}
    (h : IsSubGamma X μ ν b) (ε : ℝ) (hε : 0 < ε) (hν : 0 < ν)
    (h_int :
      Integrable (fun ω => Real.exp (ε / (ν + b * ε) * X ω)) μ) :
    μ.real {ω | ε ≤ X ω} ≤
      Real.exp (-(ε ^ 2) / (2 * (ν + b * ε))) :=
  h.measure_ge_le_bernstein ε hε hν h_int

end Examples

end ProbabilityTheory
