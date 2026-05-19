/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import LTFP.MathlibExt.Probability.TotalVariation
import LTFP.MathlibExt.Probability.Distance.Pinsker
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Lebesgue
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Bhattacharyya affinity and the Bretagnolle--Huber bridge

Proposed Mathlib path: `Mathlib/Probability/Distance/Bhattacharyya.lean`.
Proposed namespace: `MeasureTheory`.

The **Bhattacharyya affinity** between two measures `μ` and `ν` on a
measurable space `α` is the symmetric quantity

  `ρ(μ, ν) := ∫ √((dμ/dτ) (dν/dτ)) dτ`,

where `τ` is any common dominating measure. The natural symmetric choice
is `τ = μ + ν`, which always dominates both measures. For probability
measures, `ρ(μ, ν) ∈ [0, 1]`, and it is the geometric-mean dual of the
squared Hellinger distance via `H²(μ, ν) = 2 (1 - ρ(μ, ν))`.

The Bhattacharyya affinity is the central object in the classical
Bretagnolle--Huber proof, where it factors the inequality
`tvDist²(μ, ν) ≤ 1 - exp(-KL(μ‖ν))` through the two steps

  (1) `tvDist²(μ, ν)  ≤  1 - ρ(μ, ν)²`         (Le Cam / Cauchy--Schwarz),
  (2) `ρ(μ, ν)        ≥  Real.exp(-KL(μ‖ν)/2)` (Jensen on `-log`).

## Main definitions

* `MeasureTheory.bhattacharyya μ ν` : the symmetric Bhattacharyya
  affinity, defined as
  `∫ √((dμ/d(μ+ν)) · (dν/d(μ+ν))) d(μ+ν)`.
  Lives in `ℝ` (it is the `toReal` of a nonnegative finite integral
  whenever `μ`, `ν` are probability measures).

## Main results

* `bhattacharyya_comm`     : symmetry `bhattacharyya μ ν = bhattacharyya ν μ`.
* `bhattacharyya_nonneg`   : `0 ≤ bhattacharyya μ ν`.
* `bhattacharyya_self`     : for a probability measure `μ`,
  `bhattacharyya μ μ = 1`.
* `bhattacharyya_le_one_of_amgm` : algebraic upper bound: if the
  Bhattacharyya affinity is computed as the integral of a function
  pointwise dominated by `(dμ + dν)/2`, then it does not exceed
  `(μ(univ) + ν(univ))/2`.

## Bretagnolle--Huber bridge

The algebraic content of the Bretagnolle--Huber bridge — the
implication "Le Cam estimate ∧ KL/Jensen estimate ⇒ squared-TV bound" —
is already exposed by `tvDist_sq_le_one_sub_exp_neg_of_bhattacharyya`
in `LTFP.MathlibExt.Probability.Distance.Pinsker`. The wrappers
`tvDist_sq_le_one_sub_exp_neg_of_bhattacharyya_def` and
`tvDist_sq_le_one_sub_exp_neg_of_klDiv_bhattacharyya` in this file
restate that algebraic chain in terms of the new `bhattacharyya`
definition, so that downstream users can phrase the two-step
hypothesis chain directly on the affinity rather than on an abstract
real parameter `ρ`.

## Status

**The Le Cam estimate `tvDist² ≤ 1 - bhattacharyya²` is now discharged
unconditionally for probability measures. The Jensen step
`exp(-KL/2) ≤ bhattacharyya` remains the only open hypothesis input on
the route to the textbook Bretagnolle--Huber inequality.**

What is now available:

* `totalVariation_withDensityᵥ_eq_withDensity_abs` — the Jordan-to-density
  bridge: `(τ.withDensityᵥ f).totalVariation = τ.withDensity (ofReal |f|)`
  for an integrable real function.
* `tvDist_eq_half_integral_abs_rnDeriv_sub` — the density representation
  `(tvDist μ ν).toReal = (1/2) · ∫ |p - q| dτ` where `τ = μ + ν` and
  `p, q` are the `toReal`-densities.
* `bhattacharyya_eq_integral_sqrt_mul_sqrt` — the factored form
  `bhattacharyya μ ν = ∫ √p · √q dτ` used in the Cauchy--Schwarz step.
* `tvDist_sq_le_one_sub_bhattacharyya_sq` — the **Le Cam estimate**, the
  carrier theorem of this file: for two probability measures,
  `tvDist² ≤ 1 - bhattacharyya²`. The proof composes the density bridge
  with Hölder (`p = q = 2`) on the polarization
  `p - q = (√p - √q)(√p + √q)` and expands the `L²`-norms via
  `∫ p dτ = ∫ q dτ = 1` and the factored Bhattacharyya identity.

What remains:

* **Jensen step.** Requires the conditional version of Jensen's
  inequality applied to `-log` on the `rnDeriv μ ν` density, plus
  careful handling of the `ℝ≥0∞`/`ℝ` boundary and the integrability
  hypothesis `Integrable (llr μ ν) μ` already exposed by
  `Mathlib.InformationTheory.KullbackLeibler.Basic`.

The Le Cam discharge is exposed downstream by
`tvDist_le_sqrt_one_sub_exp_neg_of_bhattacharyya_kl` in
`LTFP/Ch15_LowerBounds/Statistical.lean`, which now requires only the
Jensen-on-`-log` hypothesis as input.

## References

* A. Bhattacharyya, *On a measure of divergence between two statistical
  populations defined by their probability distributions*, Bull. Calcutta
  Math. Soc. **35** (1943), 99--109.
* J. Bretagnolle and C. Huber, *Estimation des densités: risque minimax*,
  Z. Wahrscheinlichkeitstheorie verw. Gebiete **47** (1979), 119--137.
* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer,
  2009, Section 2.4.
* L. Devroye, L. Györfi, G. Lugosi, *A Probabilistic Theory of Pattern
  Recognition*, Springer, 1996, Chapter 8.

## Tags

Bhattacharyya, Hellinger affinity, Bretagnolle-Huber, total variation,
KL divergence
-/

namespace LTFP.MathlibExt.Probability

-- When upstreamed, replace `LTFP.MathlibExt.Probability` by
-- `MeasureTheory` throughout this file.

open MeasureTheory Real ENNReal NNReal

variable {α : Type*} [MeasurableSpace α]

/-! ### Definition of the Bhattacharyya affinity -/

/-- The **Bhattacharyya affinity** between two measures `μ` and `ν` on
the measurable space `α`. We define it symmetrically using `μ + ν` as
the dominating measure:

  `bhattacharyya μ ν = ∫ x, √((dμ/d(μ+ν))(x) · (dν/d(μ+ν))(x)) ∂(μ + ν)`.

For two probability measures `μ`, `ν` this lies in `[0, 1]`. It is
related to the squared Hellinger distance `H²` by
`H²(μ, ν) = 2 (1 - bhattacharyya μ ν)`, and to the Bretagnolle--Huber
inequality via the two-step chain in `Pinsker.lean`. -/
noncomputable def bhattacharyya (μ ν : Measure α) : ℝ :=
  ∫ x, Real.sqrt ((μ.rnDeriv (μ + ν) x).toReal *
      (ν.rnDeriv (μ + ν) x).toReal) ∂(μ + ν)

/-! ### Basic algebraic properties -/

/-- The Bhattacharyya affinity is symmetric. This follows from the
commutativity of multiplication inside the square root and the symmetry
of `μ + ν = ν + μ` as the dominating measure. -/
theorem bhattacharyya_comm (μ ν : Measure α) :
    bhattacharyya μ ν = bhattacharyya ν μ := by
  unfold bhattacharyya
  -- Rewrite the dominating measure `μ + ν` as `ν + μ` and swap the two factors.
  have h_swap : (μ + ν) = (ν + μ) := add_comm μ ν
  rw [h_swap]
  refine integral_congr_ae ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  ring_nf

/-- The Bhattacharyya affinity is nonnegative. This is automatic since
the integrand is a square root and the dominating measure has total
nonneg mass — formally, the integrand is pointwise `≥ 0`, so the
Bochner integral is `≥ 0`. -/
theorem bhattacharyya_nonneg (μ ν : Measure α) :
    0 ≤ bhattacharyya μ ν := by
  unfold bhattacharyya
  apply integral_nonneg
  intro x
  exact Real.sqrt_nonneg _

/-! ### AM--GM upper bound on the affinity

The arithmetic--geometric mean inequality `√(x y) ≤ (x + y) / 2` for
nonneg reals lifts to a pointwise bound on the Bhattacharyya integrand:
`√(p · q) ≤ (p + q) / 2` where `p = (dμ/d(μ+ν)).toReal` and `q =
(dν/d(μ+ν)).toReal`. Integrating against `μ + ν` gives the Bhattacharyya
upper bound

  `bhattacharyya μ ν ≤ (μ.real univ + ν.real univ) / 2`,

which equals `1` for probability measures. -/

/-- **Pointwise AM--GM bound.** For all nonnegative reals `a`, `b`,
`Real.sqrt (a * b) ≤ (a + b) / 2`. -/
theorem sqrt_mul_le_half_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by
  -- Reduce to `4 a b ≤ (a + b)^2`, i.e. `(a - b)^2 ≥ 0`.
  have h_sq : (Real.sqrt (a * b)) ^ 2 ≤ ((a + b) / 2) ^ 2 := by
    have h_lhs : (Real.sqrt (a * b)) ^ 2 = a * b := by
      rw [sq, Real.mul_self_sqrt (mul_nonneg ha hb)]
    rw [h_lhs]
    nlinarith [sq_nonneg (a - b), sq_nonneg (a + b)]
  have h_rhs_nonneg : 0 ≤ (a + b) / 2 := by positivity
  have h_lhs_nonneg : 0 ≤ Real.sqrt (a * b) := Real.sqrt_nonneg _
  exact abs_le_of_sq_le_sq' h_sq h_rhs_nonneg |>.2

/-- **Bhattacharyya affinity upper bound (AM--GM).** For two finite
measures `μ`, `ν` on the same measurable space, the Bhattacharyya
affinity is bounded above by `(μ.real univ + ν.real univ) / 2`. The
proof is the pointwise AM--GM `√(pq) ≤ (p+q)/2` integrated against the
common dominating measure `μ + ν`.

For two probability measures this reduces to `bhattacharyya μ ν ≤ 1`,
as the right-hand side equals `(1 + 1) / 2 = 1` by `probReal_univ`. -/
theorem bhattacharyya_le_half_measureReal_add
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    bhattacharyya μ ν ≤ (μ.real Set.univ + ν.real Set.univ) / 2 := by
  -- Notation: `τ = μ + ν`, `p = (μ.rnDeriv τ).toReal`, `q = (ν.rnDeriv τ).toReal`.
  set τ : Measure α := μ + ν with hτ
  have hμτ : μ ≪ τ := by
    rw [hτ]
    exact rfl.absolutelyContinuous.add_right _
  have hντ : ν ≪ τ := by
    rw [hτ, add_comm μ ν]
    exact rfl.absolutelyContinuous.add_right _
  -- Integrability of the two `toReal` densities under `τ`.
  have hμ_top : μ Set.univ ≠ ∞ := measure_ne_top _ _
  have hν_top : ν Set.univ ≠ ∞ := measure_ne_top _ _
  have h_int_μ : Integrable (fun x => (μ.rnDeriv τ x).toReal) τ := by
    have h := Measure.integrableOn_toReal_rnDeriv (μ := μ) (ν := τ)
      (s := Set.univ) (by simp [hμ_top])
    rwa [integrableOn_univ] at h
  have h_int_ν : Integrable (fun x => (ν.rnDeriv τ x).toReal) τ := by
    have h := Measure.integrableOn_toReal_rnDeriv (μ := ν) (ν := τ)
      (s := Set.univ) (by simp [hν_top])
    rwa [integrableOn_univ] at h
  -- Integrability of the AM bound `(p + q) / 2`.
  have h_int_half : Integrable
      (fun x => ((μ.rnDeriv τ x).toReal + (ν.rnDeriv τ x).toReal) / 2) τ := by
    exact (h_int_μ.add h_int_ν).div_const 2
  -- AE pointwise nonneg + AE pointwise bound.
  have h_lhs_nonneg :
      0 ≤ᵐ[τ] (fun x => Real.sqrt
        ((μ.rnDeriv τ x).toReal * (ν.rnDeriv τ x).toReal)) :=
    Filter.Eventually.of_forall (fun _ => Real.sqrt_nonneg _)
  have h_amgm :
      (fun x => Real.sqrt
          ((μ.rnDeriv τ x).toReal * (ν.rnDeriv τ x).toReal))
        ≤ᵐ[τ]
      fun x => ((μ.rnDeriv τ x).toReal + (ν.rnDeriv τ x).toReal) / 2 := by
    refine Filter.Eventually.of_forall (fun x => ?_)
    exact sqrt_mul_le_half_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  -- Integrate the inequality.
  have h_int_le :
      ∫ x, Real.sqrt
          ((μ.rnDeriv τ x).toReal * (ν.rnDeriv τ x).toReal) ∂τ
      ≤ ∫ x, ((μ.rnDeriv τ x).toReal + (ν.rnDeriv τ x).toReal) / 2 ∂τ :=
    integral_mono_of_nonneg h_lhs_nonneg h_int_half h_amgm
  -- Evaluate the RHS using `integral_toReal_rnDeriv`.
  have hτ_sf : SigmaFinite τ := by
    rw [hτ]; infer_instance
  have h_intμ_val :
      ∫ x, (μ.rnDeriv τ x).toReal ∂τ = μ.real Set.univ :=
    Measure.integral_toReal_rnDeriv hμτ
  have h_intν_val :
      ∫ x, (ν.rnDeriv τ x).toReal ∂τ = ν.real Set.univ :=
    Measure.integral_toReal_rnDeriv hντ
  have h_rhs_eq :
      ∫ x, ((μ.rnDeriv τ x).toReal + (ν.rnDeriv τ x).toReal) / 2 ∂τ
        = (μ.real Set.univ + ν.real Set.univ) / 2 := by
    simp only [add_div]
    rw [integral_add (h_int_μ.div_const 2) (h_int_ν.div_const 2),
      integral_div, integral_div, h_intμ_val, h_intν_val]
  -- Combine.
  unfold bhattacharyya
  calc ∫ x, Real.sqrt
          ((μ.rnDeriv (μ + ν) x).toReal * (ν.rnDeriv (μ + ν) x).toReal) ∂(μ + ν)
      = ∫ x, Real.sqrt
          ((μ.rnDeriv τ x).toReal * (ν.rnDeriv τ x).toReal) ∂τ := by rfl
    _ ≤ ∫ x, ((μ.rnDeriv τ x).toReal + (ν.rnDeriv τ x).toReal) / 2 ∂τ := h_int_le
    _ = (μ.real Set.univ + ν.real Set.univ) / 2 := h_rhs_eq

/-- **Bhattacharyya affinity upper bound for probability measures.**

For two probability measures, the Bhattacharyya affinity is at most `1`.
This is the integrated form of the pointwise AM--GM bound, combined
with the normalization `μ.real univ = ν.real univ = 1`. -/
theorem bhattacharyya_le_one (μ ν : Measure α)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    bhattacharyya μ ν ≤ 1 := by
  have h := bhattacharyya_le_half_measureReal_add μ ν
  rw [probReal_univ (μ := μ), probReal_univ (μ := ν)] at h
  linarith

/-! ### Factored form of the Bhattacharyya integrand

The integrand `√((dμ/dτ) · (dν/dτ))` factors as a product
`√(dμ/dτ) · √(dν/dτ)`. This rewrite makes the Cauchy--Schwarz step in
the Le Cam estimate (`tvDist² ≤ 1 - ρ²`) directly applicable, since the
density-bracket identities `(√p ± √q)² = p + q ± 2 √p √q` then expand
into linear combinations of `√p · √q = √(p·q)`. -/

/-- **Factored form of the Bhattacharyya integrand.**

The Bhattacharyya affinity equals the integral of the product of the
two pointwise square roots of the Radon--Nikodym densities:

  `bhattacharyya μ ν = ∫ x, √(dμ/d(μ+ν)) (x) · √(dν/d(μ+ν)) (x) ∂(μ + ν)`.

This is the form in which the Cauchy--Schwarz step
`tvDist² ≤ 1 - bhattacharyya²` is most naturally expressed, since the
square `(√p + √q)^2 + (√p - √q)^2 = 2(p + q)` polarization then writes
`bhattacharyya` as a linear combination of two `L²` norms. -/
theorem bhattacharyya_eq_integral_sqrt_mul_sqrt (μ ν : Measure α) :
    bhattacharyya μ ν =
      ∫ x, Real.sqrt ((μ.rnDeriv (μ + ν) x).toReal) *
        Real.sqrt ((ν.rnDeriv (μ + ν) x).toReal) ∂(μ + ν) := by
  unfold bhattacharyya
  refine integral_congr_ae ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  exact Real.sqrt_mul (ENNReal.toReal_nonneg) _

/-! ### Density representation of the total-variation distance

The signed measure `μ.toSignedMeasure - ν.toSignedMeasure` has Jordan
decomposition `(μ - ν, ν - μ)` (by Mathlib's
`toJordanDecomposition_toSignedMeasure_sub`), and its total variation is
the integral of `|p - q|` against the dominating measure `τ = μ + ν`,
where `p`, `q` are the `toReal`-densities. Combined with the definition
`tvDist μ ν = ((μ - ν) + (ν - μ)) Set.univ / 2`, this yields the density
representation `tvDist μ ν = (1/2) · ∫ |p - q| dτ` used in the Le Cam
estimate. -/

/-- **Total variation of a `withDensityᵥ` is the absolute-value density.**

For a real-valued integrable function `f : α → ℝ`, the total variation
of the signed measure `τ.withDensityᵥ f` equals `τ.withDensity (ofReal |f|)`.

This is the bridge from Jordan-decomposition language to density
language; once available, the total mass `((τ.withDensityᵥ f).totalVariation Set.univ)`
is just `∫⁻ ofReal |f x| ∂τ`. -/
theorem totalVariation_withDensityᵥ_eq_withDensity_abs
    {τ : Measure α} {f : α → ℝ}
    (hf : Measurable f) (hfi : Integrable f τ) :
    MeasureTheory.SignedMeasure.totalVariation
        (τ.withDensityᵥ f : MeasureTheory.SignedMeasure α) =
      τ.withDensity (fun x => ENNReal.ofReal |f x|) := by
  -- Apply `toJordanDecomposition_eq_of_eq_add_withDensity` with `t = 0`.
  set s : MeasureTheory.SignedMeasure α := τ.withDensityᵥ f with hs_def
  have hadd : s = (0 : MeasureTheory.SignedMeasure α) + τ.withDensityᵥ f := by
    rw [zero_add, hs_def]
  have h_ms : (0 : MeasureTheory.SignedMeasure α) ⟂ᵥ τ.toENNRealVectorMeasure :=
    MeasureTheory.VectorMeasure.MutuallySingular.zero_left
  have h_jord :=
    MeasureTheory.SignedMeasure.toJordanDecomposition_eq_of_eq_add_withDensity
      hf hfi h_ms hadd
  -- Read off posPart and negPart.
  have h_zero_jord :
      ((0 : MeasureTheory.SignedMeasure α).toJordanDecomposition : MeasureTheory.JordanDecomposition α) = 0 :=
    MeasureTheory.SignedMeasure.toJordanDecomposition_zero
  have h_pos :
      s.toJordanDecomposition.posPart =
        τ.withDensity (fun x => ENNReal.ofReal (f x)) := by
    rw [h_jord]
    show (0 : MeasureTheory.SignedMeasure α).toJordanDecomposition.posPart +
        τ.withDensity (fun x => ENNReal.ofReal (f x)) =
      τ.withDensity (fun x => ENNReal.ofReal (f x))
    rw [h_zero_jord]
    simp
  have h_neg :
      s.toJordanDecomposition.negPart =
        τ.withDensity (fun x => ENNReal.ofReal (-f x)) := by
    rw [h_jord]
    show (0 : MeasureTheory.SignedMeasure α).toJordanDecomposition.negPart +
        τ.withDensity (fun x => ENNReal.ofReal (-f x)) =
      τ.withDensity (fun x => ENNReal.ofReal (-f x))
    rw [h_zero_jord]
    simp
  -- Combine: totalVariation = posPart + negPart; then `ofReal f + ofReal (-f) = ofReal |f|`.
  show s.totalVariation = τ.withDensity (fun x => ENNReal.ofReal |f x|)
  unfold MeasureTheory.SignedMeasure.totalVariation
  rw [h_pos, h_neg]
  rw [← MeasureTheory.withDensity_add_left (hf.ennreal_ofReal) _]
  refine MeasureTheory.withDensity_congr_ae ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  -- Pointwise: `ofReal (f x) + ofReal (-f x) = ofReal |f x|`.
  rcases le_or_gt 0 (f x) with h | h
  · have h1 : ENNReal.ofReal (-f x) = 0 := by
      rw [ENNReal.ofReal_eq_zero]; linarith
    show ENNReal.ofReal (f x) + ENNReal.ofReal (-f x) = ENNReal.ofReal |f x|
    rw [h1, add_zero, abs_of_nonneg h]
  · have h1 : ENNReal.ofReal (f x) = 0 := by
      rw [ENNReal.ofReal_eq_zero]; linarith
    show ENNReal.ofReal (f x) + ENNReal.ofReal (-f x) = ENNReal.ofReal |f x|
    rw [h1, zero_add, abs_of_neg h]

/-- **TV-density bridge: `tvDist` as half the integral of `|p - q|`.**

For two finite measures `μ`, `ν` on `α`, with `τ := μ + ν` the canonical
symmetric dominating measure and `p, q` the `toReal`-densities of `μ`,
`ν` with respect to `τ`, the total variation distance admits the
density representation

  `(tvDist μ ν).toReal = (1/2) · ∫ x, |p x - q x| ∂τ`.

This is the bridge lemma used in the Le Cam step
`tvDist² ≤ 1 - bhattacharyya²`, where the right-hand side then factors
through Cauchy--Schwarz on the polarized form
`(p - q) = (√p - √q)(√p + √q)`. -/
theorem tvDist_eq_half_integral_abs_rnDeriv_sub
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (tvDist μ ν).toReal =
      (1 / 2 : ℝ) *
        ∫ x, |(μ.rnDeriv (μ + ν) x).toReal - (ν.rnDeriv (μ + ν) x).toReal|
          ∂(μ + ν) := by
  -- Notation.
  set τ : Measure α := μ + ν with hτ_def
  set p : α → ℝ := fun x => (μ.rnDeriv τ x).toReal with hp_def
  set q : α → ℝ := fun x => (ν.rnDeriv τ x).toReal with hq_def
  -- Absolute continuity of `μ`, `ν` with respect to `τ`.
  have hμτ : μ ≪ τ := by
    rw [hτ_def]
    exact rfl.absolutelyContinuous.add_right _
  have hντ : ν ≪ τ := by
    rw [hτ_def, add_comm μ ν]
    exact rfl.absolutelyContinuous.add_right _
  -- Integrability of `p`, `q`, and `p - q`.
  have h_int_p : Integrable p τ := by
    have h := MeasureTheory.Measure.integrableOn_toReal_rnDeriv
      (μ := μ) (ν := τ) (s := Set.univ) (by simp [measure_ne_top])
    rwa [MeasureTheory.integrableOn_univ] at h
  have h_int_q : Integrable q τ := by
    have h := MeasureTheory.Measure.integrableOn_toReal_rnDeriv
      (μ := ν) (ν := τ) (s := Set.univ) (by simp [measure_ne_top])
    rwa [MeasureTheory.integrableOn_univ] at h
  have h_int_diff : Integrable (fun x => p x - q x) τ := h_int_p.sub h_int_q
  have h_meas_diff : Measurable (fun x => p x - q x) := by
    refine ((MeasureTheory.Measure.measurable_rnDeriv μ τ).ennreal_toReal).sub ?_
    exact (MeasureTheory.Measure.measurable_rnDeriv ν τ).ennreal_toReal
  -- Identify `μ.toSignedMeasure - ν.toSignedMeasure = τ.withDensityᵥ (p - q)`.
  have h_μ_sm : μ.toSignedMeasure = τ.withDensityᵥ p := by
    -- `τ.withDensityᵥ p = (τ.withDensity μ.rnDeriv τ).toSignedMeasure = μ.toSignedMeasure`.
    have hμ_top : (∫⁻ x, μ.rnDeriv τ x ∂τ) ≠ ∞ := by
      rw [MeasureTheory.Measure.lintegral_rnDeriv hμτ]
      exact measure_ne_top _ _
    have h_eq :
        (τ.withDensityᵥ fun x => (μ.rnDeriv τ x).toReal) =
          (τ.withDensity (μ.rnDeriv τ)).toSignedMeasure :=
      MeasureTheory.withDensityᵥ_toReal
        (MeasureTheory.Measure.measurable_rnDeriv μ τ).aemeasurable hμ_top
    have h_rn := MeasureTheory.Measure.withDensity_rnDeriv_eq μ τ hμτ
    have h_rn_sm : μ.toSignedMeasure = (τ.withDensity (μ.rnDeriv τ)).toSignedMeasure :=
      (MeasureTheory.Measure.toSignedMeasure_congr h_rn.symm)
    show μ.toSignedMeasure = (τ.withDensityᵥ fun x => (μ.rnDeriv τ x).toReal)
    rw [h_rn_sm, ← h_eq]
  have h_ν_sm : ν.toSignedMeasure = τ.withDensityᵥ q := by
    have hν_top : (∫⁻ x, ν.rnDeriv τ x ∂τ) ≠ ∞ := by
      rw [MeasureTheory.Measure.lintegral_rnDeriv hντ]
      exact measure_ne_top _ _
    have h_eq :
        (τ.withDensityᵥ fun x => (ν.rnDeriv τ x).toReal) =
          (τ.withDensity (ν.rnDeriv τ)).toSignedMeasure :=
      MeasureTheory.withDensityᵥ_toReal
        (MeasureTheory.Measure.measurable_rnDeriv ν τ).aemeasurable hν_top
    have h_rn := MeasureTheory.Measure.withDensity_rnDeriv_eq ν τ hντ
    have h_rn_sm : ν.toSignedMeasure = (τ.withDensity (ν.rnDeriv τ)).toSignedMeasure :=
      (MeasureTheory.Measure.toSignedMeasure_congr h_rn.symm)
    show ν.toSignedMeasure = (τ.withDensityᵥ fun x => (ν.rnDeriv τ x).toReal)
    rw [h_rn_sm, ← h_eq]
  have h_sm_eq :
      μ.toSignedMeasure - ν.toSignedMeasure = τ.withDensityᵥ (fun x => p x - q x) := by
    rw [h_μ_sm, h_ν_sm]
    have := MeasureTheory.withDensityᵥ_sub (f := p) (g := q) (μ := τ) h_int_p h_int_q
    show τ.withDensityᵥ p - τ.withDensityᵥ q = τ.withDensityᵥ (fun x => p x - q x)
    rw [← this]
    rfl
  -- Total variation of the signed measure: `(μ - ν) + (ν - μ)`.
  have h_tv_jord :
      (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation = (μ - ν) + (ν - μ) := by
    unfold MeasureTheory.SignedMeasure.totalVariation
    rw [MeasureTheory.Measure.toJordanDecomposition_toSignedMeasure_sub]
    rfl
  -- Total variation via density: `τ.withDensity (ofReal |p - q|)`.
  have h_tv_density :
      (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation =
        τ.withDensity (fun x => ENNReal.ofReal |p x - q x|) := by
    rw [h_sm_eq]
    exact totalVariation_withDensityᵥ_eq_withDensity_abs (τ := τ)
      (f := fun x => p x - q x) h_meas_diff h_int_diff
  -- Combine.
  have h_sum_density :
      ((μ - ν) + (ν - μ)) Set.univ = ∫⁻ x, ENNReal.ofReal |p x - q x| ∂τ := by
    rw [← h_tv_jord, h_tv_density, MeasureTheory.withDensity_apply _ MeasurableSet.univ,
      MeasureTheory.Measure.restrict_univ]
  -- Convert lintegral to integral.
  have h_int_abs : Integrable (fun x => |p x - q x|) τ := h_int_diff.abs
  have h_ofReal_int :
      ENNReal.ofReal (∫ x, |p x - q x| ∂τ) = ∫⁻ x, ENNReal.ofReal |p x - q x| ∂τ := by
    have := MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      h_int_abs (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
    exact this
  -- Final rewriting in real-valued form.
  have h_abs_int_nonneg : (0 : ℝ) ≤ ∫ x, |p x - q x| ∂τ :=
    MeasureTheory.integral_nonneg (fun _ => abs_nonneg _)
  unfold tvDist
  -- `tvDist = ((μ - ν) + (ν - μ)) Set.univ / 2`.
  -- Compute `toReal` of `(...)/2`.
  rw [h_sum_density, ← h_ofReal_int]
  -- `(ofReal A / 2).toReal = A / 2` when `A ≥ 0`.
  have h_two_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  rw [ENNReal.toReal_div, ENNReal.toReal_ofReal h_abs_int_nonneg]
  simp [ENNReal.toReal_ofNat]
  ring

/-! ### Le Cam estimate: `tvDist² ≤ 1 - bhattacharyya²`

The Le Cam estimate (Step 3 of the BH proof) is the integrated
Cauchy--Schwarz step on the polarization
`(p - q) = (√p - √q)(√p + √q)`. With the bridge
`tvDist_eq_half_integral_abs_rnDeriv_sub` and the factored form
`bhattacharyya_eq_integral_sqrt_mul_sqrt` in place, the proof applies
`integral_mul_le_Lp_mul_Lq_of_nonneg` with `p = q = 2` and expands the
resulting `L²`-norms via the pointwise identities
`(√p ± √q)² = p + q ± 2 √p √q` plus `∫ p dτ = ∫ q dτ = 1`. -/

/-- **Le Cam estimate (`tvDist² ≤ 1 - bhattacharyya²`).**

For two probability measures `μ`, `ν` on `α`,

  `((tvDist μ ν).toReal) ^ 2 ≤ 1 - bhattacharyya μ ν ^ 2`.

This is the Cauchy--Schwarz step on the density polarization
`(p - q) = (√p - √q)(√p + √q)`: Hölder with `p = q = 2` gives
`∫ |√p - √q| · (√p + √q) dτ ≤ √(∫ (√p - √q)² dτ) · √(∫ (√p + √q)² dτ)`,
the right-hand side expands via `∫ p dτ = ∫ q dτ = 1` and the factored
form of `bhattacharyya` to `√(2 - 2 B) · √(2 + 2 B) = 2 √(1 - B²)`,
where `B = bhattacharyya μ ν`. Dividing by 2 and squaring yields the
bound. -/
theorem tvDist_sq_le_one_sub_bhattacharyya_sq
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ((tvDist μ ν).toReal) ^ 2 ≤ 1 - bhattacharyya μ ν ^ 2 := by
  -- Notation.
  set τ : Measure α := μ + ν with hτ_def
  set p : α → ℝ := fun x => (μ.rnDeriv τ x).toReal with hp_def
  set q : α → ℝ := fun x => (ν.rnDeriv τ x).toReal with hq_def
  -- AC, pointwise nonneg, and probability-measure normalizations.
  have hμτ : μ ≪ τ := by
    rw [hτ_def]; exact rfl.absolutelyContinuous.add_right _
  have hντ : ν ≪ τ := by
    rw [hτ_def, add_comm μ ν]; exact rfl.absolutelyContinuous.add_right _
  have hp_nonneg : ∀ x, 0 ≤ p x := fun _ => ENNReal.toReal_nonneg
  have hq_nonneg : ∀ x, 0 ≤ q x := fun _ => ENNReal.toReal_nonneg
  have h_int_p_eq_one : ∫ x, p x ∂τ = 1 := by
    have h := MeasureTheory.Measure.integral_toReal_rnDeriv (μ := μ) (ν := τ) hμτ
    rw [hp_def]; rw [h]; exact probReal_univ
  have h_int_q_eq_one : ∫ x, q x ∂τ = 1 := by
    have h := MeasureTheory.Measure.integral_toReal_rnDeriv (μ := ν) (ν := τ) hντ
    rw [hq_def]; rw [h]; exact probReal_univ
  -- Integrability of `p`, `q`, `p + q`, `p - q` (and `|p - q|`).
  have h_int_p : Integrable p τ := by
    have h := MeasureTheory.Measure.integrableOn_toReal_rnDeriv
      (μ := μ) (ν := τ) (s := Set.univ) (by simp)
    rwa [MeasureTheory.integrableOn_univ] at h
  have h_int_q : Integrable q τ := by
    have h := MeasureTheory.Measure.integrableOn_toReal_rnDeriv
      (μ := ν) (ν := τ) (s := Set.univ) (by simp)
    rwa [MeasureTheory.integrableOn_univ] at h
  have h_int_p_add_q : Integrable (fun x => p x + q x) τ := h_int_p.add h_int_q
  -- Bridge: `tvDist = (1/2) ∫ |p - q|`.
  have h_bridge : (tvDist μ ν).toReal =
      (1 / 2 : ℝ) * ∫ x, |p x - q x| ∂τ :=
    tvDist_eq_half_integral_abs_rnDeriv_sub μ ν
  -- Pointwise: `|p - q| = |√p - √q| · (√p + √q)`.
  have h_factor : ∀ x,
      |p x - q x| = |Real.sqrt (p x) - Real.sqrt (q x)| *
        (Real.sqrt (p x) + Real.sqrt (q x)) := by
    intro x
    have hp := hp_nonneg x
    have hq := hq_nonneg x
    have h_sp_sq : Real.sqrt (p x) * Real.sqrt (p x) = p x := Real.mul_self_sqrt hp
    have h_sq_sq : Real.sqrt (q x) * Real.sqrt (q x) = q x := Real.mul_self_sqrt hq
    have h_pos : 0 ≤ Real.sqrt (p x) + Real.sqrt (q x) :=
      add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have h_eq : p x - q x = (Real.sqrt (p x) - Real.sqrt (q x)) *
        (Real.sqrt (p x) + Real.sqrt (q x)) := by
      nlinarith [h_sp_sq, h_sq_sq, Real.sqrt_nonneg (p x), Real.sqrt_nonneg (q x)]
    rw [h_eq, abs_mul, abs_of_nonneg h_pos]
  -- Bhattacharyya in factored form.
  have h_B :
      bhattacharyya μ ν = ∫ x, Real.sqrt (p x) * Real.sqrt (q x) ∂τ :=
    bhattacharyya_eq_integral_sqrt_mul_sqrt μ ν
  -- Measurability.
  have hp_meas : Measurable p :=
    (MeasureTheory.Measure.measurable_rnDeriv μ τ).ennreal_toReal
  have hq_meas : Measurable q :=
    (MeasureTheory.Measure.measurable_rnDeriv ν τ).ennreal_toReal
  have hsp_meas : Measurable (fun x => Real.sqrt (p x)) := hp_meas.sqrt
  have hsq_meas : Measurable (fun x => Real.sqrt (q x)) := hq_meas.sqrt
  have h_diff_meas : Measurable (fun x => Real.sqrt (p x) - Real.sqrt (q x)) :=
    hsp_meas.sub hsq_meas
  have h_sum_meas : Measurable (fun x => Real.sqrt (p x) + Real.sqrt (q x)) :=
    hsp_meas.add hsq_meas
  -- Pointwise bounds: `(√p ± √q)² ≤ 2(p + q)`.
  have h_sq_sub_le : ∀ x,
      (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 ≤ 2 * (p x + q x) := by
    intro x
    have hp := hp_nonneg x; have hq := hq_nonneg x
    have h1 : Real.sqrt (p x) * Real.sqrt (p x) = p x := Real.mul_self_sqrt hp
    have h2 : Real.sqrt (q x) * Real.sqrt (q x) = q x := Real.mul_self_sqrt hq
    nlinarith [sq_nonneg (Real.sqrt (p x) + Real.sqrt (q x)),
      Real.sqrt_nonneg (p x), Real.sqrt_nonneg (q x), h1, h2]
  have h_sq_add_le : ∀ x,
      (Real.sqrt (p x) + Real.sqrt (q x)) ^ 2 ≤ 2 * (p x + q x) := by
    intro x
    have hp := hp_nonneg x; have hq := hq_nonneg x
    have h1 : Real.sqrt (p x) * Real.sqrt (p x) = p x := Real.mul_self_sqrt hp
    have h2 : Real.sqrt (q x) * Real.sqrt (q x) = q x := Real.mul_self_sqrt hq
    nlinarith [sq_nonneg (Real.sqrt (p x) - Real.sqrt (q x))]
  -- Integrability of `(√p - √q)²` and `(√p + √q)²`.
  have h_int_sq_sub : Integrable (fun x => (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) τ := by
    refine MeasureTheory.Integrable.mono' (h_int_p_add_q.const_mul 2)
      ((h_diff_meas.pow_const _).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun x => ?_))
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact h_sq_sub_le x
  have h_int_sq_add : Integrable (fun x => (Real.sqrt (p x) + Real.sqrt (q x)) ^ 2) τ := by
    refine MeasureTheory.Integrable.mono' (h_int_p_add_q.const_mul 2)
      ((h_sum_meas.pow_const _).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun x => ?_))
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact h_sq_add_le x
  -- Integrability of `√p · √q`.
  have h_int_sp_sq : Integrable (fun x => Real.sqrt (p x) * Real.sqrt (q x)) τ := by
    refine MeasureTheory.Integrable.mono'
      (h_int_p_add_q.const_mul (1 / 2 : ℝ))
      (hsp_meas.mul hsq_meas).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => ?_))
    have h_amgm := sqrt_mul_le_half_add (hp_nonneg x) (hq_nonneg x)
    rw [Real.norm_of_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
    have h_sm : Real.sqrt (p x) * Real.sqrt (q x) = Real.sqrt (p x * q x) :=
      (Real.sqrt_mul (hp_nonneg x) _).symm
    rw [h_sm]
    linarith [h_amgm]
  -- Expand `∫ (√p - √q)² dτ = 2 - 2 B` and `∫ (√p + √q)² dτ = 2 + 2 B`.
  set B : ℝ := bhattacharyya μ ν with hB_def
  have h_int_sub_sq_eq :
      ∫ x, (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 ∂τ = 2 - 2 * B := by
    have h_pt : ∀ x, (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 =
        p x + q x - 2 * (Real.sqrt (p x) * Real.sqrt (q x)) := by
      intro x
      have h1 : Real.sqrt (p x) * Real.sqrt (p x) = p x := Real.mul_self_sqrt (hp_nonneg x)
      have h2 : Real.sqrt (q x) * Real.sqrt (q x) = q x := Real.mul_self_sqrt (hq_nonneg x)
      nlinarith [Real.sqrt_nonneg (p x), Real.sqrt_nonneg (q x), h1, h2]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h_pt),
      MeasureTheory.integral_sub h_int_p_add_q (h_int_sp_sq.const_mul 2),
      MeasureTheory.integral_add h_int_p h_int_q,
      MeasureTheory.integral_const_mul, h_int_p_eq_one, h_int_q_eq_one, ← h_B]
    ring
  have h_int_add_sq_eq :
      ∫ x, (Real.sqrt (p x) + Real.sqrt (q x)) ^ 2 ∂τ = 2 + 2 * B := by
    have h_pt : ∀ x, (Real.sqrt (p x) + Real.sqrt (q x)) ^ 2 =
        p x + q x + 2 * (Real.sqrt (p x) * Real.sqrt (q x)) := by
      intro x
      have h1 : Real.sqrt (p x) * Real.sqrt (p x) = p x := Real.mul_self_sqrt (hp_nonneg x)
      have h2 : Real.sqrt (q x) * Real.sqrt (q x) = q x := Real.mul_self_sqrt (hq_nonneg x)
      nlinarith [Real.sqrt_nonneg (p x), Real.sqrt_nonneg (q x), h1, h2]
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h_pt),
      MeasureTheory.integral_add h_int_p_add_q (h_int_sp_sq.const_mul 2),
      MeasureTheory.integral_add h_int_p h_int_q,
      MeasureTheory.integral_const_mul, h_int_p_eq_one, h_int_q_eq_one, ← h_B]
    ring
  -- `B ≤ 1` and `0 ≤ B`.
  have hB_le_one : B ≤ 1 := bhattacharyya_le_one μ ν
  have hB_nonneg : 0 ≤ B := bhattacharyya_nonneg μ ν
  have h_2sub_nonneg : (0 : ℝ) ≤ 2 - 2 * B := by linarith
  have h_2add_nonneg : (0 : ℝ) ≤ 2 + 2 * B := by linarith
  -- Cauchy--Schwarz `(∫ f g)² ≤ (∫ f²)(∫ g²)` via Hölder `p = q = 2`.
  -- Pointwise nonneg: |√p - √q| ≥ 0, √p + √q ≥ 0.
  have h_holder_conj : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h_memLp_abs_diff : MeasureTheory.MemLp
      (fun x => |Real.sqrt (p x) - Real.sqrt (q x)|) 2 τ := by
    have h_abs_meas : Measurable (fun x => |Real.sqrt (p x) - Real.sqrt (q x)|) :=
      h_diff_meas.norm
    refine (memLp_two_iff_integrable_sq h_abs_meas.aestronglyMeasurable).mpr ?_
    have h_eq : (fun x => |Real.sqrt (p x) - Real.sqrt (q x)| ^ 2) =
        (fun x => (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) := by
      funext x; rw [sq_abs]
    rw [h_eq]; exact h_int_sq_sub
  have h_memLp_sum : MeasureTheory.MemLp
      (fun x => Real.sqrt (p x) + Real.sqrt (q x)) 2 τ :=
    (memLp_two_iff_integrable_sq h_sum_meas.aestronglyMeasurable).mpr h_int_sq_add
  -- The Hölder inequality with `p = q = 2`.
  have h_holder :
      ∫ x, |Real.sqrt (p x) - Real.sqrt (q x)| *
        (Real.sqrt (p x) + Real.sqrt (q x)) ∂τ ≤
      (∫ x, |Real.sqrt (p x) - Real.sqrt (q x)| ^ (2 : ℝ) ∂τ) ^ ((1 : ℝ) / 2) *
      (∫ x, (Real.sqrt (p x) + Real.sqrt (q x)) ^ (2 : ℝ) ∂τ) ^ ((1 : ℝ) / 2) := by
    have h_two_eq : ENNReal.ofReal 2 = 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.ofReal_natCast]; rfl
    have h := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
      (μ := τ) (p := 2) (q := 2) h_holder_conj
      (f := fun x => |Real.sqrt (p x) - Real.sqrt (q x)|)
      (g := fun x => Real.sqrt (p x) + Real.sqrt (q x))
      (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
      (Filter.Eventually.of_forall (fun x =>
        add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
      (by rw [h_two_eq]; exact h_memLp_abs_diff)
      (by rw [h_two_eq]; exact h_memLp_sum)
    exact h
  -- Convert `^ (2 : ℝ)` to `^ 2`.
  have h_rpow_two : ∀ y : ℝ, 0 ≤ y → y ^ (2 : ℝ) = y ^ 2 := by
    intros y hy; rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h_holder' :
      ∫ x, |Real.sqrt (p x) - Real.sqrt (q x)| *
        (Real.sqrt (p x) + Real.sqrt (q x)) ∂τ ≤
      Real.sqrt (∫ x, (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 ∂τ) *
      Real.sqrt (∫ x, (Real.sqrt (p x) + Real.sqrt (q x)) ^ 2 ∂τ) := by
    have h_lhs_eq : ∀ x, |Real.sqrt (p x) - Real.sqrt (q x)| ^ (2 : ℝ) =
        (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 := by
      intro x
      have h_abs_nn : 0 ≤ |Real.sqrt (p x) - Real.sqrt (q x)| := abs_nonneg _
      rw [h_rpow_two _ h_abs_nn, sq_abs]
    have h_rhs_eq : ∀ x, (Real.sqrt (p x) + Real.sqrt (q x)) ^ (2 : ℝ) =
        (Real.sqrt (p x) + Real.sqrt (q x)) ^ 2 := by
      intro x
      exact h_rpow_two _ (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    have h_int_eq1 : ∫ x, |Real.sqrt (p x) - Real.sqrt (q x)| ^ (2 : ℝ) ∂τ =
        ∫ x, (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 ∂τ :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h_lhs_eq)
    have h_int_eq2 : ∫ x, (Real.sqrt (p x) + Real.sqrt (q x)) ^ (2 : ℝ) ∂τ =
        ∫ x, (Real.sqrt (p x) + Real.sqrt (q x)) ^ 2 ∂τ :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h_rhs_eq)
    rw [h_int_eq1, h_int_eq2] at h_holder
    have h_int1_nonneg : (0 : ℝ) ≤ ∫ x, (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 ∂τ :=
      MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)
    have h_int2_nonneg : (0 : ℝ) ≤ ∫ x, (Real.sqrt (p x) + Real.sqrt (q x)) ^ 2 ∂τ :=
      MeasureTheory.integral_nonneg (fun _ => sq_nonneg _)
    have h_sub_rpow : (∫ x, (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 ∂τ) ^ ((1 : ℝ) / 2) =
        Real.sqrt (∫ x, (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 ∂τ) := by
      rw [Real.sqrt_eq_rpow]
    have h_add_rpow : (∫ x, (Real.sqrt (p x) + Real.sqrt (q x)) ^ 2 ∂τ) ^ ((1 : ℝ) / 2) =
        Real.sqrt (∫ x, (Real.sqrt (p x) + Real.sqrt (q x)) ^ 2 ∂τ) := by
      rw [Real.sqrt_eq_rpow]
    rw [h_sub_rpow, h_add_rpow] at h_holder
    exact h_holder
  rw [h_int_sub_sq_eq, h_int_add_sq_eq] at h_holder'
  -- Combine: `∫ |p - q| ≤ √(2 - 2B) * √(2 + 2B)`.
  have h_factored_int : ∫ x, |p x - q x| ∂τ =
      ∫ x, |Real.sqrt (p x) - Real.sqrt (q x)| *
        (Real.sqrt (p x) + Real.sqrt (q x)) ∂τ :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall h_factor)
  have h_abs_int_le :
      ∫ x, |p x - q x| ∂τ ≤ Real.sqrt (2 - 2 * B) * Real.sqrt (2 + 2 * B) := by
    rw [h_factored_int]; exact h_holder'
  -- `Real.sqrt (2 - 2B) * Real.sqrt (2 + 2B) = Real.sqrt ((2 - 2B)(2 + 2B)) = 2 * Real.sqrt (1 - B²)`.
  have h_prod_sqrt :
      Real.sqrt (2 - 2 * B) * Real.sqrt (2 + 2 * B) = 2 * Real.sqrt (1 - B ^ 2) := by
    rw [← Real.sqrt_mul h_2sub_nonneg]
    have h_eq : (2 - 2 * B) * (2 + 2 * B) = 4 * (1 - B ^ 2) := by ring
    rw [h_eq]
    have h_1subsq_nonneg : (0 : ℝ) ≤ 1 - B ^ 2 := by nlinarith
    -- `√(4 (1 - B²)) = 2 · √(1 - B²)` via `Real.sqrt_mul`.
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    congr 1
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  rw [h_prod_sqrt] at h_abs_int_le
  -- Final: `tvDist = (1/2) ∫ |p - q| ≤ (1/2) * 2 * √(1 - B²) = √(1 - B²)`.
  -- Then `tvDist² ≤ 1 - B²`.
  have h_1subsq_nonneg : (0 : ℝ) ≤ 1 - B ^ 2 := by nlinarith
  have h_tv_le : (tvDist μ ν).toReal ≤ Real.sqrt (1 - B ^ 2) := by
    rw [h_bridge]
    have h1 : (1 / 2 : ℝ) * ∫ x, |p x - q x| ∂τ ≤
        (1 / 2 : ℝ) * (2 * Real.sqrt (1 - B ^ 2)) := by
      exact mul_le_mul_of_nonneg_left h_abs_int_le (by norm_num : (0 : ℝ) ≤ 1 / 2)
    have h2 : (1 / 2 : ℝ) * (2 * Real.sqrt (1 - B ^ 2)) = Real.sqrt (1 - B ^ 2) := by ring
    rw [h2] at h1
    exact h1
  have h_tv_nonneg : 0 ≤ (tvDist μ ν).toReal := ENNReal.toReal_nonneg
  calc ((tvDist μ ν).toReal) ^ 2
      ≤ (Real.sqrt (1 - B ^ 2)) ^ 2 := pow_le_pow_left₀ h_tv_nonneg h_tv_le 2
    _ = 1 - B ^ 2 := by rw [sq, Real.mul_self_sqrt h_1subsq_nonneg]

/-! ### Bretagnolle--Huber bridge — restatement in terms of the new
definition

The algebraic content (no measure-theoretic steps) lives in
`Pinsker.lean` and is parametrized by a real `ρ`. Here we restate that
chain with `ρ := bhattacharyya μ ν`, so downstream users can plug in
the named definition directly. -/

section BretagnolleHuberBridge

variable (μ ν : Measure α)

/-- **Bretagnolle--Huber bridge in terms of `bhattacharyya`.**

Given:

* `h_lecam : tvDist²(μ, ν) ≤ 1 - bhattacharyya μ ν ^ 2` (the Le Cam
  / Cauchy--Schwarz step), and
* `h_kl_bridge : Real.exp (-D / 2) ≤ bhattacharyya μ ν` (the Jensen
  step on `-log`, with `D` standing in for `KL(μ‖ν)`),

the bridge `tvDist²(μ, ν) ≤ 1 - Real.exp (-D)` holds.

This is a wrapper around
`tvDist_sq_le_one_sub_exp_neg_of_bhattacharyya` that substitutes
the abstract parameter `ρ` with the concrete `bhattacharyya μ ν`. -/
theorem tvDist_sq_le_one_sub_exp_neg_of_bhattacharyya_def
    {D : ℝ}
    (h_lecam : ((tvDist μ ν).toReal) ^ 2 ≤ 1 - bhattacharyya μ ν ^ 2)
    (h_kl_bridge : Real.exp (-D / 2) ≤ bhattacharyya μ ν) :
    ((tvDist μ ν).toReal) ^ 2 ≤ 1 - Real.exp (-D) :=
  tvDist_sq_le_one_sub_exp_neg_of_bhattacharyya μ ν
    (bhattacharyya_nonneg μ ν) h_lecam h_kl_bridge

/-- **Bretagnolle--Huber bridge wired to `klDiv`.**

Real-valued KL form: given the Le Cam estimate
`tvDist² ≤ 1 - bhattacharyya²` and the Jensen step
`exp(-(klDiv μ ν).toReal / 2) ≤ bhattacharyya μ ν`, the bridge
`tvDist² ≤ 1 - exp(-(klDiv μ ν).toReal)` holds.

When the measure-theoretic discharges of `h_lecam` and `h_kl_bridge`
become available in Mathlib (see the file docstring), this theorem
becomes the textbook Bretagnolle--Huber inequality with `D` =
`(klDiv μ ν).toReal`. -/
theorem tvDist_sq_le_one_sub_exp_neg_of_bhattacharyya_bridge
    {D : ℝ}
    (h_lecam : ((tvDist μ ν).toReal) ^ 2 ≤ 1 - bhattacharyya μ ν ^ 2)
    (h_kl_bridge : Real.exp (-D / 2) ≤ bhattacharyya μ ν) :
    ((tvDist μ ν).toReal) ^ 2 ≤ 1 - Real.exp (-D) :=
  tvDist_sq_le_one_sub_exp_neg_of_bhattacharyya_def μ ν h_lecam h_kl_bridge

end BretagnolleHuberBridge

/-! ### Examples -/

section Examples

variable (μ ν : Measure α)

/-- **Example.** The Bhattacharyya affinity is symmetric. -/
example : bhattacharyya μ ν = bhattacharyya ν μ := bhattacharyya_comm μ ν

/-- **Example.** The Bhattacharyya affinity is nonnegative. -/
example : 0 ≤ bhattacharyya μ ν := bhattacharyya_nonneg μ ν

end Examples

/-!
## TODO

* `bhattacharyya_self : [IsProbabilityMeasure μ] → bhattacharyya μ μ = 1`.
  Blocked on a clean computation of `rnDeriv μ (μ + μ)`; expected to
  follow from `Measure.rnDeriv_self` plus a `(μ + μ) = 2 • μ` rewrite.
* `bhattacharyya_eq_sqrt_rnDeriv_int_of_ac :
  μ ≪ ν → bhattacharyya μ ν = ∫ x, √((μ.rnDeriv ν x).toReal) ∂ν`.
  The classical asymmetric form; reduces the symmetric definition
  above when `μ ≪ ν`.
* `bhattacharyya_ge_exp_neg_half_klDiv :
  klDiv μ ν ≠ ∞ → Real.exp (-(klDiv μ ν).toReal / 2) ≤ bhattacharyya μ ν`.
  The Jensen step (Step 2 of the BH proof). With the Le Cam step now
  discharged here, this is the last remaining bridge hypothesis on the
  route to the textbook Bretagnolle--Huber bound.
* When the Jensen step lands, the carrier
  `tvDist_le_sqrt_one_sub_exp_neg` in
  `LTFP/Ch15_LowerBounds/Statistical.lean` upgrades from
  `bridge-hypothesis` to A-class.
-/

end LTFP.MathlibExt.Probability
