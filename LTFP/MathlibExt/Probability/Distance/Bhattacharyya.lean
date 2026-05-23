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
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Measure.LogLikelihoodRatio
import Mathlib.InformationTheory.KullbackLeibler.Basic

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

**Both steps of the classical Bretagnolle--Huber proof are now
discharged unconditionally for probability measures:**

* the **Le Cam estimate** `tvDist² ≤ 1 - bhattacharyya²`, and
* the **Jensen step** `exp(-(klDiv μ ν).toReal / 2) ≤ bhattacharyya μ ν`
  (under `μ ≪ ν` and `klDiv μ ν ≠ ∞`).

What is now available:

* `totalVariation_withDensityᵥ_eq_withDensity_abs` — the Jordan-to-density
  bridge: `(τ.withDensityᵥ f).totalVariation = τ.withDensity (ofReal |f|)`
  for an integrable real function.
* `tvDist_eq_half_integral_abs_rnDeriv_sub` — the density representation
  `(tvDist μ ν).toReal = (1/2) · ∫ |p - q| dτ` where `τ = μ + ν` and
  `p, q` are the `toReal`-densities.
* `bhattacharyya_eq_integral_sqrt_mul_sqrt` — the factored form
  `bhattacharyya μ ν = ∫ √p · √q dτ` used in the Cauchy--Schwarz step.
* `tvDist_sq_le_one_sub_bhattacharyya_sq` — the **Le Cam estimate**: for
  two probability measures, `tvDist² ≤ 1 - bhattacharyya²`. The proof
  composes the density bridge with Hölder (`p = q = 2`) on the
  polarization `p - q = (√p - √q)(√p + √q)` and expands the `L²`-norms
  via `∫ p dτ = ∫ q dτ = 1` and the factored Bhattacharyya identity.
* `hellingerSquared` — the squared Hellinger distance, defined via
  `Hsq(μ, ν) := 2 (1 - bhattacharyya μ ν)`.
* `tvDist_sq_le_hellingerSquared_mul` — Le Cam in Hellinger form:
  `tvDist² ≤ Hsq · (1 - Hsq / 4)`.
* `hellingerSquared_le_two_one_sub_exp_neg_half_klDiv` — Bhattacharyya
  --KL bridge in Hellinger form: under `μ ≪ ν` and `klDiv μ ν ≠ ∞`,
  `Hsq ≤ 2 (1 - exp(-(klDiv μ ν).toReal / 2))`.
* `bhattacharyya_eq_integral_sqrt_rnDeriv_of_ac` — the asymmetric-form
  bridge: under `μ ≪ ν`,
  `bhattacharyya μ ν = ∫ √((μ.rnDeriv ν).toReal) ∂ν`. Factors through
  the Radon--Nikodym chain rule `μ.rnDeriv τ =ᵐ[τ]
  (μ.rnDeriv ν) · (ν.rnDeriv τ)` and the change-of-measure identity.
* `bhattacharyya_ge_exp_neg_half_klDiv` — the **Jensen step**: under
  `μ ≪ ν` and `klDiv μ ν ≠ ∞`,
  `Real.exp (-(klDiv μ ν).toReal / 2) ≤ bhattacharyya μ ν`. The proof
  composes the asymmetric-form bridge with the change-of-measure
  identity `∫ √(dμ/dν) dν = ∫ exp(-(1/2) llr μ ν) dμ` and Jensen's
  inequality applied to the convex exponential function over the
  probability measure `μ`.

The composition `tvDist² ≤ 1 - bhattacharyya² ≤ 1 - exp(-KL)` is now an
A-class theorem; see
`LTFP.Ch15_LowerBounds.tvDist_le_sqrt_one_sub_exp_neg_klDiv`.

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

/-! ### Asymmetric form of the Bhattacharyya affinity

When `μ ≪ ν`, the symmetric Bhattacharyya integral
`∫ √((dμ/dτ)(dν/dτ)) dτ` over `τ = μ + ν` coincides with the
classical asymmetric form `∫ √(dμ/dν) dν`. The bridge factors through
the Radon--Nikodym chain rule
`μ.rnDeriv (μ+ν) =ᵐ[μ+ν] (μ.rnDeriv ν) · (ν.rnDeriv (μ+ν))`
and the change-of-measure identity for `ν.rnDeriv (μ+ν)`. -/

/-- **Integrability of `√(dμ/dν)` under `ν`.**

For two finite measures `μ`, `ν`, the function `x ↦ √((μ.rnDeriv ν x).toReal)`
is integrable with respect to `ν`. The proof uses the elementary bound
`√t ≤ 1 + t` for `t ≥ 0` to dominate the integrand by an integrable
function (namely `1 + (μ.rnDeriv ν).toReal`, integrable since `ν` is
finite and `(μ.rnDeriv ν).toReal` is integrable under `ν` for finite
`μ`). -/
theorem integrable_sqrt_rnDeriv
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    Integrable (fun x => Real.sqrt ((μ.rnDeriv ν x).toReal)) ν := by
  -- Measurability.
  have h_meas : Measurable (fun x => Real.sqrt ((μ.rnDeriv ν x).toReal)) :=
    ((MeasureTheory.Measure.measurable_rnDeriv μ ν).ennreal_toReal).sqrt
  -- Bound: `√t ≤ 1 + t` for `t ≥ 0` (because if `t ≤ 1` then `√t ≤ 1`,
  -- and if `t > 1` then `√t < t ≤ 1 + t`).
  have h_bound : ∀ x, Real.sqrt ((μ.rnDeriv ν x).toReal) ≤
      1 + (μ.rnDeriv ν x).toReal := by
    intro x
    set t : ℝ := (μ.rnDeriv ν x).toReal with ht_def
    have ht_nonneg : 0 ≤ t := ENNReal.toReal_nonneg
    by_cases ht1 : t ≤ 1
    · have : Real.sqrt t ≤ 1 := by
        rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
        exact Real.sqrt_le_sqrt ht1
      linarith
    · push_neg at ht1
      have h_sqrt_le : Real.sqrt t ≤ t := by
        have h_sq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht_nonneg
        have h_sqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr (by linarith)
        nlinarith [h_sq, Real.sqrt_nonneg t]
      linarith
  -- Integrability of the dominating function `1 + (μ.rnDeriv ν).toReal`.
  have h_int_dom : Integrable
      (fun x => 1 + (μ.rnDeriv ν x).toReal) ν :=
    (integrable_const 1).add Measure.integrable_toReal_rnDeriv
  -- Dominated convergence: `|√(rnDeriv)| ≤ 1 + rnDeriv`.
  refine MeasureTheory.Integrable.mono' h_int_dom h_meas.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact h_bound x

/-- **Asymmetric form of the Bhattacharyya affinity.**

For two finite measures `μ`, `ν` with `μ ≪ ν`, the symmetric Bhattacharyya
integral `∫ √((dμ/dτ)(dν/dτ)) dτ` over `τ = μ + ν` reduces to the
classical asymmetric form:

  `bhattacharyya μ ν = ∫ x, √((μ.rnDeriv ν x).toReal) ∂ν`.

This is the bridge between the symmetric definition (which exists for
arbitrary pairs of measures) and the asymmetric Hellinger affinity
(which only makes sense under absolute continuity). It is the key
identity used to apply Jensen's inequality on `exp` for the
`bhattacharyya ≥ exp(-KL/2)` step. -/
theorem bhattacharyya_eq_integral_sqrt_rnDeriv_of_ac
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) :
    bhattacharyya μ ν = ∫ x, Real.sqrt ((μ.rnDeriv ν x).toReal) ∂ν := by
  -- Notation: `τ = μ + ν`, `r = μ.rnDeriv τ`, `s = ν.rnDeriv τ`.
  set τ : Measure α := μ + ν with hτ_def
  -- Absolute continuity chain.
  have hμτ : μ ≪ τ := by
    rw [hτ_def]; exact rfl.absolutelyContinuous.add_right _
  have hντ : ν ≪ τ := by
    rw [hτ_def, add_comm μ ν]; exact rfl.absolutelyContinuous.add_right _
  have hτν : τ ≪ ν := by
    rw [hτ_def]; exact MeasureTheory.Measure.AbsolutelyContinuous.add_left hμν
      MeasureTheory.Measure.AbsolutelyContinuous.rfl
  have hτ_sf : SigmaFinite τ := by rw [hτ_def]; infer_instance
  -- Chain rule: `μ.rnDeriv ν · ν.rnDeriv τ =ᵐ[τ] μ.rnDeriv τ`.
  have h_chain :
      μ.rnDeriv ν * ν.rnDeriv τ =ᵐ[τ] μ.rnDeriv τ :=
    MeasureTheory.Measure.rnDeriv_mul_rnDeriv (κ := τ) hμν
  -- Pointwise rewrite of the integrand on a.e. τ.
  -- Use `hτν : τ ≪ ν` to lift `∀ᵐ x ∂ν, μ.rnDeriv ν x ≠ ∞` to `∀ᵐ x ∂τ`.
  have hμν_top_τ : ∀ᵐ x ∂τ, μ.rnDeriv ν x ≠ ∞ :=
    hτν.ae_le (MeasureTheory.Measure.rnDeriv_ne_top μ ν)
  have hντ_top : ∀ᵐ x ∂τ, ν.rnDeriv τ x ≠ ∞ :=
    MeasureTheory.Measure.rnDeriv_ne_top ν τ
  have h_pt : ∀ᵐ x ∂τ,
      Real.sqrt ((μ.rnDeriv τ x).toReal * (ν.rnDeriv τ x).toReal) =
        Real.sqrt ((μ.rnDeriv ν x).toReal) * (ν.rnDeriv τ x).toReal := by
    filter_upwards [h_chain, hμν_top_τ, hντ_top] with x hx hμν_top hντ_top
    -- From the chain rule, `(μ.rnDeriv τ x).toReal = (μ.rnDeriv ν x).toReal · (ν.rnDeriv τ x).toReal`.
    have h_chain_real :
        (μ.rnDeriv τ x).toReal =
          (μ.rnDeriv ν x).toReal * (ν.rnDeriv τ x).toReal := by
      have := hx
      -- `hx : (μ.rnDeriv ν * ν.rnDeriv τ) x = μ.rnDeriv τ x` in `ℝ≥0∞`.
      have h_eq : μ.rnDeriv ν x * ν.rnDeriv τ x = μ.rnDeriv τ x := this
      have h_toReal := congrArg ENNReal.toReal h_eq
      rw [ENNReal.toReal_mul] at h_toReal
      exact h_toReal.symm
    rw [h_chain_real]
    -- Now: `√(a · s² ) = √a · |s| = √a · s` since `s ≥ 0`. Here, decompose:
    -- `(μ.rnDeriv ν x).toReal · (ν.rnDeriv τ x).toReal · (ν.rnDeriv τ x).toReal
    --     = (μ.rnDeriv ν x).toReal · ((ν.rnDeriv τ x).toReal)²`.
    set a : ℝ := (μ.rnDeriv ν x).toReal
    set s : ℝ := (ν.rnDeriv τ x).toReal
    have ha : 0 ≤ a := ENNReal.toReal_nonneg
    have hs : 0 ≤ s := ENNReal.toReal_nonneg
    -- We want: `√(a · s · s) = √a · s`. Use `√(a · s²) = √a · √(s²) = √a · |s| = √a · s`.
    have h_rewrite : a * s * s = a * s ^ 2 := by ring
    rw [h_rewrite, Real.sqrt_mul ha, Real.sqrt_sq hs]
  -- Translate the integrand equality into an `integral` equality.
  have h_int_eq :
      ∫ x, Real.sqrt ((μ.rnDeriv τ x).toReal * (ν.rnDeriv τ x).toReal) ∂τ =
        ∫ x, Real.sqrt ((μ.rnDeriv ν x).toReal) * (ν.rnDeriv τ x).toReal ∂τ :=
    MeasureTheory.integral_congr_ae h_pt
  -- Use change of measure: `∫ (ν.rnDeriv τ).toReal · f ∂τ = ∫ f ∂ν` (under `ν ≪ τ`).
  have h_cofmeas :
      ∫ x, Real.sqrt ((μ.rnDeriv ν x).toReal) * (ν.rnDeriv τ x).toReal ∂τ =
        ∫ x, Real.sqrt ((μ.rnDeriv ν x).toReal) ∂ν := by
    have h := MeasureTheory.integral_rnDeriv_smul (μ := ν) (ν := τ)
      (f := fun x => Real.sqrt ((μ.rnDeriv ν x).toReal)) hντ
    -- `h : ∫ x, (ν.rnDeriv τ x).toReal • √((μ.rnDeriv ν x).toReal) ∂τ
    --   = ∫ x, √((μ.rnDeriv ν x).toReal) ∂ν`.
    simp only [smul_eq_mul] at h
    -- swap multiplication order.
    have h_swap :
        ∫ x, Real.sqrt ((μ.rnDeriv ν x).toReal) * (ν.rnDeriv τ x).toReal ∂τ =
          ∫ x, (ν.rnDeriv τ x).toReal * Real.sqrt ((μ.rnDeriv ν x).toReal) ∂τ := by
      refine MeasureTheory.integral_congr_ae ?_
      refine Filter.Eventually.of_forall (fun x => ?_); ring
    rw [h_swap]; exact h
  -- Conclude.
  unfold bhattacharyya
  rw [show (μ + ν : Measure α) = τ from rfl, h_int_eq, h_cofmeas]

/-! ### Jensen step: `exp(-(klDiv μ ν).toReal / 2) ≤ bhattacharyya μ ν`

With the asymmetric form `bhattacharyya μ ν = ∫ √((μ.rnDeriv ν).toReal) ∂ν`
in place (under `μ ≪ ν`), Jensen's inequality applied to the convex
function `Real.exp` against the probability measure `μ` produces the
lower bound

  `Real.exp (-(klDiv μ ν).toReal / 2) ≤ bhattacharyya μ ν`,

provided `μ ≪ ν`, both measures are probability measures, and the
Kullback--Leibler divergence is finite (`klDiv μ ν ≠ ∞`, equivalently
`Integrable (llr μ ν) μ`).

The proof factors through two identities:

* `(klDiv μ ν).toReal = ∫ llr μ ν dμ` (Mathlib's
  `toReal_klDiv_of_measure_eq` for probability measures).
* `∫ exp(-(1/2) llr μ ν x) dμ = ∫ √((μ.rnDeriv ν x).toReal) dν`
  (change of measure via `integral_rnDeriv_smul`, combined with
  `exp_llr_of_ac : exp(llr μ ν) =ᵐ[μ] (μ.rnDeriv ν).toReal`).

Jensen on the convex function `Real.exp` then gives
`exp(∫ -(1/2) llr dμ) ≤ ∫ exp(-(1/2) llr) dμ`, which translates to the
desired inequality. -/

/-- **Integral identity: `∫ exp(-(1/2) llr) dμ = ∫ √(dμ/dν) dν`.**

For probability measures `μ ≪ ν`, the expectation of `exp(-(1/2) llr μ ν)`
under `μ` equals the integral of `√((μ.rnDeriv ν).toReal)` against `ν`.
This is the change-of-measure identity used in the Jensen step. -/
theorem integral_exp_neg_half_llr_eq_integral_sqrt_rnDeriv
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) :
    ∫ x, Real.exp (-(1/2) * MeasureTheory.llr μ ν x) ∂μ =
      ∫ x, Real.sqrt ((μ.rnDeriv ν x).toReal) ∂ν := by
  -- Change of measure: `∫ f dμ = ∫ (μ.rnDeriv ν).toReal • f dν` (under `μ ≪ ν`).
  -- Apply with `f x = exp(-(1/2) llr μ ν x)`.
  have h_cofmeas := MeasureTheory.integral_rnDeriv_smul (μ := μ) (ν := ν)
    (f := fun x => Real.exp (-(1/2) * MeasureTheory.llr μ ν x)) hμν
  -- `h_cofmeas : ∫ x, (μ.rnDeriv ν x).toReal • exp(-(1/2) llr μ ν x) ∂ν
  --   = ∫ x, exp(-(1/2) llr μ ν x) ∂μ`.
  simp only [smul_eq_mul] at h_cofmeas
  rw [← h_cofmeas]
  -- Pointwise: a.e. ν, `(μ.rnDeriv ν x).toReal · exp(-(1/2) llr μ ν x)
  --   = √((μ.rnDeriv ν x).toReal)`.
  -- Reason: by `exp_llr`, `exp(llr μ ν x) =ᵐ[ν] if rnDeriv = 0 then 1
  --   else (rnDeriv).toReal`. So at rnDeriv = 0, exp(-(1/2) llr) = 1 and
  --   the product is 0 · 1 = 0 = √0. At rnDeriv > 0, `exp(-(1/2) llr) =
  --   1/√(rnDeriv).toReal`, so the product is `√(rnDeriv).toReal`.
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [MeasureTheory.exp_llr μ ν,
    MeasureTheory.Measure.rnDeriv_lt_top μ ν] with x hx_exp hx_top
  -- Notation aliases (not via `set`, to keep the goal in unfolded form).
  by_cases h_zero : μ.rnDeriv ν x = 0
  · -- LHS = 0 · _ = 0; RHS = √0 = 0.
    have h_toReal_zero : (μ.rnDeriv ν x).toReal = 0 := by rw [h_zero]; simp
    show (μ.rnDeriv ν x).toReal * Real.exp (-(1/2) * MeasureTheory.llr μ ν x) =
      Real.sqrt ((μ.rnDeriv ν x).toReal)
    rw [h_toReal_zero, zero_mul, Real.sqrt_zero]
  · -- rnDeriv > 0; rewrite via exp_llr.
    set pr : ℝ := (μ.rnDeriv ν x).toReal with hpr_def
    have hpr_nonneg : 0 ≤ pr := ENNReal.toReal_nonneg
    have h_exp_eq_pr : Real.exp (MeasureTheory.llr μ ν x) = pr := by
      have hxe : Real.exp (MeasureTheory.llr μ ν x) =
          (if μ.rnDeriv ν x = 0 then (1 : ℝ) else (μ.rnDeriv ν x).toReal) := hx_exp
      rw [hxe, if_neg h_zero]
    have hpr_pos : 0 < pr := by
      rw [hpr_def]
      exact ENNReal.toReal_pos h_zero hx_top.ne
    -- `exp((1/2) llr)` squared equals `exp(llr) = pr`, so it equals `√pr`.
    have h_half_pos : 0 < Real.exp ((1/2) * MeasureTheory.llr μ ν x) := Real.exp_pos _
    have h_sq_eq : Real.exp ((1/2) * MeasureTheory.llr μ ν x) *
        Real.exp ((1/2) * MeasureTheory.llr μ ν x) = pr := by
      rw [← Real.exp_add, show (1/2) * MeasureTheory.llr μ ν x +
        (1/2) * MeasureTheory.llr μ ν x = MeasureTheory.llr μ ν x from by ring,
        h_exp_eq_pr]
    have h_eq_sqrt : Real.exp ((1/2) * MeasureTheory.llr μ ν x) = Real.sqrt pr := by
      have : Real.sqrt (Real.exp ((1/2) * MeasureTheory.llr μ ν x) *
          Real.exp ((1/2) * MeasureTheory.llr μ ν x)) =
          Real.exp ((1/2) * MeasureTheory.llr μ ν x) :=
        Real.sqrt_mul_self h_half_pos.le
      rw [h_sq_eq] at this
      exact this.symm
    -- `exp(-(1/2) llr) = (exp((1/2) llr))⁻¹ = (√pr)⁻¹`.
    have h_exp_neg_half :
        Real.exp (-(1/2) * MeasureTheory.llr μ ν x) = (Real.sqrt pr)⁻¹ := by
      rw [show -(1/2) * MeasureTheory.llr μ ν x = -((1/2) * MeasureTheory.llr μ ν x) from
        by ring, Real.exp_neg, h_eq_sqrt]
    -- Conclude: `pr · (√pr)⁻¹ = (√pr · √pr) · (√pr)⁻¹ = √pr`.
    show pr * Real.exp (-(1/2) * MeasureTheory.llr μ ν x) = Real.sqrt pr
    rw [h_exp_neg_half]
    have h_sqrt_pos : 0 < Real.sqrt pr := Real.sqrt_pos.mpr hpr_pos
    have h_sqrt_sq : Real.sqrt pr * Real.sqrt pr = pr := Real.mul_self_sqrt hpr_nonneg
    field_simp
    linarith [h_sqrt_sq]

/-- **Integrability of `exp(-(1/2) llr μ ν)` under `μ`.**

For two finite measures `μ`, `ν`, the function `x ↦ exp(-(1/2) llr μ ν x)`
is integrable with respect to `μ`. The proof uses the elementary bound
`exp(-y/2) ≤ 1 + exp(-y)` for all `y ∈ ℝ`, combined with the fact that
`exp(-llr μ ν) =ᵐ[μ] (ν.rnDeriv μ).toReal` (under `μ ≪ ν`) which is
integrable under `μ` when `ν` is a finite measure. -/
theorem integrable_exp_neg_half_llr
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) :
    Integrable (fun x => Real.exp (-(1/2) * MeasureTheory.llr μ ν x)) μ := by
  have h_meas : Measurable (fun x => Real.exp (-(1/2) * MeasureTheory.llr μ ν x)) := by
    refine Real.measurable_exp.comp ?_
    exact (measurable_const.mul (MeasureTheory.measurable_llr μ ν))
  -- Bound: `exp(-y/2) ≤ 1 + exp(-y)` for all `y`.
  -- Proof: if `y ≥ 0`, then `-y/2 ≤ 0`, so `exp(-y/2) ≤ 1 ≤ 1 + exp(-y)`.
  -- If `y < 0`, then `-y > 0` and `-y/2 ≤ -y`, so `exp(-y/2) ≤ exp(-y) ≤ 1 + exp(-y)`.
  have h_bound : ∀ y : ℝ, Real.exp (-(1/2) * y) ≤ 1 + Real.exp (-y) := by
    intro y
    by_cases hy : 0 ≤ y
    · have h_le : -(1/2) * y ≤ 0 := by nlinarith
      have h_exp_le_one : Real.exp (-(1/2) * y) ≤ 1 := Real.exp_le_one_iff.mpr h_le
      have h_exp_neg_nonneg : 0 ≤ Real.exp (-y) := (Real.exp_pos _).le
      linarith
    · push_neg at hy
      have h_le : -(1/2) * y ≤ -y := by nlinarith
      have h_exp_le : Real.exp (-(1/2) * y) ≤ Real.exp (-y) := Real.exp_le_exp.mpr h_le
      have h_one_pos : (0 : ℝ) ≤ 1 := zero_le_one
      linarith
  -- Apply: `exp(-(1/2) llr μ ν x) ≤ 1 + exp(-llr μ ν x)`.
  -- Under μ ≪ ν, `exp(-llr μ ν) =ᵐ[μ] (ν.rnDeriv μ).toReal`, integrable.
  have h_int_neg_llr : Integrable (fun x => Real.exp (-MeasureTheory.llr μ ν x)) μ := by
    have h_eq : (fun x => Real.exp (-MeasureTheory.llr μ ν x)) =ᵐ[μ]
        fun x => (ν.rnDeriv μ x).toReal :=
      MeasureTheory.exp_neg_llr hμν
    refine (MeasureTheory.integrable_congr h_eq).mpr ?_
    exact MeasureTheory.Measure.integrable_toReal_rnDeriv
  have h_int_bound : Integrable (fun x => (1 : ℝ) + Real.exp (-MeasureTheory.llr μ ν x)) μ :=
    (integrable_const _).add h_int_neg_llr
  refine MeasureTheory.Integrable.mono' h_int_bound h_meas.aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall (fun x => ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  exact h_bound _

/-- **Jensen step: `exp(-(klDiv μ ν).toReal / 2) ≤ bhattacharyya μ ν`.**

For two probability measures `μ ≪ ν` on `α` with finite KL divergence
(`klDiv μ ν ≠ ∞`), the Bhattacharyya affinity dominates the
exponentiated half-KL bound:

  `Real.exp (-(klDiv μ ν).toReal / 2) ≤ bhattacharyya μ ν`.

The proof composes the asymmetric-form bridge
`bhattacharyya = ∫ √((μ.rnDeriv ν).toReal) ∂ν`, the change-of-measure
identity `∫ √(dμ/dν) dν = ∫ exp(-(1/2) llr) dμ`, and Jensen's inequality
applied to the convex exponential function over the probability measure
`μ`. -/
theorem bhattacharyya_ge_exp_neg_half_klDiv
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (hkl : InformationTheory.klDiv μ ν ≠ ∞) :
    Real.exp (-(InformationTheory.klDiv μ ν).toReal / 2) ≤ bhattacharyya μ ν := by
  -- Equivalent characterization of `klDiv ≠ ∞` for `μ ≪ ν`.
  have h_int_llr : Integrable (MeasureTheory.llr μ ν) μ := by
    rcases (InformationTheory.klDiv_ne_top_iff (μ := μ) (ν := ν)).mp hkl with ⟨_, h⟩
    exact h
  -- `(klDiv μ ν).toReal = ∫ llr μ ν dμ` for probability measures.
  have h_kl_real : (InformationTheory.klDiv μ ν).toReal =
      ∫ x, MeasureTheory.llr μ ν x ∂μ := by
    refine InformationTheory.toReal_klDiv_of_measure_eq hμν ?_
    rw [show μ Set.univ = (1 : ℝ≥0∞) from measure_univ,
        show ν Set.univ = (1 : ℝ≥0∞) from measure_univ]
  -- Step A — Jensen on `exp` (convex on `ℝ`) over the probability measure `μ`.
  -- Let `g x = -(1/2) * llr μ ν x`. Then:
  --   exp(∫ g dμ) ≤ ∫ exp(g) dμ.
  have h_int_g : Integrable (fun x => -(1/2 : ℝ) * MeasureTheory.llr μ ν x) μ :=
    h_int_llr.const_mul _
  have h_int_exp_g : Integrable
      (fun x => Real.exp (-(1/2 : ℝ) * MeasureTheory.llr μ ν x)) μ :=
    integrable_exp_neg_half_llr μ ν hμν
  have h_jensen :
      Real.exp (∫ x, -(1/2 : ℝ) * MeasureTheory.llr μ ν x ∂μ) ≤
        ∫ x, Real.exp (-(1/2 : ℝ) * MeasureTheory.llr μ ν x) ∂μ := by
    have h := ConvexOn.map_integral_le (μ := μ) (E := ℝ)
      (s := Set.univ) (g := Real.exp)
      (f := fun x => -(1/2 : ℝ) * MeasureTheory.llr μ ν x)
      convexOn_exp Real.continuous_exp.continuousOn isClosed_univ
      (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
      h_int_g h_int_exp_g
    exact h
  -- Step B — Evaluate the LHS of Jensen.
  have h_lhs_int :
      ∫ x, -(1/2 : ℝ) * MeasureTheory.llr μ ν x ∂μ =
        -(1/2) * (InformationTheory.klDiv μ ν).toReal := by
    rw [MeasureTheory.integral_const_mul, ← h_kl_real]
  have h_lhs_eq :
      Real.exp (∫ x, -(1/2 : ℝ) * MeasureTheory.llr μ ν x ∂μ) =
        Real.exp (-(InformationTheory.klDiv μ ν).toReal / 2) := by
    rw [h_lhs_int]; congr 1; ring
  -- Step C — Evaluate the RHS via the change-of-measure + asymmetric-form bridge.
  have h_rhs_eq :
      ∫ x, Real.exp (-(1/2 : ℝ) * MeasureTheory.llr μ ν x) ∂μ =
        bhattacharyya μ ν := by
    rw [integral_exp_neg_half_llr_eq_integral_sqrt_rnDeriv μ ν hμν,
      ← bhattacharyya_eq_integral_sqrt_rnDeriv_of_ac μ ν hμν]
  -- Combine.
  rw [← h_lhs_eq, ← h_rhs_eq]
  exact h_jensen

/-! ### Squared Hellinger distance and the Hellinger-form bridge

The **squared Hellinger distance** `Hsq(μ, ν) := 2 (1 - ρ(μ, ν))` is
the geometric-mean complement of the Bhattacharyya affinity. It is the
natural quantity for stating the Le Cam estimate in Hellinger form,

  `tvDist²(μ, ν) ≤ Hsq · (1 - Hsq / 4)`,

and the Bhattacharyya--KL bridge `Hsq ≤ 2 (1 - exp(-KL/2))`. Together
with the algebraic chain `Hsq (1 - Hsq/4) = 1 - ρ²` (an identity in
`ρ = 1 - Hsq/2`) these two pieces compose into the same A-class
Bretagnolle--Huber inequality discharged through the Bhattacharyya
route, just restated via the Hellinger affinity. -/

/-- The **squared Hellinger distance** between two measures `μ` and `ν`,
defined via the Bhattacharyya affinity by
`Hsq(μ, ν) := 2 (1 - ρ(μ, ν))`. For probability measures this lies in
`[0, 2]`. The classical pointwise expression
`Hsq(μ, ν) = ∫ (√(dμ/dτ) - √(dν/dτ))² dτ` follows from the polarization
`(√p - √q)² = p + q - 2 √(pq)` together with `∫ p dτ = ∫ q dτ = 1`. -/
noncomputable def hellingerSquared (μ ν : Measure α) : ℝ :=
  2 * (1 - bhattacharyya μ ν)

/-- The defining identity `Hsq(μ, ν) = 2 - 2 · ρ(μ, ν)`. -/
theorem hellingerSquared_eq_two_sub_two_bhattacharyya (μ ν : Measure α) :
    hellingerSquared μ ν = 2 - 2 * bhattacharyya μ ν := by
  unfold hellingerSquared; ring

/-- The squared Hellinger distance is nonnegative for two probability
measures, since `bhattacharyya μ ν ≤ 1`. -/
theorem hellingerSquared_nonneg
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    0 ≤ hellingerSquared μ ν := by
  unfold hellingerSquared
  have h := bhattacharyya_le_one μ ν
  linarith

/-- The squared Hellinger distance is bounded above by `2`, since
`0 ≤ bhattacharyya μ ν`. -/
theorem hellingerSquared_le_two (μ ν : Measure α) :
    hellingerSquared μ ν ≤ 2 := by
  unfold hellingerSquared
  have h := bhattacharyya_nonneg μ ν
  linarith

/-- **Le Cam estimate in Hellinger form.**

For two probability measures `μ`, `ν`, the squared total-variation
distance is bounded above by `Hsq · (1 - Hsq / 4)`:

  `((tvDist μ ν).toReal) ^ 2 ≤ hellingerSquared μ ν *
      (1 - hellingerSquared μ ν / 4)`.

This is the same fact as the Bhattacharyya-form Le Cam estimate
`tvDist² ≤ 1 - ρ²`, restated through the identity
`Hsq (1 - Hsq/4) = 1 - ρ²` (which is a polynomial identity in
`ρ = 1 - Hsq/2`). -/
theorem tvDist_sq_le_hellingerSquared_mul
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ((tvDist μ ν).toReal) ^ 2 ≤
      hellingerSquared μ ν * (1 - hellingerSquared μ ν / 4) := by
  -- The Bhattacharyya-form Le Cam estimate.
  have h_bh : ((tvDist μ ν).toReal) ^ 2 ≤ 1 - bhattacharyya μ ν ^ 2 :=
    tvDist_sq_le_one_sub_bhattacharyya_sq μ ν
  -- Polynomial identity: `Hsq (1 - Hsq/4) = 1 - ρ²` when `Hsq = 2(1 - ρ)`.
  have h_eq :
      hellingerSquared μ ν * (1 - hellingerSquared μ ν / 4)
        = 1 - bhattacharyya μ ν ^ 2 := by
    unfold hellingerSquared; ring
  rw [h_eq]
  exact h_bh

/-- **Bhattacharyya--KL bridge in Hellinger form.**

Under `μ ≪ ν` with finite KL divergence (`klDiv μ ν ≠ ∞`), the squared
Hellinger distance is bounded above by `2 (1 - exp(-KL/2))`:

  `hellingerSquared μ ν ≤ 2 * (1 - Real.exp (-(klDiv μ ν).toReal / 2))`.

This is the Hellinger-form restatement of the Jensen step
`exp(-KL/2) ≤ bhattacharyya`. -/
theorem hellingerSquared_le_two_one_sub_exp_neg_half_klDiv
    (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : μ ≪ ν) (hkl : InformationTheory.klDiv μ ν ≠ ∞) :
    hellingerSquared μ ν ≤
      2 * (1 - Real.exp (-(InformationTheory.klDiv μ ν).toReal / 2)) := by
  -- The Jensen step in Bhattacharyya form.
  have h_jensen :
      Real.exp (-(InformationTheory.klDiv μ ν).toReal / 2) ≤
        bhattacharyya μ ν :=
    bhattacharyya_ge_exp_neg_half_klDiv μ ν hμν hkl
  unfold hellingerSquared
  linarith

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

/-! ### Self-affinity for probability measures -/

/-- **Bhattacharyya self-affinity for probability measures.** For any
probability measure `μ`, the Bhattacharyya affinity satisfies
`bhattacharyya μ μ = 1`.

The proof routes through the asymmetric-form bridge
`bhattacharyya_eq_integral_sqrt_rnDeriv_of_ac` (with `ν := μ` and
`hμν := Measure.AbsolutelyContinuous.rfl`), reduces the integrand to
the constant `1` via `Measure.rnDeriv_self` (an a.e. equality), and
evaluates `∫ 1 ∂μ = 1` using `probReal_univ` for the probability
measure. -/
theorem bhattacharyya_self_eq_one (μ : Measure α) [IsProbabilityMeasure μ] :
    bhattacharyya μ μ = 1 := by
  -- Bridge: `bhattacharyya μ μ = ∫ √((μ.rnDeriv μ x).toReal) ∂μ`.
  rw [bhattacharyya_eq_integral_sqrt_rnDeriv_of_ac μ μ
        MeasureTheory.Measure.AbsolutelyContinuous.rfl]
  -- The integrand equals `1` almost everywhere with respect to `μ`.
  have h_rn : μ.rnDeriv μ =ᵐ[μ] fun _ => (1 : ℝ≥0∞) :=
    MeasureTheory.Measure.rnDeriv_self μ
  have h_pt : (fun x => Real.sqrt ((μ.rnDeriv μ x).toReal)) =ᵐ[μ]
      fun _ => (1 : ℝ) := by
    filter_upwards [h_rn] with x hx
    rw [hx]
    simp [ENNReal.toReal_one, Real.sqrt_one]
  rw [MeasureTheory.integral_congr_ae h_pt, MeasureTheory.integral_const,
    probReal_univ, smul_eq_mul, mul_one]

/-!
## TODO

* When `μ` is not absolutely continuous with respect to `ν`, the
  asymmetric-form bridge `bhattacharyya_eq_integral_sqrt_rnDeriv_of_ac`
  fails (the singular part of `μ` is invisible to `μ.rnDeriv ν`). A
  full upstreaming would replace `hμν` by the weaker hypothesis
  `μ ≪ ν + singular part of ν w.r.t. μ`; this requires a Lebesgue
  decomposition of `ν` against `μ` and lands more naturally in the
  proposed `Mathlib/Probability/Distance/Bhattacharyya.lean`.
-/

end LTFP.MathlibExt.Probability
