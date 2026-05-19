/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import LTFP.MathlibExt.Probability.TotalVariation
import LTFP.MathlibExt.Probability.Distance.Pinsker
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Real

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

**Partial — Bhattacharyya is now a named definition; the two
measure-theoretic steps `tvDist² ≤ 1 - bhattacharyya²` (Le Cam) and
`exp(-KL/2) ≤ bhattacharyya` (Jensen) remain hypothesis inputs.**

The reason the measure-theoretic steps are not yet discharged here:

* **Le Cam step.** Local `tvDist` is defined via signed-measure
  subtraction `((μ - ν) + (ν - μ)) Set.univ / 2`, not via the
  density-integral form `½ ∫|dμ/dτ - dν/dτ| dτ`. Re-establishing the
  density form requires the Jordan decomposition of `μ - ν` as a signed
  measure, which is currently not exposed as a one-line bridge by
  Mathlib. (See the TODOs in `LTFP.MathlibExt.Probability.TotalVariation`
  for the dual gap.)
* **Jensen step.** Requires the conditional version of Jensen's
  inequality applied to `-log` on the `rnDeriv μ ν` density, plus
  careful handling of the `ℝ≥0∞`/`ℝ` boundary and the integrability
  hypothesis `Integrable (llr μ ν) μ` already exposed by
  `Mathlib.InformationTheory.KullbackLeibler.Basic`.

Both steps are tracked as open Mathlib infrastructure gaps. Once they
land upstream, the parametric chain below will collapse to the textbook
Bretagnolle--Huber inequality with the bridge hypotheses removed.

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
theorem tvDist_sq_le_one_sub_exp_neg_klDiv_of_bhattacharyya
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
* `bhattacharyya_le_one_of_isProbabilityMeasure :
  [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] →
  bhattacharyya μ ν ≤ 1`. Standard AM--GM argument
  `√(xy) ≤ (x + y)/2`, integrated against `μ + ν`.
* `bhattacharyya_eq_sqrt_rnDeriv_int_of_ac :
  μ ≪ ν → bhattacharyya μ ν = ∫ x, √((μ.rnDeriv ν x).toReal) ∂ν`.
  The classical asymmetric form; reduces the symmetric definition
  above when `μ ≪ ν`.
* `bhattacharyya_ge_exp_neg_half_klDiv :
  klDiv μ ν ≠ ∞ → Real.exp (-(klDiv μ ν).toReal / 2) ≤ bhattacharyya μ ν`.
  The Jensen step (Step 2 of the BH proof).
* `tvDist_sq_le_one_sub_bhattacharyya_sq : (tvDist μ ν).toReal ^ 2 ≤
  1 - bhattacharyya μ ν ^ 2`. The Le Cam step (Step 3 of the BH proof);
  requires a density representation of `tvDist`.
* When both bridge steps are discharged, the carrier
  `tvDist_le_sqrt_one_sub_exp_neg` in
  `LTFP/Ch15_LowerBounds/Statistical.lean` upgrades from
  `bridge-hypothesis` to A-class.
-/

end LTFP.MathlibExt.Probability
