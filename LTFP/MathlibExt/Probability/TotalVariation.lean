/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import Mathlib.MeasureTheory.Measure.Sub
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.JordanSub

/-!
# Total variation distance between two measures

Proposed Mathlib path: `Mathlib/MeasureTheory/Measure/TotalVariation.lean`.
Proposed Mathlib namespace: `MeasureTheory` (this file currently lives in
`LTFP.MathlibExt.Probability` until upstreamed; see the trailing
`namespace` block for the alias).

The **total variation distance** between two (finite) measures `μ` and `ν` on a
measurable space `α` is a fundamental quantity in probability and information
theory: it measures how far apart the two measures are when viewed as set
functions, and it is the basis for many classical inequalities such as
Pinsker, Bretagnolle–Huber, and the Le Cam two-point lower bound.

This file gives a named definition `tvDist μ ν` for this distance, in terms
of Mathlib's existing truncated subtraction `μ - ν` on measures (see
`Mathlib.MeasureTheory.Measure.Sub`), and proves its basic algebraic
properties. The intent is that this module can be PR'd upstream as a small,
self-contained addition that does not depend on the signed Jordan
decomposition.

## Main definitions

* `MeasureTheory.tvDist μ ν` : the total variation distance between two
  measures, defined as `((μ - ν) + (ν - μ)) Set.univ / 2`. The result lies
  in `ℝ≥0∞`, so nonnegativity is automatic and the definition extends
  naturally to infinite measures (where it may take the value `∞`).

## Main results

* `tvDist_self`   : `tvDist μ μ = 0`. Marked `@[simp]`.
* `tvDist_comm`   : `tvDist μ ν = tvDist ν μ`.
* `tvDist_nonneg` : `0 ≤ tvDist μ ν` (automatic in `ℝ≥0∞`, exposed as a
  named lemma for use in `gcongr`/rewriting chains).
* `tvDist_le_one` : for two probability measures the distance is at most `1`.

## Implementation notes

We choose the formulation `((μ - ν) + (ν - μ)) Set.univ / 2` because:

1. it is manifestly symmetric in `μ` and `ν`;
2. it lives in `ℝ≥0∞`, so nonnegativity and `0 ≤ ⊤` are free;
3. it reuses the existing `Measure.sub_self` and `Measure.sub_le` simp
   lemmas, keeping the basic API one-liners;
4. it does not require the Jordan decomposition of a signed measure,
   keeping the import surface minimal.

For probability measures this agrees with the classical
`sup_{A measurable} |μ A - ν A|` formulation, but stating the equivalence
requires the signed Jordan decomposition that is intentionally out of
scope for this minimal module.

The characterization `tvDist μ ν = 0 ↔ μ = ν` for finite measures requires
the implication `μ - ν = 0 → μ ≤ ν`, which is not currently a standalone
Mathlib lemma (Mathlib only provides the converse `Measure.sub_eq_zero_of_le`).
The natural proof route is via the Jordan decomposition of `μ - ν` as a
signed measure; once that infrastructure lands upstream, this
characterization can be added in a single line by combining the two
`sub_eq_zero` directions with `le_antisymm`. See the *Future work* section
in the accompanying PR description.

## References

* A. B. Tsybakov, *Introduction to Nonparametric Estimation*, Springer,
  2009, Section 2.4.
* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University
  Press, 1998, Chapter 25.
* L. Devroye, L. Györfi, G. Lugosi, *A Probabilistic Theory of Pattern
  Recognition*, Springer, 1996, Chapter 8.

## Tags

total variation, total variation distance, statistical distance,
probability measure, finite measure
-/

namespace LTFP.MathlibExt.Probability

-- When upstreamed, replace `LTFP.MathlibExt.Probability` by `MeasureTheory`
-- throughout this file. All declarations are intended to live in the
-- `MeasureTheory` namespace.

open MeasureTheory ENNReal

variable {α : Type*} [MeasurableSpace α]

/-- The **total variation distance** between two measures `μ` and `ν` on a
measurable space `α`, defined as
`tvDist μ ν = ((μ - ν) + (ν - μ)) Set.univ / 2`.

For finite measures this matches the standard textbook definition
`½ · ‖μ - ν‖_TV`; for two probability measures it lies in `[0, 1]`
(see `tvDist_le_one`). The result is valued in `ℝ≥0∞` so that
nonnegativity is automatic and the definition extends naturally to
infinite measures, where it may take the value `∞`. -/
noncomputable def tvDist (μ ν : Measure α) : ℝ≥0∞ :=
  ((μ - ν) + (ν - μ)) Set.univ / 2

/-- The total variation distance from a measure to itself vanishes. -/
@[simp]
theorem tvDist_self (μ : Measure α) : tvDist μ μ = 0 := by
  simp [tvDist]

/-- The total variation distance is symmetric in its two arguments. -/
theorem tvDist_comm (μ ν : Measure α) : tvDist μ ν = tvDist ν μ := by
  simp [tvDist, add_comm]

/-- The total variation distance is nonnegative. This is automatic since
`tvDist` is valued in `ℝ≥0∞`, but the lemma is provided as a named entry
point for `gcongr`, `positivity`-style proofs, and downstream rewriting. -/
theorem tvDist_nonneg (μ ν : Measure α) : 0 ≤ tvDist μ ν :=
  zero_le _

/-- For two probability measures the total variation distance is bounded by
one. The proof uses `Measure.sub_le : μ - ν ≤ μ` to bound each truncated
difference by the total mass of the corresponding probability measure,
and then divides by `2`. -/
theorem tvDist_le_one (μ ν : ProbabilityMeasure α) :
    tvDist (μ : Measure α) (ν : Measure α) ≤ 1 := by
  classical
  set μ' : Measure α := (μ : Measure α)
  set ν' : Measure α := (ν : Measure α)
  -- Each truncated difference is bounded by the corresponding measure.
  have h₁ : (μ' - ν') Set.univ ≤ μ' Set.univ :=
    Measure.sub_le (μ := μ') (ν := ν') Set.univ
  have h₂ : (ν' - μ') Set.univ ≤ ν' Set.univ :=
    Measure.sub_le (μ := ν') (ν := μ') Set.univ
  have hμ : μ' Set.univ = 1 := measure_univ
  have hν : ν' Set.univ = 1 := measure_univ
  -- Add the two pointwise bounds and rewrite the totals.
  have hsum :
      ((μ' - ν') + (ν' - μ')) Set.univ ≤ μ' Set.univ + ν' Set.univ := by
    simpa [Measure.add_apply] using add_le_add h₁ h₂
  have hsum' : ((μ' - ν') + (ν' - μ')) Set.univ ≤ 2 := by
    have h2 : μ' Set.univ + ν' Set.univ = 2 := by
      rw [hμ, hν]; norm_num
    rw [h2] at hsum
    exact hsum
  -- Divide by 2.
  have h2ne : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  calc tvDist μ' ν'
      = ((μ' - ν') + (ν' - μ')) Set.univ / 2 := rfl
    _ ≤ 2 / 2 := ENNReal.div_le_div_right hsum' 2
    _ = 1 := ENNReal.div_self h2ne h2top

/-- For two probability measures the total variation distance is not `∞`.
This is the `ne_top` companion to `tvDist_le_one`, useful as an `ENNReal`
finiteness side condition for downstream `toReal` / `lift` rewrites. -/
theorem tvDist_ne_top (μ ν : ProbabilityMeasure α) :
    tvDist (μ : Measure α) (ν : Measure α) ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (tvDist_le_one μ ν)

/-- The real-valued total variation distance is nonnegative. Provided as a
named entry point so downstream lemmas can write `0 ≤ (tvDist μ ν).toReal`
without unfolding `ENNReal.toReal`. -/
theorem tvDist_toReal_nonneg (μ ν : Measure α) :
    0 ≤ (tvDist μ ν).toReal :=
  ENNReal.toReal_nonneg

/-- For two probability measures, the real-valued total variation distance
is at most `1`. This is the `toReal` lift of `tvDist_le_one`, packaged for
consumers (Pinsker, Bretagnolle–Huber, Le Cam) that work in `ℝ` rather
than `ℝ≥0∞`. -/
theorem tvDist_toReal_le_one (μ ν : ProbabilityMeasure α) :
    (tvDist (μ : Measure α) (ν : Measure α)).toReal ≤ 1 := by
  have hle : tvDist (μ : Measure α) (ν : Measure α) ≤ 1 := tvDist_le_one μ ν
  have hne : tvDist (μ : Measure α) (ν : Measure α) ≠ ∞ := tvDist_ne_top μ ν
  have := (ENNReal.toReal_le_toReal hne ENNReal.one_ne_top).mpr hle
  simpa using this

/-! ### Identification with the signed Jordan total variation

The pair `(μ - ν, ν - μ)` of mutually singular finite measures is exactly the
Jordan decomposition of `μ.toSignedMeasure - ν.toSignedMeasure` (see
`MeasureTheory.Measure.toJordanDecomposition_toSignedMeasure_sub`). Hence
the sum `(μ - ν) + (ν - μ)` agrees with the total variation measure of
that signed measure, and `tvDist μ ν` equals half its total mass. This
identification is the bridge that lets us discharge the
`tvDist μ ν = 0 ↔ μ = ν` characterisation without re-proving anything
about signed measures here. -/

/-- The sum `(μ - ν) + (ν - μ)` is the total variation measure of the
signed measure `μ.toSignedMeasure - ν.toSignedMeasure`. This is the
infrastructure lemma underlying `tvDist_eq_signedMeasure_totalVariation_div_two`
and `tvDist_eq_zero_iff`. -/
theorem add_sub_eq_signedMeasure_totalVariation
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    (μ - ν) + (ν - μ) =
      (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation := by
  rw [MeasureTheory.SignedMeasure.totalVariation,
    MeasureTheory.Measure.toJordanDecomposition_toSignedMeasure_sub,
    MeasureTheory.Measure.jordanDecompositionOfToSignedMeasureSub_posPart,
    MeasureTheory.Measure.jordanDecompositionOfToSignedMeasureSub_negPart]

/-- The total variation distance of two finite measures equals half the
total mass of the total variation measure of the signed difference
`μ.toSignedMeasure - ν.toSignedMeasure`. This is the reusable identity
extracted from the unconditional Le Cam / Bhattacharyya bound and is the
bridge to the Jordan / Hahn decomposition API. -/
theorem tvDist_eq_signedMeasure_totalVariation_div_two
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tvDist μ ν =
      (μ.toSignedMeasure - ν.toSignedMeasure).totalVariation Set.univ / 2 := by
  rw [tvDist, add_sub_eq_signedMeasure_totalVariation]

/-- **Total variation distance separates finite measures.** For two finite
measures `μ` and `ν`, `tvDist μ ν = 0` iff `μ = ν`. The forward direction
uses the Jordan decomposition of `μ.toSignedMeasure - ν.toSignedMeasure`
together with the injectivity of `Measure.toSignedMeasure` on finite
measures (Mathlib's `toSignedMeasure_eq_toSignedMeasure_iff`); the
backward direction is the diagonal vanishing `tvDist_self`. This is the
first metric axiom for the `tvDist` API. -/
theorem tvDist_eq_zero_iff
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    tvDist μ ν = 0 ↔ μ = ν := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  -- Step 1: peel off the division by 2.
  have h2top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have hmass : ((μ - ν) + (ν - μ)) Set.univ = 0 := by
    have := h
    rw [tvDist, ENNReal.div_eq_zero_iff] at this
    rcases this with h0 | h2 -- div_eq_zero_iff gives a = 0 ∨ b = ∞
    · exact h0
    · exact absurd h2 h2top
  -- Step 2: total mass zero on a finite measure ⟹ the measure itself is zero.
  have hzero : (μ - ν) + (ν - μ) = 0 := by
    have hadd : ((μ - ν) + (ν - μ)) Set.univ = 0 := hmass
    -- `μ Set.univ = 0 ↔ μ = 0` for measures (Mathlib's `measure_univ_eq_zero`).
    exact (MeasureTheory.Measure.measure_univ_eq_zero (μ := (μ - ν) + (ν - μ))).1 hadd
  -- Step 3: split the sum of two nonneg measures into two zero conditions.
  have hsplit : (μ - ν) Set.univ = 0 ∧ (ν - μ) Set.univ = 0 := by
    have hadd : ((μ - ν) + (ν - μ)) Set.univ = 0 := hmass
    rw [MeasureTheory.Measure.add_apply, add_eq_zero] at hadd
    exact hadd
  obtain ⟨hμν, hνμ⟩ := hsplit
  have hμν0 : μ - ν = 0 :=
    (MeasureTheory.Measure.measure_univ_eq_zero (μ := μ - ν)).1 hμν
  have hνμ0 : ν - μ = 0 :=
    (MeasureTheory.Measure.measure_univ_eq_zero (μ := ν - μ)).1 hνμ
  -- Step 4: feed the two zero conditions into the Jordan decomposition.
  have hjd :
      MeasureTheory.Measure.jordanDecompositionOfToSignedMeasureSub μ ν =
        (0 : MeasureTheory.JordanDecomposition α) := by
    apply MeasureTheory.JordanDecomposition.ext
    · simp [MeasureTheory.Measure.jordanDecompositionOfToSignedMeasureSub_posPart, hμν0]
    · simp [MeasureTheory.Measure.jordanDecompositionOfToSignedMeasureSub_negPart, hνμ0]
  -- Step 5: zero Jordan decomposition ⟹ signed measure is zero.
  have hsig : μ.toSignedMeasure - ν.toSignedMeasure = 0 := by
    rw [← MeasureTheory.Measure.jordanDecompositionOfToSignedMeasureSub_toSignedMeasure,
      hjd, MeasureTheory.JordanDecomposition.toSignedMeasure_zero]
  -- Step 6: signed measures of finite measures coincide ⟹ measures coincide.
  have hsig' : μ.toSignedMeasure = ν.toSignedMeasure := by
    rwa [sub_eq_zero] at hsig
  exact MeasureTheory.Measure.toSignedMeasure_eq_toSignedMeasure_iff.mp hsig'

/-- The unconditional corollary: equal finite measures have zero total
variation distance. Already covered by the `tvDist_self` simp lemma when
specialised; surfaced here as the explicit `μ = ν → tvDist μ ν = 0`
direction of `tvDist_eq_zero_iff` for callers that want a one-liner
without `Iff.mpr`. -/
theorem tvDist_eq_zero_of_eq
    {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : μ = ν) : tvDist μ ν = 0 := by
  subst h; simp

/-! ### Examples

These examples demonstrate basic usage of the `tvDist` API and double as
quick smoke tests that the simp set fires as expected. -/

section Examples

variable (μ ν : Measure α)

/-- `tvDist` vanishes on the diagonal. -/
example : tvDist μ μ = 0 := by simp

/-- `tvDist` is symmetric. -/
example : tvDist μ ν = tvDist ν μ := tvDist_comm μ ν

/-- For probability measures, `tvDist` is a value in `[0, 1]` in `ℝ≥0∞`. -/
example (μ ν : ProbabilityMeasure α) :
    tvDist (μ : Measure α) (ν : Measure α) ≤ 1 :=
  tvDist_le_one μ ν

end Examples

/-!
## TODO

* `tvDist_triangle` : the triangle inequality. Expected from
  `Measure.sub` subadditivity once a `Measure.sub_add_sub_le` lemma is
  available. This is sub-step 2 of the TV-metric API milestone.
* Equivalence with the supremum formulation
  `tvDist μ ν = ⨆ A, |μ A - ν A| / 2` for finite signed measures,
  via the Jordan/Hahn decomposition.
* Connections to KL divergence (Pinsker's inequality) and Hellinger
  distance (Bretagnolle–Huber). These belong in separate files but
  should depend on the API exposed here.
-/

end LTFP.MathlibExt.Probability
