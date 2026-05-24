/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.Convex.Function
import LTFP.MathlibExt.MatrixAnalysis.CStarRpowIntegrandConcave

/-!
# Operator concavity of `rpow` on `[0, 1]`

This file establishes that the C⋆-algebra power map `a ↦ a ^ p` is
operator concave on the positive cone whenever `p ∈ [0, 1]`, both for
the non-unital `nnrpow` flavor (parameter `p : ℝ≥0`) and the unital
`rpow` flavor (parameter `p : ℝ`).

These are the concavity counterparts to Mathlib's `CFC.monotone_nnrpow`
and `CFC.monotone_rpow` (in
`Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/Order.lean`),
and discharge the first item in the TODO list of that file.

## Main results

* `CFC.concaveOn_nnrpow` : for `p ∈ [0, 1]` (`ℝ≥0`), the map `a ↦ a ^ p`
  is operator concave on `Ici (0 : A)` in any non-unital C⋆-algebra.
* `CFC.concaveOn_rpow` : the same with `p ∈ [0, 1]` (`ℝ`) and `A`
  a unital C⋆-algebra.

## Proof strategy

For the interior `p ∈ (0, 1)`, we use Mathlib's integral representation
`CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁` to write
`a ^ p = ∫ t in Ioi 0, cfcₙ (rpowIntegrand₀₁ p t) a ∂μ`, and then
combine `integral_concaveOn_of_integrand_ae` with the fibrewise concavity
result `CFC.concaveOn_cfcₙ_rpowIntegrand₀₁` (Piece A, in
`CStarRpowIntegrandConcave.lean`). This is the concave analogue of the
proof of `CFC.monotoneOn_nnrpow_Ioo` in upstream Mathlib.

The endpoints `p = 0` and `p = 1` are handled separately:
* nnrpow at `p = 0`: `a ^ (0 : ℝ≥0) = 0` (constant, concave),
* nnrpow at `p = 1`: `a ^ (1 : ℝ≥0) = a` (identity, concave),
* rpow at `p = 0`: `a ^ (0 : ℝ) = 1` (constant, concave).

For the unital `rpow` version we transfer to `nnrpow` via
`CFC.nnrpow_eq_rpow`, exactly mirroring the structure of
`CFC.monotone_rpow`.

## References

* Carlen, Eric A. *Trace inequalities and quantum entropies: An
  introductory course.* (Lemma 2.8 gives the integral-representation
  proof of operator concavity of `x ↦ x ^ p` on `(0, 1)`.)
-/

@[expose] public section

namespace LTFP.MathlibExt.MatrixAnalysis

open scoped NonUnitalContinuousFunctionalCalculus CStarAlgebra NNReal
open Real Set MeasureTheory

namespace CFC

section NonUnitalCStarAlgebra

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Intermediate step: operator concavity of `a ↦ a ^ p` on `Ici 0`
for `p ∈ (0, 1)`, via the integral representation. This is the concave
analogue of `CFC.monotoneOn_nnrpow_Ioo` from Mathlib. -/
private lemma concaveOn_nnrpow_Ioo {p : ℝ≥0} (hp : p ∈ Ioo (0 : ℝ≥0) 1) :
    ConcaveOn ℝ (Ici (0 : A)) (fun a : A => a ^ p) := by
  obtain ⟨μ, hμ⟩ := CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁ A hp
  -- The function equals its integral representation on `Ici 0`.
  have h_eq : (Ici (0 : A)).EqOn (fun a : A => a ^ p)
      (fun a : A => ∫ t in Ioi 0, cfcₙ (Real.rpowIntegrand₀₁ p t) a ∂μ) :=
    fun a ha => (hμ a ha).2
  refine ConcaveOn.congr ?_ h_eq.symm
  -- Apply integral concavity. Restrict measure to Ioi 0.
  refine integral_concaveOn_of_integrand_ae (convex_Ici (0 : A)) ?_
    (fun a ha => (hμ a ha).1)
  -- Almost-everywhere, each fiber `cfcₙ (rpowIntegrand₀₁ p t)` is concave.
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  -- `ht : t ∈ Ioi 0`, i.e. `0 < t`. Apply Piece A.
  exact CFC.concaveOn_cfcₙ_rpowIntegrand₀₁ hp ht

/-- **Operator concavity of `nnrpow` on `[0, 1]`.**

For any non-unital C⋆-algebra `A` and `p ∈ [0, 1]` (as `ℝ≥0`), the map
`a ↦ a ^ p` is operator concave on the positive cone of `A`. -/
lemma concaveOn_nnrpow {p : ℝ≥0} (hp : p ∈ Icc (0 : ℝ≥0) 1) :
    ConcaveOn ℝ (Ici (0 : A)) (fun a : A => a ^ p) := by
  -- Split `Icc 0 1` into `Ioo 0 1 ∪ {0} ∪ {1}` and handle each case.
  have hIcc : Icc (0 : ℝ≥0) 1 = Ioo 0 1 ∪ {0} ∪ {1} := by ext; simp
  rw [hIcc] at hp
  obtain (hp | hp) | hp := hp
  · -- `p ∈ Ioo 0 1`: use the integral-representation lemma.
    exact concaveOn_nnrpow_Ioo hp
  · -- `p = 0`: `a ^ (0 : ℝ≥0) = 0`, constant function is concave.
    have hp0 : p = 0 := hp
    subst hp0
    refine ConcaveOn.congr (concaveOn_const (0 : A) (convex_Ici _)) ?_
    intro a _
    exact CFC.nnrpow_zero.symm
  · -- `p = 1`: `a ^ (1 : ℝ≥0) = a`, identity function is concave.
    have hp1 : p = 1 := hp
    subst hp1
    refine ConcaveOn.congr (concaveOn_id (convex_Ici (0 : A))) ?_
    intro a (ha : 0 ≤ a)
    exact (CFC.nnrpow_one a ha).symm

end NonUnitalCStarAlgebra

section UnitalCStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Operator concavity of `rpow` on `[0, 1]`.**

For any unital C⋆-algebra `A` and `p ∈ [0, 1]` (real), the map
`a ↦ a ^ p` is operator concave on the positive cone of `A`. -/
lemma concaveOn_rpow {p : ℝ} (hp : p ∈ Icc (0 : ℝ) 1) :
    ConcaveOn ℝ (Ici (0 : A)) (fun a : A => a ^ p) := by
  -- Lift the real parameter to ℝ≥0.
  let q : ℝ≥0 := ⟨p, hp.1⟩
  have hq_coe : (q : ℝ) = p := rfl
  have hq_mem : q ∈ Icc (0 : ℝ≥0) 1 := by
    refine ⟨zero_le q, ?_⟩
    -- Need q ≤ 1 in ℝ≥0, which follows from (q : ℝ) = p ≤ 1.
    have : (q : ℝ) ≤ ((1 : ℝ≥0) : ℝ) := by
      rw [hq_coe]; simpa using hp.2
    exact_mod_cast this
  change ConcaveOn ℝ (Ici (0 : A)) (fun a : A => a ^ (q : ℝ))
  cases (zero_le q).lt_or_eq' with
  | inl hq =>
    -- `0 < q`: transfer to nnrpow via `nnrpow_eq_rpow`.
    have h_nnrpow : ConcaveOn ℝ (Ici (0 : A)) (fun a : A => a ^ q) :=
      concaveOn_nnrpow hq_mem
    refine ConcaveOn.congr h_nnrpow ?_
    intro a _
    -- Goal: (fun a => a ^ ↑q) a = (fun a => a ^ q) a
    -- i.e. a ^ (↑q : ℝ) = a ^ (q : ℝ≥0). Use `nnrpow_eq_rpow`.
    exact CFC.nnrpow_eq_rpow hq
  | inr hq =>
    -- `q = 0`, so `p = 0`: `a ^ (0 : ℝ) = 1` on the positive cone, constant.
    have hp0 : p = 0 := by
      have : (q : ℝ) = 0 := by rw [hq]; rfl
      rwa [hq_coe] at this
    subst hp0
    -- Goal: ConcaveOn ℝ (Ici (0 : A)) (fun a : A => a ^ ((q : ℝ≥0) : ℝ))
    -- but `q : ℝ≥0 := ⟨0, _⟩`, so `(q : ℝ) = 0`.
    refine ConcaveOn.congr (concaveOn_const (1 : A) (convex_Ici _)) ?_
    intro a (ha : 0 ≤ a)
    show (1 : A) = a ^ ((q : ℝ≥0) : ℝ)
    have : ((q : ℝ≥0) : ℝ) = 0 := rfl
    rw [this, CFC.rpow_zero a ha]

end UnitalCStarAlgebra

end CFC

end LTFP.MathlibExt.MatrixAnalysis
