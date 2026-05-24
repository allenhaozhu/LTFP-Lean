/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Tactic.NoncommRing
import LTFP.MathlibExt.MatrixAnalysis.CStarShiftedResolventConcave
import LTFP.MathlibExt.MatrixAnalysis.CStarRpowIntegrandConcave

/-!
# Hansen-Pedersen Jensen inequality for `rpow` on positive elements

This file builds toward `CFC.star_mul_rpow_mul_le_rpow_star_mul`, the
Hansen-Pedersen Jensen inequality: for `0 ≤ a`, `star v * v ≤ 1`,
`p ∈ [0,1]`,
`star v * (a ^ p) * v ≤ (star v * a * v) ^ p`.

This is Part 5 of the B6 L3 carrier closure path (Parts 1–4 already
landed in `CStarShiftedResolventConcave`, `CStarRpowIntegrandConcave`,
`CStarRpowConcave`, `CStarLogConcave`).

The full proof for `p ∈ (0,1)` reduces via the rpow integral
representation to a conjugated shifted-resolvent inequality
(Sub-Part 5.1). This file contains the trivial endpoint cases
(`p = 0` and `p = 1`, Sub-Part 5.4) and the central conjugated
shifted-resolvent inequality (Sub-Part 5.1) via a Hansen–Pedersen
sum-of-squares decomposition.

## Main results

* `CFC.star_mul_rpow_mul_le_rpow_star_mul_zero` — endpoint `p = 0`.
* `CFC.star_mul_rpow_mul_le_rpow_star_mul_one` — endpoint `p = 1`.
* `CFC.star_mul_one_sub_one_add_inv_mul_le` — conjugated shifted
  resolvent inequality.

## Proof strategy for `CFC.star_mul_one_sub_one_add_inv_mul_le`

Following Hansen–Pedersen (1982), set `R := (1+a)⁻¹` and `S := (1 + v* a v)⁻¹`.
The key algebraic identity (`compression_inv_sos`) states

```
v* R v + (1 - v* v) - S = star ξ * (1 + a) * ξ + star η * (1 - v* v) * η
```

where `ξ := R v - v S` and `η := 1 - S`. Both summands are
star-left-conjugations of nonneg elements, so the RHS is `≥ 0`.
After rewriting both sides of the target inequality via
`cfc_one_sub_one_add_inv_eq`, the goal becomes exactly this `≥ 0`.
-/

@[expose] public section

namespace LTFP.MathlibExt.MatrixAnalysis

open scoped NNReal CStarAlgebra

/-- **Hansen-Pedersen Jensen inequality, endpoint `p = 0`.**

For `0 ≤ a` and `star v * v ≤ 1`, we have
`star v * (a ^ (0 : ℝ)) * v ≤ (star v * a * v) ^ (0 : ℝ)`.

Both sides collapse via `CFC.rpow_zero`: the left side becomes
`star v * 1 * v = star v * v`, the right side becomes `1`, and the
inequality is exactly the hypothesis `hv`. -/
lemma CFC.star_mul_rpow_mul_le_rpow_star_mul_zero
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a v : A} (ha : 0 ≤ a) (hv : star v * v ≤ 1) :
    star v * (a ^ (0 : ℝ)) * v ≤ (star v * a * v) ^ (0 : ℝ) := by
  have hvav : 0 ≤ star v * a * v := star_left_conjugate_nonneg ha v
  rw [_root_.CFC.rpow_zero a ha, _root_.CFC.rpow_zero (star v * a * v) hvav,
    mul_one]
  exact hv

/-- **Hansen-Pedersen Jensen inequality, endpoint `p = 1`.**

For `0 ≤ a` and `star v * v ≤ 1`, we have
`star v * (a ^ (1 : ℝ)) * v ≤ (star v * a * v) ^ (1 : ℝ)`.

Both sides collapse via `CFC.rpow_one` to `star v * a * v`, so the
inequality is reflexivity. The hypothesis `hv` is not used here but
is retained so the lemma signature matches the general statement
`star_mul_rpow_mul_le_rpow_star_mul` for arbitrary `p ∈ [0,1]`. -/
lemma CFC.star_mul_rpow_mul_le_rpow_star_mul_one
    {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {a v : A} (ha : 0 ≤ a) (hv : star v * v ≤ 1) :
    star v * (a ^ (1 : ℝ)) * v ≤ (star v * a * v) ^ (1 : ℝ) := by
  have hvav : 0 ≤ star v * a * v := star_left_conjugate_nonneg ha v
  rw [_root_.CFC.rpow_one a ha, _root_.CFC.rpow_one (star v * a * v) hvav]

/-! ### Pure noncommutative algebraic SOS identity

The first step of the Hansen–Pedersen Jensen proof is a purely algebraic
identity in a non-commutative ring with star. Given self-adjoint
`a, r, s` with `r` a two-sided inverse of `1 + a` and `s` a two-sided
inverse of `1 + v* a v`, the difference

```
D := v* r v + (1 - v* v) - s
```

decomposes as a sum of two star-left-conjugated nonneg expressions:

```
D = star (r v - v s) * (1 + a) * (r v - v s) + star (1 - s) * (1 - v* v) * (1 - s)
```

The decomposition is verified by direct expansion. -/

section SosIdentity

variable {R : Type*} [Ring R] [StarRing R]

/-- **Sum-of-squares decomposition for the difference of shifted resolvents.**

Given self-adjoint `a, r, s : R` with `r` a two-sided inverse of `1 + a`
and `s` a two-sided inverse of `1 + star v * a * v`, the algebraic
identity

```
star v * r * v + (1 - star v * v) - s =
  star (r * v - v * s) * (1 + a) * (r * v - v * s) +
  star (1 - s) * (1 - star v * v) * (1 - s)
```

holds in `R`. Both summands on the RHS are star-left-conjugations,
which makes positivity transparent in an ordered C⋆-algebra. -/
lemma compression_inv_sos
    (a v r s : R)
    (hr : star r = r) (hs : star s = s)
    (hr_l : (1 + a) * r = 1) (hr_r : r * (1 + a) = 1)
    (hs_l : (1 + star v * a * v) * s = 1)
    (hs_r : s * (1 + star v * a * v) = 1) :
    star v * r * v + (1 - star v * v) - s =
      star (r * v - v * s) * (1 + a) * (r * v - v * s) +
      star (1 - s) * (1 - star v * v) * (1 - s) := by
  -- Substitution form of one inverse equation we need below:
  -- s*(1 + v*av) = 1 ⟹ s*(v*av) = 1 - s.
  have h_sc : s * (star v * a * v) = 1 - s := by
    have h : s + s * (star v * a * v) = 1 := by
      have h0 := hs_r; rw [mul_add, mul_one] at h0; exact h0
    exact eq_sub_of_add_eq' h
  -- Expand the stars on the RHS using `star r = r` and `star s = s`.
  rw [show star (r * v - v * s) = star v * r - s * star v from by
        rw [star_sub, star_mul, star_mul, hr, hs],
      show star (1 - s) = 1 - s from by
        rw [star_sub, star_one, hs]]
  -- Re-bracket the bilinear product on the RHS so that the two key
  -- subterms `r * (1 + a)` and `(1 + a) * r` are exposed (this is pure
  -- associativity, dispatched by `noncomm_ring`):
  --   (star v * r - s * star v) * (1 + a) * (r * v - v * s)
  -- = star v * (r * (1+a)) * (r * v) - star v * (r * (1+a)) * (v * s)
  --   - s * (star v * ((1+a) * r)) * v + s * star v * v * s
  --   + s * (star v * a * v) * s.
  -- Then `hr_r : r * (1+a) = 1` and `hr_l : (1+a) * r = 1` collapse the
  -- first three terms, while `h_sc` handles the s*v*a*v*s tail.
  have eq_term1 :
      (star v * r - s * star v) * (1 + a) * (r * v - v * s)
        = star v * (r * (1 + a)) * (r * v) - star v * (r * (1 + a)) * (v * s)
          - s * (star v * ((1 + a) * r)) * v + s * star v * v * s
          + s * (star v * a * v) * s := by
    noncomm_ring
  rw [eq_term1, hr_r, hr_l]
  -- Apply h_sc to `s * (star v * a * v) * s` (re-associating first so
  -- the subterm `s * (star v * a * v)` matches).
  rw [show s * (star v * a * v) * s = (s * (star v * a * v)) * s from by
        noncomm_ring]
  rw [h_sc]
  -- All non-ring substitutions applied; finish with pure ring algebra.
  noncomm_ring

end SosIdentity

/-! ### Conjugated shifted-resolvent inequality

The public theorem of this section: for `0 ≤ a` in a unital C⋆-algebra
and a sub-isometric `v` (`star v * v ≤ 1`), the shifted-resolvent
function `f(x) = 1 - (1+x)⁻¹` satisfies the Hansen–Pedersen Jensen
inequality

```
star v * f(a) * v ≤ f(star v * a * v).
```

The proof packages the SOS decomposition `compression_inv_sos`. -/

section ShiftedResolventJensen

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped CStarAlgebra

/-- **Conjugated Hansen–Pedersen Jensen for the shifted resolvent.**

For `0 ≤ a` and `star v * v ≤ 1` in a unital C⋆-algebra,

```
star v * cfc (fun x : ℝ => 1 - (1 + x)⁻¹) a * v
    ≤ cfc (fun x : ℝ => 1 - (1 + x)⁻¹) (star v * a * v).
```

This is the central operator-Jensen inequality for the shifted
resolvent. The proof reduces to the SOS identity `compression_inv_sos`:
setting `R = (1+a)⁻¹` and `S = (1 + v* a v)⁻¹`, the target inequality
is equivalent to `D := v* R v + (1 - v* v) - S ≥ 0`, and the SOS
decomposition writes `D` as a sum of two star-left-conjugations of
nonneg elements, hence `D ≥ 0`. -/
lemma CFC.star_mul_one_sub_one_add_inv_mul_le
    {a v : A} (ha : 0 ≤ a) (hv : star v * v ≤ 1) :
    star v * cfc (fun x : ℝ => 1 - (1 + x)⁻¹) a * v
      ≤ cfc (fun x : ℝ => 1 - (1 + x)⁻¹) (star v * a * v) := by
  -- Setup: derive star v * a * v ≥ 0.
  have hvav : 0 ≤ star v * a * v := star_left_conjugate_nonneg ha v
  -- 1 + a and 1 + (star v * a * v) are strictly positive (sum of 1 and nonneg).
  have h1_a_sp : IsStrictlyPositive (1 + a) :=
    IsStrictlyPositive.add_nonneg isStrictlyPositive_one ha
  have h1_vav_sp : IsStrictlyPositive (1 + star v * a * v) :=
    IsStrictlyPositive.add_nonneg isStrictlyPositive_one hvav
  -- Promote to units U_a and U_vav.
  set U_a : Aˣ := h1_a_sp.isUnit.unit with hU_a_def
  set U_vav : Aˣ := h1_vav_sp.isUnit.unit with hU_vav_def
  have hU_a_eq : (U_a : A) = 1 + a := IsUnit.unit_spec _
  have hU_vav_eq : (U_vav : A) = 1 + star v * a * v := IsUnit.unit_spec _
  -- Underlying elements of the inverses.
  set R : A := ((U_a⁻¹ : Aˣ) : A) with hR_def
  set S : A := ((U_vav⁻¹ : Aˣ) : A) with hS_def
  -- Two-sided inverse equations.
  have hR_l : (1 + a) * R = 1 := by
    show (1 + a) * ((U_a⁻¹ : Aˣ) : A) = 1
    rw [← hU_a_eq]
    exact_mod_cast U_a.mul_inv
  have hR_r : R * (1 + a) = 1 := by
    show ((U_a⁻¹ : Aˣ) : A) * (1 + a) = 1
    rw [← hU_a_eq]
    exact_mod_cast U_a.inv_mul
  have hS_l : (1 + star v * a * v) * S = 1 := by
    show (1 + star v * a * v) * ((U_vav⁻¹ : Aˣ) : A) = 1
    rw [← hU_vav_eq]
    exact_mod_cast U_vav.mul_inv
  have hS_r : S * (1 + star v * a * v) = 1 := by
    show ((U_vav⁻¹ : Aˣ) : A) * (1 + star v * a * v) = 1
    rw [← hU_vav_eq]
    exact_mod_cast U_vav.inv_mul
  -- Self-adjointness of R and S: R = Ring.inverse (1 + a), and
  -- star (Ring.inverse x) = Ring.inverse (star x). Since 1 + a is self-adjoint
  -- (as a sum of self-adjoint elements), so is R.
  have hR_sa : star R = R := by
    -- star R = Ring.inverse (star (1+a)) = Ring.inverse (1+a) = R.
    show star ((U_a⁻¹ : Aˣ) : A) = ((U_a⁻¹ : Aˣ) : A)
    have h1a_sa : IsSelfAdjoint ((U_a : A)) := by
      rw [hU_a_eq]
      exact (IsSelfAdjoint.one (R := A)).add (IsSelfAdjoint.of_nonneg ha)
    -- Use Ring.inverse / Units interaction.
    have h_inv_eq : ((U_a⁻¹ : Aˣ) : A) = Ring.inverse ((U_a : A)) := by
      rw [Ring.inverse_unit]
    rw [h_inv_eq]
    rw [← Ring.inverse_star]
    rw [h1a_sa.star_eq]
  have hS_sa : star S = S := by
    show star ((U_vav⁻¹ : Aˣ) : A) = ((U_vav⁻¹ : Aˣ) : A)
    have h1vav_sa : IsSelfAdjoint ((U_vav : A)) := by
      rw [hU_vav_eq]
      exact (IsSelfAdjoint.one (R := A)).add (IsSelfAdjoint.of_nonneg hvav)
    have h_inv_eq : ((U_vav⁻¹ : Aˣ) : A) = Ring.inverse ((U_vav : A)) := by
      rw [Ring.inverse_unit]
    rw [h_inv_eq, ← Ring.inverse_star, h1vav_sa.star_eq]
  -- Apply the SOS identity.
  have h_sos := compression_inv_sos (R := A) a v R S hR_sa hS_sa hR_l hR_r hS_l hS_r
  -- Derive positivity: D = star ξ * (1+a) * ξ + star η * (1 - v*v) * η ≥ 0.
  have hD_nonneg : 0 ≤ star v * R * v + (1 - star v * v) - S := by
    rw [h_sos]
    -- D = star ξ * (1+a) * ξ + star η * (1 - v*v) * η, both summands ≥ 0.
    refine add_nonneg ?_ ?_
    · -- star (R*v - v*S) * (1+a) * (R*v - v*S) ≥ 0
      exact star_left_conjugate_nonneg
        (add_nonneg (zero_le_one (α := A)) ha) (R * v - v * S)
    · -- star (1 - S) * (1 - star v * v) * (1 - S) ≥ 0
      have h1vv_nn : (0 : A) ≤ 1 - star v * v := sub_nonneg.mpr hv
      exact star_left_conjugate_nonneg h1vv_nn (1 - S)
  -- Translate D ≥ 0 into the target inequality.
  -- Target: star v * cfc f a * v ≤ cfc f (star v * a * v)
  -- where f(x) = 1 - (1+x)⁻¹.
  -- By cfc_one_sub_one_add_inv_eq: cfc f a = 1 - R, cfc f (v*av) = 1 - S.
  -- So target becomes: star v * (1 - R) * v ≤ 1 - S,
  --   i.e., star v * v - star v * R * v ≤ 1 - S,
  --   i.e., 0 ≤ 1 - S - (star v * v - star v * R * v) = star v * R * v + (1 - star v * v) - S = D ≥ 0. ✓
  have h_cfc_a : cfc (fun x : ℝ => 1 - (1 + x)⁻¹) a = 1 - R := by
    have := cfc_one_sub_one_add_inv_eq (A := A) ha
    -- this : cfc f a = 1 - (h1_a_sp.isUnit.unit⁻¹ : Aˣ)
    -- and U_a = h1_a_sp.isUnit.unit so U_a⁻¹ = h1_a_sp.isUnit.unit⁻¹.
    show cfc (fun x : ℝ => 1 - (1 + x)⁻¹) a = 1 - ((U_a⁻¹ : Aˣ) : A)
    exact this
  have h_cfc_vav : cfc (fun x : ℝ => 1 - (1 + x)⁻¹) (star v * a * v) = 1 - S := by
    have := cfc_one_sub_one_add_inv_eq (A := A) hvav
    show cfc (fun x : ℝ => 1 - (1 + x)⁻¹) (star v * a * v) = 1 - ((U_vav⁻¹ : Aˣ) : A)
    exact this
  rw [h_cfc_a, h_cfc_vav]
  -- Goal: star v * (1 - R) * v ≤ 1 - S
  -- Equivalent: 0 ≤ 1 - S - (star v * (1 - R) * v) = star v * R * v + (1 - star v * v) - S
  rw [← sub_nonneg]
  have h_rearrange :
      1 - S - star v * (1 - R) * v = star v * R * v + (1 - star v * v) - S := by
    noncomm_ring
  rw [h_rearrange]
  exact hD_nonneg

end ShiftedResolventJensen

/-! ### Non-unital lift of the shifted-resolvent Jensen inequality

We lift Sub-Part 5.1 (`CFC.star_mul_one_sub_one_add_inv_mul_le`) from the
unital setting to the non-unital setting via `Unitization.real_cfcₙ_eq_cfc_inr`.
The function `f(x) = 1 - (1+x)⁻¹` vanishes at `0`, so the non-unital
`cfcₙ` agrees with the unital `cfc` on the unitization `A⁺¹`. -/

section ShiftedResolventJensenNonUnital

open scoped CStarAlgebra
open MeasureTheory Set Real

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Unitization

/-- **Non-unital shifted-resolvent Jensen helper.**

For `0 ≤ a` and `star (↑v : A⁺¹) * ↑v ≤ 1` (the sub-isometric condition
expressed in the unitization), the non-unital `cfcₙ` shifted-resolvent
function `f(x) = 1 - (1+x)⁻¹` satisfies the Jensen-type inequality

```
star v * cfcₙ f a * v ≤ cfcₙ f (star v * a * v).
```

This lifts the unital version (`CFC.star_mul_one_sub_one_add_inv_mul_le`)
through `Unitization.real_cfcₙ_eq_cfc_inr`: since `f 0 = 0`, both
`cfcₙ f a` and `cfcₙ f (star v * a * v)` agree on `A⁺¹` with the unital
`cfc f` of the inr-images, and the unital 5.1 closes the lifted goal. -/
private lemma star_mul_cfcₙ_one_sub_one_add_inv_mul_le
    {a v : A} (ha : 0 ≤ a)
    (hv : star (v : Unitization ℂ A) * (v : Unitization ℂ A) ≤ 1) :
    star v * cfcₙ (fun x : ℝ => 1 - (1 + x)⁻¹) a * v
      ≤ cfcₙ (fun x : ℝ => 1 - (1 + x)⁻¹) (star v * a * v) := by
  -- The function vanishes at zero, enabling the inr-transport.
  have hf0 : (fun x : ℝ => 1 - (1 + x)⁻¹) 0 = 0 := by norm_num
  -- Star left conjugation preserves nonnegativity.
  have hvav : 0 ≤ star v * a * v := star_left_conjugate_nonneg ha v
  -- Self-adjointness of both sides for lifting via `inr_le_iff`.
  have h_lhs_sa : IsSelfAdjoint (star v * cfcₙ (fun x : ℝ => 1 - (1 + x)⁻¹) a * v) := by
    have h_cfcₙ_sa : IsSelfAdjoint (cfcₙ (fun x : ℝ => 1 - (1 + x)⁻¹) a) :=
      cfcₙ_predicate _ _
    -- star v * (sa) * v is sa.
    rw [IsSelfAdjoint, star_mul, star_mul, star_star, h_cfcₙ_sa.star_eq, mul_assoc]
  have h_rhs_sa : IsSelfAdjoint
      (cfcₙ (fun x : ℝ => 1 - (1 + x)⁻¹) (star v * a * v)) :=
    cfcₙ_predicate _ _
  -- Lift goal to A⁺¹ via inr_le_iff.
  rw [← Unitization.inr_le_iff _ _ h_lhs_sa h_rhs_sa]
  -- Distribute inr over * and star on LHS, and over * on RHS.
  have h_lhs_dist :
      ((star v * cfcₙ (fun x : ℝ => 1 - (1 + x)⁻¹) a * v : A) : Unitization ℂ A)
        = star (v : Unitization ℂ A)
          * ((cfcₙ (fun x : ℝ => 1 - (1 + x)⁻¹) a : A) : Unitization ℂ A)
          * (v : Unitization ℂ A) := by
    rw [Unitization.inr_mul ℂ, Unitization.inr_mul ℂ, Unitization.inr_star]
  have h_rhs_inr_arg : ((star v * a * v : A) : Unitization ℂ A)
      = star (v : Unitization ℂ A) * (a : Unitization ℂ A) * (v : Unitization ℂ A) := by
    rw [Unitization.inr_mul ℂ, Unitization.inr_mul ℂ, Unitization.inr_star]
  rw [h_lhs_dist]
  rw [Unitization.real_cfcₙ_eq_cfc_inr a _ hf0]
  rw [Unitization.real_cfcₙ_eq_cfc_inr (star v * a * v) _ hf0]
  rw [h_rhs_inr_arg]
  -- Now apply the unital 5.1 in Unitization ℂ A.
  have ha' : (0 : Unitization ℂ A) ≤ (a : Unitization ℂ A) := inr_nonneg_iff.mpr ha
  exact CFC.star_mul_one_sub_one_add_inv_mul_le (A := Unitization ℂ A) ha' hv

/-- **Per-`t` integrand Hansen-Pedersen Jensen inequality (B6 L3 Sub-Part 5.2).**

For `p ∈ (0, 1)`, `t > 0`, `0 ≤ a` in a non-unital C⋆-algebra, and
`star (↑v : A⁺¹) * ↑v ≤ 1`, the per-`t` integrand
`f_t(x) = Real.rpowIntegrand₀₁ p t x = t^p * (t⁻¹ - (t + x)⁻¹)` satisfies
the Hansen-Pedersen Jensen inequality

```
star v * cfcₙ (rpowIntegrand₀₁ p t) a * v
    ≤ cfcₙ (rpowIntegrand₀₁ p t) (star v * a * v).
```

This is the parametric-in-`t` upgrade of Sub-Part 5.1. The proof transports
through Mathlib's identity
`CFC.cfcₙ_rpowIntegrand₀₁_eq_cfcₙ_rpowIntegrand₀₁_one` which expresses
`cfcₙ (rpowIntegrand₀₁ p t) a = t^(p-1) • cfcₙ (rpowIntegrand₀₁ p 1) (t⁻¹ • a)`
and the identification `cfcₙ (rpowIntegrand₀₁ p 1) = cfcₙ (1 - (1+·)⁻¹)`
(`cfcₙ_rpowIntegrand₀₁_one_eq`). The Jensen inequality then follows from
the non-unital shifted-resolvent helper above applied at `t⁻¹ • a`, with a
positive `t^(p-1)`-scalar multiplication preserving the inequality. -/
lemma CFC.star_mul_cfcₙ_rpowIntegrand₀₁_mul_le
    {p t : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) (ht : 0 < t)
    {a v : A} (ha : 0 ≤ a)
    (hv : star (v : Unitization ℂ A) * (v : Unitization ℂ A) ≤ 1) :
    star v * cfcₙ (Real.rpowIntegrand₀₁ p t) a * v
      ≤ cfcₙ (Real.rpowIntegrand₀₁ p t) (star v * a * v) := by
  -- Star left conjugation preserves nonnegativity.
  have hvav : 0 ≤ star v * a * v := star_left_conjugate_nonneg ha v
  -- Both endpoints rewrite via the Mathlib transport identity.
  have htinv_nn : (0 : ℝ) ≤ t⁻¹ := inv_nonneg.mpr ht.le
  -- 0 ≤ t⁻¹ • a in A.
  have htinv_smul_a_nn : (0 : A) ≤ t⁻¹ • a := smul_nonneg htinv_nn ha
  -- t^(p - 1) > 0 from t > 0 alone (no constraint on p needed).
  have htp_pos : (0 : ℝ) < t ^ (p - 1) := Real.rpow_pos_of_pos ht (p - 1)
  -- Transport LHS endpoint a.
  have h_lhs_endpoint :
      cfcₙ (Real.rpowIntegrand₀₁ p t) a
        = t ^ (p - 1) • cfcₙ (Real.rpowIntegrand₀₁ p 1) (t⁻¹ • a) :=
    CFC.cfcₙ_rpowIntegrand₀₁_eq_cfcₙ_rpowIntegrand₀₁_one hp ht a ha
  -- Transport RHS endpoint star v * a * v.
  have h_rhs_endpoint :
      cfcₙ (Real.rpowIntegrand₀₁ p t) (star v * a * v)
        = t ^ (p - 1) • cfcₙ (Real.rpowIntegrand₀₁ p 1) (t⁻¹ • (star v * a * v)) :=
    CFC.cfcₙ_rpowIntegrand₀₁_eq_cfcₙ_rpowIntegrand₀₁_one hp ht (star v * a * v) hvav
  rw [h_lhs_endpoint, h_rhs_endpoint]
  -- Identify `cfcₙ (rpowIntegrand₀₁ p 1)` with `cfcₙ (fun x => 1 - (1+x)⁻¹)`.
  rw [cfcₙ_rpowIntegrand₀₁_one_eq (A := A) p (t⁻¹ • a)]
  rw [cfcₙ_rpowIntegrand₀₁_one_eq (A := A) p (t⁻¹ • (star v * a * v))]
  -- Re-express t⁻¹ • (star v * a * v) = star v * (t⁻¹ • a) * v.
  have h_smul_conj :
      t⁻¹ • (star v * a * v) = star v * (t⁻¹ • a) * v := by
    simp [smul_mul_assoc, mul_smul_comm]
  rw [h_smul_conj]
  -- Apply the helper at t⁻¹ • a (which is nonneg).
  have h_helper :
      star v * cfcₙ (fun x : ℝ => 1 - (1 + x)⁻¹) (t⁻¹ • a) * v
        ≤ cfcₙ (fun x : ℝ => 1 - (1 + x)⁻¹) (star v * (t⁻¹ • a) * v) :=
    star_mul_cfcₙ_one_sub_one_add_inv_mul_le htinv_smul_a_nn hv
  -- Distribute star v * (t^(p-1) • X) * v = t^(p-1) • (star v * X * v).
  have h_smul_conj_cfc :
      star v * (t ^ (p - 1) • cfcₙ (fun x : ℝ => 1 - (1 + x)⁻¹) (t⁻¹ • a)) * v
        = t ^ (p - 1) •
            (star v * cfcₙ (fun x : ℝ => 1 - (1 + x)⁻¹) (t⁻¹ • a) * v) := by
    rw [mul_smul_comm, smul_mul_assoc]
  rw [h_smul_conj_cfc]
  -- Now both sides are t^(p-1) • (...); apply scalar monotonicity.
  exact smul_le_smul_of_nonneg_left h_helper htp_pos.le

/-- **Integral Jensen for `nnrpow` on `p ∈ (0, 1)` (B6 L3 Sub-Part 5.3).**

For `p : ℝ≥0` with `(p : ℝ) ∈ (0, 1)`, `0 ≤ a` in a non-unital C⋆-algebra
`A` (with completeness), and `star (↑v : A⁺¹) * ↑v ≤ 1` in the
unitization, the Hansen-Pedersen Jensen inequality

```
star v * (a ^ p) * v ≤ (star v * a * v) ^ p
```

holds in the operator order.

The proof integrates the per-`t` integrand Jensen inequality (Sub-Part
5.2) against the measure `μ` provided by Mathlib's integral
representation `CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁`:
the integral representation rewrites both `a ^ p` and `(star v * a * v) ^ p`
as integrals of the per-`t` integrand, and the AE per-`t` inequality
is preserved under left- and right-multiplication by `star v` and `v`. -/
lemma CFC.star_mul_nnrpow_mul_le_nnrpow_star_mul_Ioo
    [CompleteSpace A] {p : ℝ≥0} (hp : (p : ℝ) ∈ Set.Ioo (0 : ℝ) 1)
    {a v : A} (ha : 0 ≤ a)
    (hv : star (v : Unitization ℂ A) * (v : Unitization ℂ A) ≤ 1) :
    star v * (a ^ p) * v ≤ (star v * a * v) ^ p := by
  -- The ℝ≥0-membership counterpart, for invoking the integral representation.
  have hp_nn : p ∈ Set.Ioo (0 : ℝ≥0) 1 := by exact_mod_cast hp
  -- Star left conjugation preserves nonnegativity.
  have hvav : 0 ≤ star v * a * v := star_left_conjugate_nonneg ha v
  -- Obtain the shared measure and per-element representations.
  obtain ⟨μ, hμ⟩ :=
    CFC.exists_measure_nnrpow_eq_integral_cfcₙ_rpowIntegrand₀₁ A hp_nn
  -- The integrand `t ↦ cfcₙ (rpowIntegrand₀₁ p t) ·` evaluated at each base.
  set F : ℝ → A := fun t => cfcₙ (Real.rpowIntegrand₀₁ p t) a
  set G : ℝ → A := fun t => cfcₙ (Real.rpowIntegrand₀₁ p t) (star v * a * v)
  -- Integrability of each integrand on `Ioi 0`.
  have hF_int : Integrable F (μ.restrict (Set.Ioi 0)) := (hμ a ha).1
  have hG_int : Integrable G (μ.restrict (Set.Ioi 0)) := (hμ (star v * a * v) hvav).1
  -- Integral representation of both endpoints.
  have hF_eq : a ^ p = ∫ t in Set.Ioi 0, F t ∂μ := (hμ a ha).2
  have hG_eq : (star v * a * v) ^ p = ∫ t in Set.Ioi 0, G t ∂μ :=
    (hμ (star v * a * v) hvav).2
  -- Multiplication-as-CLM operators for moving constants through the integral.
  let Lmul : A →L[ℝ] A := ContinuousLinearMap.mul ℝ A (star v)
  let Rmul : A →L[ℝ] A := (ContinuousLinearMap.mul ℝ A).flip v
  -- The composite `t ↦ star v * F t * v` agrees with `t ↦ Rmul (Lmul (F t))`.
  -- Integrability of the composite via two `integrable_comp` steps.
  have hLF_int : Integrable (fun t => star v * F t) (μ.restrict (Set.Ioi 0)) :=
    Lmul.integrable_comp hF_int
  have hLFR_int :
      Integrable (fun t => star v * F t * v) (μ.restrict (Set.Ioi 0)) :=
    Rmul.integrable_comp hLF_int
  -- Rewrite `a ^ p` and pull `star v * · * v` through the set-integral.
  rw [hF_eq, hG_eq]
  -- We transform the LHS step by step.
  have h_lhs_const_mul :
      ∫ t in Set.Ioi 0, star v * F t ∂μ
        = star v * ∫ t in Set.Ioi 0, F t ∂μ :=
    integral_const_mul_of_integrable hF_int (c := star v)
  have h_lhs_mul_const :
      ∫ t in Set.Ioi 0, star v * F t * v ∂μ
        = (∫ t in Set.Ioi 0, star v * F t ∂μ) * v :=
    integral_mul_const_of_integrable hLF_int (c := v)
  have h_lhs :
      star v * (∫ t in Set.Ioi 0, F t ∂μ) * v
        = ∫ t in Set.Ioi 0, star v * F t * v ∂μ := by
    rw [h_lhs_mul_const, h_lhs_const_mul]
  rw [h_lhs]
  -- Apply integral monotonicity: AE per-`t`, Sub-Part 5.2 dominates.
  refine integral_mono_ae hLFR_int hG_int ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  -- `ht : t ∈ Ioi 0`, i.e., `0 < t`. Apply Sub-Part 5.2.
  exact CFC.star_mul_cfcₙ_rpowIntegrand₀₁_mul_le hp ht ha hv

end ShiftedResolventJensenNonUnital

/-! ### Final assembly: Hansen-Pedersen Jensen for real exponents

We assemble the full Hansen-Pedersen Jensen inequality for real
exponents `p ∈ [0, 1]` by splitting on the position of `p` in `[0, 1]`:

* `p = 0` and `p = 1` are the endpoint cases (Sub-Part 5.4).
* `p ∈ (0, 1)` reduces to the NNReal version (Sub-Part 5.3) via
  `CFC.nnrpow_eq_rpow`.

The interior reduction uses the unital→unitization lift for the
sub-isometric hypothesis `star v * v ≤ 1`: in a unital C⋆-algebra,
`0 ≤ star v * v ≤ 1` implies `‖star v * v‖ ≤ 1`, hence
`(↑(star v * v) : A⁺¹) ∈ [0, 1]` via `Unitization.inr_mem_Icc_iff_norm_le`,
which then unfolds (using `inr_mul` and `inr_star`) to
`star (↑v) * ↑v ≤ 1` in `A⁺¹` — precisely the hypothesis Sub-Part 5.3
requires.

This closes **Part 5** of the B6 L3 carrier closure path: Hansen-Pedersen
Jensen is now formalized for the full real interval `[0, 1]`. -/

section RpowJensenFinal

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open scoped CStarAlgebra
open Unitization

/-- **Hansen-Pedersen Jensen inequality for real exponents (B6 L3 Sub-Part 5.5).**

For `0 ≤ a` and `star v * v ≤ 1` in a unital C⋆-algebra and `p ∈ [0, 1]`
(real), the Hansen-Pedersen Jensen inequality

```
star v * (a ^ p) * v ≤ (star v * a * v) ^ p
```

holds in the operator order.

This is the final assembly of B6 L3 Part 5. The proof splits on `p`:

* For `p = 0` or `p = 1`: invoke the endpoint cases
  `CFC.star_mul_rpow_mul_le_rpow_star_mul_zero` and
  `CFC.star_mul_rpow_mul_le_rpow_star_mul_one` (Sub-Part 5.4).
* For `p ∈ (0, 1)`: lift `p` to `p.toNNReal : ℝ≥0`, lift the hypothesis
  `hv : star v * v ≤ 1` to `star (↑v) * ↑v ≤ 1` in `A⁺¹` via
  `Unitization.inr_mem_Icc_iff_norm_le` (using `0 ≤ star v * v` and
  `‖star v * v‖ ≤ 1`), and invoke
  `CFC.star_mul_nnrpow_mul_le_nnrpow_star_mul_Ioo` (Sub-Part 5.3).
  Conversion between `a ^ (p.toNNReal)` and `a ^ p` uses
  `CFC.nnrpow_eq_rpow`. -/
theorem CFC.star_mul_rpow_mul_le_rpow_star_mul
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) {a v : A}
    (ha : 0 ≤ a) (hv : star v * v ≤ 1) :
    star v * (a ^ p) * v ≤ (star v * a * v) ^ p := by
  -- Star left conjugation preserves nonnegativity (used in the endpoint cases
  -- by the endpoint lemmas themselves; recorded here for completeness).
  -- Split on whether p is interior or boundary.
  rcases hp.1.lt_or_eq with hp_pos | hp_eq_zero
  · -- 0 < p
    rcases hp.2.lt_or_eq with hp_lt_one | hp_eq_one
    · -- 0 < p < 1: interior; reduce to Sub-Part 5.3 via NNReal lift.
      set p_nn : ℝ≥0 := p.toNNReal with hp_nn_def
      have hp_nn_coe : (p_nn : ℝ) = p := Real.coe_toNNReal p hp.1
      have hp_nn_pos_nnreal : (0 : ℝ≥0) < p_nn :=
        Real.toNNReal_pos.mpr hp_pos
      have hp_nn_Ioo : (p_nn : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
        rw [hp_nn_coe]; exact ⟨hp_pos, hp_lt_one⟩
      -- Lift hv to the unitization.
      have hstar_nn : (0 : A) ≤ star v * v := star_left_conjugate_nonneg
        (zero_le_one (α := A)) v |>.trans_eq (by rw [mul_one])
      have h_norm_le : ‖star v * v‖ ≤ 1 :=
        (CStarAlgebra.norm_le_one_iff_of_nonneg (star v * v) hstar_nn).mpr hv
      have h_inr_Icc : ((star v * v : A) : Unitization ℂ A) ∈ Set.Icc 0 1 :=
        CStarAlgebra.inr_mem_Icc_iff_norm_le.mpr ⟨hstar_nn, h_norm_le⟩
      have h_inr_le : ((star v * v : A) : Unitization ℂ A) ≤ 1 := h_inr_Icc.2
      -- Rewrite ↑(star v * v) = star ↑v * ↑v.
      have h_inr_mul_star :
          ((star v * v : A) : Unitization ℂ A)
            = star (v : Unitization ℂ A) * (v : Unitization ℂ A) := by
        rw [Unitization.inr_mul ℂ, Unitization.inr_star]
      rw [h_inr_mul_star] at h_inr_le
      -- Apply Sub-Part 5.3.
      have h53 :=
        CFC.star_mul_nnrpow_mul_le_nnrpow_star_mul_Ioo (A := A) hp_nn_Ioo ha h_inr_le
      -- Convert NNReal exponent back to real via nnrpow_eq_rpow.
      have h_rpow_a : a ^ (p_nn : ℝ) = a ^ p_nn := (CFC.nnrpow_eq_rpow hp_nn_pos_nnreal).symm
      have hvav : 0 ≤ star v * a * v := star_left_conjugate_nonneg ha v
      have h_rpow_vav : (star v * a * v) ^ (p_nn : ℝ) = (star v * a * v) ^ p_nn :=
        (CFC.nnrpow_eq_rpow hp_nn_pos_nnreal).symm
      rw [show p = (p_nn : ℝ) from hp_nn_coe.symm, h_rpow_a, h_rpow_vav]
      exact h53
    · -- p = 1
      subst hp_eq_one
      exact CFC.star_mul_rpow_mul_le_rpow_star_mul_one ha hv
  · -- p = 0
    subst hp_eq_zero
    exact CFC.star_mul_rpow_mul_le_rpow_star_mul_zero ha hv

end RpowJensenFinal

end LTFP.MathlibExt.MatrixAnalysis
