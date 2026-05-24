/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Tactic.NoncommRing
import LTFP.MathlibExt.MatrixAnalysis.CStarShiftedResolventConcave

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

open scoped NNReal

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

end LTFP.MathlibExt.MatrixAnalysis
