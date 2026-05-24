/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.IntegralRepresentation
import Mathlib.Analysis.Convex.Function
import LTFP.MathlibExt.MatrixAnalysis.CStarShiftedResolventConcave

/-!
# Operator concavity of the rpow integrand

This file establishes operator concavity of the integrand used in Mathlib's
integral representation of `x ↦ x ^ p` for `p ∈ (0, 1)`:
```
Real.rpowIntegrand₀₁ p t x = t ^ p * (t⁻¹ - (t + x)⁻¹).
```

Concretely, we prove
```
CFC.concaveOn_cfcₙ_rpowIntegrand₀₁ :
    ConcaveOn ℝ (Set.Ici (0 : A)) (cfcₙ (Real.rpowIntegrand₀₁ p t))
```
for `p ∈ (0, 1)` and `t > 0`, where `A` is any non-unital C⋆-algebra.

## Proof strategy

We reduce to the shifted-resolvent concavity
`CFC.concaveOn_one_sub_one_add_inv_real` from
`LTFP/MathlibExt/MatrixAnalysis/CStarShiftedResolventConcave.lean`.

1. **`t = 1` reduction (`A.1`).** The scalar identity
   `rpowIntegrand₀₁ p 1 x = 1 - (1 + x)⁻¹` (after `1 ^ p = 1` and
   `1⁻¹ = 1`) lets us identify
   `cfcₙ (rpowIntegrand₀₁ p 1) a = cfcₙ (fun x => 1 - (1 + x)⁻¹) a`
   via `cfcₙ_congr`.

2. **Input scaling (`A.2`).** The map `a ↦ t⁻¹ • a` is `ℝ`-linear on `A`, and
   for `t > 0` its preimage of `Ici 0` contains `Ici 0`. Applying
   `ConcaveOn.comp_linearMap` to the result from step 1 yields concavity of
   `a ↦ cfcₙ (rpowIntegrand₀₁ p 1) (t⁻¹ • a)` on `Ici 0`.

3. **Output scaling (`A.3`).** The scalar `t ^ (p - 1)` is nonneg (in fact
   positive) for `t > 0`, so `ConcaveOn.smul` upgrades step 2's concavity to
   concavity of `a ↦ t ^ (p - 1) • cfcₙ (rpowIntegrand₀₁ p 1) (t⁻¹ • a)`.

4. **Transport back (`A.4`).** Mathlib's existing identity
   `CFC.cfcₙ_rpowIntegrand₀₁_eq_cfcₙ_rpowIntegrand₀₁_one`
   states
   `cfcₙ (rpowIntegrand₀₁ p t) a = t ^ (p - 1) • cfcₙ (rpowIntegrand₀₁ p 1) (t⁻¹ • a)`
   for `a ∈ Ici 0`. `ConcaveOn.congr` finishes.

## Downstream usage

This is the "piece A" of B6 L3 part 2 (Bach §1, rpow operator concavity from
the integral representation). Combined with linearity of the integral, it
yields operator concavity of `x ↦ x ^ p` on the positive cone for
`p ∈ (0, 1)`.
-/

@[expose] public section

namespace LTFP.MathlibExt.MatrixAnalysis

open scoped NonUnitalContinuousFunctionalCalculus CStarAlgebra
open Real Set

section RpowIntegrand

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

omit [PartialOrder A] [StarOrderedRing A] in
/-- **Step A.1.** Identify `cfcₙ (rpowIntegrand₀₁ p 1)` with the shifted
resolvent `cfcₙ (fun x => 1 - (1 + x)⁻¹)`. This is purely scalar: the
integrand simplifies to `1 - (1 + x)⁻¹` at `t = 1`. -/
lemma cfcₙ_rpowIntegrand₀₁_one_eq (p : ℝ) (a : A) :
    cfcₙ (Real.rpowIntegrand₀₁ p 1) a = cfcₙ (fun x : ℝ => 1 - (1 + x)⁻¹) a := by
  refine cfcₙ_congr ?_
  intro x _
  simp [Real.rpowIntegrand₀₁, Real.one_rpow]

/-- **Step A.2 + A.1 packaged.** Concavity of `a ↦ cfcₙ (rpowIntegrand₀₁ p 1) a`
on the positive cone, obtained directly from
`CFC.concaveOn_one_sub_one_add_inv_real` and `cfcₙ_rpowIntegrand₀₁_one_eq`. -/
lemma CFC.concaveOn_cfcₙ_rpowIntegrand₀₁_one (p : ℝ) :
    ConcaveOn ℝ (Set.Ici (0 : A)) (cfcₙ (Real.rpowIntegrand₀₁ p 1)) := by
  -- Use the t = 1 identification + the shifted-resolvent concavity.
  refine
    (CFC.concaveOn_one_sub_one_add_inv_real (A := A)).congr (fun a _ => ?_)
  exact (cfcₙ_rpowIntegrand₀₁_one_eq p a).symm

/-- **Step A: full statement.** Operator concavity of
`cfcₙ (Real.rpowIntegrand₀₁ p t)` on the positive cone, for `p ∈ (0, 1)` and
`t > 0`. -/
theorem CFC.concaveOn_cfcₙ_rpowIntegrand₀₁
    {p t : ℝ} (hp : p ∈ Set.Ioo (0 : ℝ) 1) (ht : 0 < t) :
    ConcaveOn ℝ (Set.Ici (0 : A)) (cfcₙ (Real.rpowIntegrand₀₁ p t)) := by
  -- The linear input-rescaling map `a ↦ t⁻¹ • a : A →ₗ[ℝ] A`.
  let g : A →ₗ[ℝ] A := (t⁻¹ : ℝ) • (LinearMap.id : A →ₗ[ℝ] A)
  have hg_apply : ∀ a : A, g a = t⁻¹ • a := fun a => by
    show ((t⁻¹ : ℝ) • (LinearMap.id : A →ₗ[ℝ] A)) a = t⁻¹ • a
    simp
  have htinv_pos : 0 < t⁻¹ := inv_pos.mpr ht
  -- Step A.1+A.2: concavity of `a ↦ cfcₙ (rpowIntegrand₀₁ p 1) a` on `Ici 0`.
  have h_one : ConcaveOn ℝ (Set.Ici (0 : A)) (cfcₙ (Real.rpowIntegrand₀₁ p 1)) :=
    CFC.concaveOn_cfcₙ_rpowIntegrand₀₁_one p
  -- Step A.3: precompose with `g` (linear), restricting to `Ici 0`.
  -- `ConcaveOn.comp_linearMap` lives on `g ⁻¹' (Ici 0)`, which contains
  -- `Ici 0` because `t⁻¹ > 0`.
  have h_preimg : Set.Ici (0 : A) ⊆ g ⁻¹' Set.Ici (0 : A) := by
    intro a (ha : 0 ≤ a)
    show (0 : A) ≤ g a
    rw [hg_apply]
    exact smul_nonneg htinv_pos.le ha
  have h_comp_full : ConcaveOn ℝ (g ⁻¹' Set.Ici (0 : A))
      ((cfcₙ (Real.rpowIntegrand₀₁ p 1)) ∘ g) :=
    h_one.comp_linearMap g
  have h_comp : ConcaveOn ℝ (Set.Ici (0 : A))
      (fun a => cfcₙ (Real.rpowIntegrand₀₁ p 1) (t⁻¹ • a)) := by
    have hsub := h_comp_full.subset h_preimg (convex_Ici (0 : A))
    -- (cfcₙ (rpowIntegrand₀₁ p 1)) ∘ g = fun a => cfcₙ (rpowIntegrand₀₁ p 1) (t⁻¹ • a)
    have hfun : ((cfcₙ (Real.rpowIntegrand₀₁ p 1)) ∘ g)
        = fun a : A => cfcₙ (Real.rpowIntegrand₀₁ p 1) (t⁻¹ • a) := by
      funext a; show cfcₙ _ (g a) = _; rw [hg_apply]
    rw [hfun] at hsub
    exact hsub
  -- Step A.4: smul by the nonneg scalar `t ^ (p - 1)`.
  have hpow_nn : (0 : ℝ) ≤ t ^ (p - 1) := Real.rpow_nonneg ht.le _
  have h_smul :
      ConcaveOn ℝ (Set.Ici (0 : A))
        (fun a => t ^ (p - 1) • cfcₙ (Real.rpowIntegrand₀₁ p 1) (t⁻¹ • a)) :=
    h_comp.smul hpow_nn
  -- Step A.5: transport back via Mathlib's CFC scaling identity.
  refine h_smul.congr ?_
  intro a (ha : 0 ≤ a)
  -- `cfcₙ (rpowIntegrand₀₁ p t) a = t^(p-1) • cfcₙ (rpowIntegrand₀₁ p 1) (t⁻¹ • a)`
  exact
    (CFC.cfcₙ_rpowIntegrand₀₁_eq_cfcₙ_rpowIntegrand₀₁_one hp ht a ha).symm

end RpowIntegrand

end LTFP.MathlibExt.MatrixAnalysis
