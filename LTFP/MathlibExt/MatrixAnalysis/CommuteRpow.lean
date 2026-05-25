/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

/-!
# Commuting-product real powers in a unital C⋆-algebra

This file proves the operator identity

```
(x * y) ^ p = x ^ p * y ^ p
```

for any real `p`, when `x` and `y` are commuting strictly positive
elements of a unital C⋆-algebra.  This is the algebraic core of the
simplification of the operator rpow perspective in B6 L3 Sub-Part 7.3.

## Main results

* `CFC.exp_rpow_eq_exp_smul` — for a selfadjoint element `a` and any
  real `p`, `(NormedSpace.exp a) ^ p = NormedSpace.exp (p • a)`.  This
  is the bridge from unital real powers (defined via the CFC on `ℝ≥0`)
  to `NormedSpace.exp` on a selfadjoint argument.
* `CFC.commute_rpow_mul_of_strictlyPositive` — for commuting strictly
  positive `x` and `y` and any real `p`, `(x * y) ^ p = x ^ p * y ^ p`.

## Proof strategy

**Strict-positive helper.**  For commuting strictly positive `x, y`,
both `log x` and `log y` are well-defined selfadjoints, and they
commute (via `Commute.cfc_real` applied twice to `Commute x y`).
Then `x * y = exp (log x) * exp (log y) = exp (log x + log y)` by
`NormedSpace.exp_add_of_commute`, and the result follows by raising
both sides to the `p`-th power using `CFC.exp_rpow_eq_exp_smul`.
-/

@[expose] public section

open NNReal NormedSpace

namespace CFC

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-! ### Powers of exponentials -/

/-- For a selfadjoint element `a` of a unital C⋆-algebra and any real
`p`, the `p`-th rpow of `exp a` equals `exp (p • a)`.

This is the algebraic bridge between unital real powers (defined via
the CFC on `ℝ≥0`) and `NormedSpace.exp` on a selfadjoint argument. -/
lemma exp_rpow_eq_exp_smul {a : A} (ha : IsSelfAdjoint a) (p : ℝ) :
    (exp a) ^ p = exp (p • a) := by
  -- Both sides reduce to `cfc` expressions on `a`.
  have hps : IsSelfAdjoint (p • a) := IsSelfAdjoint.smul (.all _) ha
  have hexp_eq : exp a = cfc Real.exp a := (real_exp_eq_normedSpace_exp ha).symm
  have hexp_nonneg : (0 : A) ≤ exp a := ha.exp_nonneg
  -- LHS: (exp a) ^ p = cfc (fun t : ℝ => t ^ p) (exp a) via `rpow_eq_cfc_real`.
  -- Then by cfc_comp on Real.exp, this becomes cfc ((·^p) ∘ Real.exp) a.
  rw [rpow_eq_cfc_real (a := exp a) hexp_nonneg]
  rw [hexp_eq]
  -- Continuity of (·^p) on Real.exp '' spectrum a (which is ⊆ (0, ∞)).
  have hg_cont : ContinuousOn (fun t : ℝ => t ^ p) (Real.exp '' spectrum ℝ a) := by
    intro x hx
    obtain ⟨s, _, rfl⟩ := hx
    exact (Real.continuousAt_rpow_const _ p (Or.inl (Real.exp_pos s).ne')).continuousWithinAt
  rw [← cfc_comp (g := fun t : ℝ => t ^ p) (f := Real.exp) (a := a) (hg := hg_cont)]
  -- RHS: exp (p • a) = cfc Real.exp (p • a) = cfc (Real.exp ∘ (p • ·)) a
  -- using cfc_smul_id and cfc_comp.
  rw [show exp (p • a) = cfc Real.exp (p • a) from
        (real_exp_eq_normedSpace_exp hps).symm]
  rw [show (p • a : A) = cfc (fun t : ℝ => p • t) a from
        (cfc_smul_id (R := ℝ) p a).symm]
  rw [← cfc_comp Real.exp (fun t : ℝ => p • t) a]
  -- Now both sides are `cfc f a` for some `f : ℝ → ℝ`; check pointwise equality
  refine cfc_congr fun s _ => ?_
  -- (Real.exp s) ^ p = Real.exp (p • s)
  show (Real.exp s) ^ p = Real.exp (p • s)
  rw [smul_eq_mul, Real.rpow_def_of_pos (Real.exp_pos s), Real.log_exp,
      mul_comm s p]

/-! ### Commuting-product rpow on strictly positive elements -/

/-- For commuting strictly positive elements `x, y` of a unital C⋆-algebra
and any real `p`, `(x * y) ^ p = x ^ p * y ^ p`.

The proof uses the bijection `exp ∘ log = id` on strictly positive
elements: writing `x = exp (log x)` and `y = exp (log y)` reduces the
product to `exp (log x + log y)` (using that `log x` and `log y`
commute), and then `exp_rpow_eq_exp_smul` distributes the `p`-th power
through the sum back into a product. -/
lemma commute_rpow_mul_of_strictlyPositive
    {x y : A} (hx : IsStrictlyPositive x) (hy : IsStrictlyPositive y)
    (hxy : Commute x y) (p : ℝ) :
    (x * y) ^ p = x ^ p * y ^ p := by
  -- Set up: log x and log y are both selfadjoint.
  have hlx_sa : IsSelfAdjoint (log x) := IsSelfAdjoint.log
  have hly_sa : IsSelfAdjoint (log y) := IsSelfAdjoint.log
  -- log x commutes with y (by Commute.cfc_real).
  have hlx_y : Commute (log x) y := hxy.cfc_real _
  -- log x commutes with log y: from hlx_y.symm get Commute y (log x),
  -- then cfc_real gives Commute (log y) (log x), then symm.
  have hly_lx : Commute (log y) (log x) := hlx_y.symm.cfc_real _
  have hlx_ly : Commute (log x) (log y) := hly_lx.symm
  -- For `exp_add_of_commute` we need a `NormedAlgebra ℚ A` instance.
  let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  -- x = exp (log x), y = exp (log y).
  have hex : x = exp (log x) := (exp_log x).symm
  have hey : y = exp (log y) := (exp_log y).symm
  -- x * y = exp (log x + log y) via Commute.exp_add.
  have hxy_eq : x * y = exp (log x + log y) := by
    rw [exp_add_of_commute hlx_ly]
    rw [← hex, ← hey]
  -- (x * y) ^ p = (exp (log x + log y)) ^ p
  rw [hxy_eq]
  rw [exp_rpow_eq_exp_smul (hlx_sa.add hly_sa) p]
  -- = exp (p • (log x + log y)) = exp (p • log x + p • log y)
  rw [smul_add]
  -- = exp (p • log x) * exp (p • log y) via Commute.exp_add.
  rw [exp_add_of_commute (hlx_ly.smul_left p |>.smul_right p)]
  -- Re-express as x ^ p * y ^ p using exp_rpow_eq_exp_smul backwards.
  rw [← exp_rpow_eq_exp_smul hlx_sa p, ← exp_rpow_eq_exp_smul hly_sa p]
  rw [← hex, ← hey]

end CFC
