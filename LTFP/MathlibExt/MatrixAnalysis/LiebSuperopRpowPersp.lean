/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import LTFP.MathlibExt.MatrixAnalysis.LiebSuperopCStar
import LTFP.MathlibExt.MatrixAnalysis.CommuteRpow
import LTFP.MathlibExt.MatrixAnalysis.CStarRpowPerspective

/-!
# Operator rpow perspective on left/right superoperator pairs

This file specialises `CFC.rpowPerspective` (the abstract C⋆-algebra
rpow perspective, defined in `CStarRpowPerspective.lean`) to pairs
of left / right multiplication superoperators `LC A`, `RC B`
(constructed in `LiebSuperopCStar.lean`).

The main identity is the algebraic simplification

```
CFC.rpowPerspective p (LC A) (RC B) = LC (A ^ p) * RC (B ^ (1 - p)),
```

which we currently land for both `A` *strictly positive* (positive
definite) and `B` strictly positive.  The PSD-relaxation of `A`
requires an ε-regularization argument together with continuity of
`(·)^p` in the operator argument; this is deferred to a future round.

## Main results

* `LiebSuperop.commute_LC_rpow_RC_rpow` — powers of `LC A` and powers
  of `RC B` always commute in the C⋆-algebra `SuperAlg n`.
* `LiebSuperop.rpowPerspective_L_R_of_strictlyPositive` — the
  rpow-perspective simplification, valid when both `A` and `B` are
  strictly positive.
-/

@[expose] public section

open scoped NNReal MatrixOrder ComplexOrder
open CStarMatrix CFC

namespace LiebSuperop

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Powers of `LC A` and `RC B` commute -/

/-- Powers of `LC A` and powers of `RC B` always commute in the
C⋆-algebra `SuperAlg n`.

This is `Commute.cfc_nnreal` applied twice to `LC_RC_commute`. -/
lemma commute_LC_rpow_RC_rpow {A B : Matrix n n ℂ} (p q : ℝ) :
    Commute ((LC A) ^ p) ((RC B) ^ q) := by
  -- Step 1: from Commute (LC A) (RC B), get Commute (cfc (·^p) (LC A)) (RC B).
  have h1 : Commute (cfc (R := ℝ≥0) (fun x : ℝ≥0 => x ^ p) (LC A)) (RC B) :=
    (LC_RC_commute (n := n) A B).cfc_nnreal _
  -- Step 2: from h1.symm get Commute (RC B) (cfc (·^p) (LC A)), then cfc_nnreal
  -- gives Commute (cfc (·^q) (RC B)) (cfc (·^p) (LC A)).
  have h2 : Commute (cfc (R := ℝ≥0) (fun x : ℝ≥0 => x ^ q) (RC B))
                    (cfc (R := ℝ≥0) (fun x : ℝ≥0 => x ^ p) (LC A)) :=
    h1.symm.cfc_nnreal _
  -- Convert cfc back to ^ notation via rpow_def.
  show Commute ((LC A) ^ p) ((RC B) ^ q)
  rw [show ((LC A) ^ p : SuperAlg n)
        = cfc (R := ℝ≥0) (fun x : ℝ≥0 => x ^ p) (LC A)
        from CFC.rpow_def,
      show ((RC B) ^ q : SuperAlg n)
        = cfc (R := ℝ≥0) (fun x : ℝ≥0 => x ^ q) (RC B)
        from CFC.rpow_def]
  exact h2.symm

/-! ### Strict positivity of `LC A` when `A` is positive definite -/

/-- The left superoperator wrapper `LC` is strictly positive when the
underlying matrix `A` is positive definite (= strictly positive).

The proof routes through `Matrix.PosDef.kronecker`: the identity is
positive definite, so the Kronecker product `1 ⊗ₖ A = L A` is positive
definite, hence strictly positive; the strict positivity transports
through `ofMatrix`. -/
lemma LC_strictlyPositive {A : Matrix n n ℂ} (hA : IsStrictlyPositive A) :
    IsStrictlyPositive (LC A) := by
  have hAdef : A.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp hA
  have h1def : (1 : Matrix n n ℂ).PosDef := Matrix.PosDef.one
  have hLdef : (L A).PosDef := by
    unfold L
    exact h1def.kronecker hAdef
  have hL_sp : IsStrictlyPositive (L A) := hLdef.isStrictlyPositive
  refine ⟨ofMatrix_nonneg_of_nonneg (n := n) hL_sp.nonneg, ?_⟩
  exact (ofMatrix_isUnit_iff (n := n) (M := L A)).mpr hL_sp.isUnit

/-! ### The rpow perspective simplification (strictly positive case) -/

/-- For strictly positive (= positive definite) matrices `A` and
strictly positive `B`, the operator rpow perspective at exponent `p`
on the pair `(LC A, RC B)` simplifies to

```
CFC.rpowPerspective p (LC A) (RC B) = LC (A ^ p) * RC (B ^ (1 - p)).
```

This is the strictly-positive case of B6 L3 Sub-Part 7.3b's main
identity.  The PSD-relaxation of `A` requires ε-regularization and is
deferred to a future round. -/
lemma rpowPerspective_L_R_of_strictlyPositive
    {A B : Matrix n n ℂ}
    (hA : IsStrictlyPositive A) (hB : IsStrictlyPositive B)
    {p : ℝ} (hp : 0 ≤ p) :
    CFC.rpowPerspective p (LC A) (RC B) =
      LC (A ^ p) * RC (B ^ ((1 : ℝ) - p)) := by
  -- Strict positivity of the wrappers.
  have hLC_sp : IsStrictlyPositive (LC A) := LC_strictlyPositive (n := n) hA
  have hRC_sp : IsStrictlyPositive (RC B) := RC_strictlyPositive (n := n) hB
  -- A is PosDef, so PosSemidef; B is PD likewise.
  have hA_psd : A.PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp hA.nonneg
  have hB_psd : B.PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp hB.nonneg
  -- `RC B`-powers commute with `LC A`-powers.
  have hcomm : ∀ p q : ℝ, Commute ((LC A) ^ p) ((RC B) ^ q) :=
    fun p q => commute_LC_rpow_RC_rpow (n := n) (A := A) (B := B) p q
  -- Unfold `rpowPerspective`.
  show (RC B) ^ ((1 : ℝ) / 2) *
        (((RC B) ^ (-((1 : ℝ) / 2))) * (LC A) * ((RC B) ^ (-((1 : ℝ) / 2)))) ^ p *
       (RC B) ^ ((1 : ℝ) / 2) = LC (A ^ p) * RC (B ^ ((1 : ℝ) - p))
  -- Step 1: Simplify the middle factor.
  -- (RC B)^(-1/2) * LC A * (RC B)^(-1/2) = LC A * (RC B)^(-1).
  -- We use (RC B)^(-1/2) commutes with LC A (commute_LC_rpow_RC_rpow at p=1
  -- ... but LC A = (LC A)^1, hence we use commutation).
  have hcomm_LC_RChalf : Commute ((LC A) ^ (1 : ℝ)) ((RC B) ^ (-((1:ℝ)/2))) :=
    hcomm 1 (-((1:ℝ)/2))
  -- (LC A) ^ 1 = LC A (rpow_one).
  have hLC1 : ((LC A) ^ (1 : ℝ) : SuperAlg n) = LC A :=
    CFC.rpow_one (LC A) hLC_sp.nonneg
  rw [hLC1] at hcomm_LC_RChalf
  -- Conclude commutation of LC A with (RC B)^(-1/2).
  have hcomm' : Commute (LC A) ((RC B) ^ (-((1 : ℝ) / 2))) := hcomm_LC_RChalf
  -- Now: middle expression = (RC B)^(-1/2) * (LC A * (RC B)^(-1/2))
  --                        = (RC B)^(-1/2) * ((RC B)^(-1/2) * LC A)
  --                        = ((RC B)^(-1/2) * (RC B)^(-1/2)) * LC A
  --                        = (RC B)^(-1) * LC A   (rpow_add)
  --                        = LC A * (RC B)^(-1)   (commute)
  have hmid : (((RC B) ^ (-((1 : ℝ) / 2))) * (LC A) * ((RC B) ^ (-((1 : ℝ) / 2))))
            = (LC A) * ((RC B) ^ (-(1 : ℝ))) := by
    -- Pull (LC A) to the left via commutation, then merge powers.
    -- (RC B)^(-1/2) * LC A = LC A * (RC B)^(-1/2) (commute, taking symm).
    have h1 : (((RC B) ^ (-((1 : ℝ) / 2))) * (LC A) : SuperAlg n)
        = (LC A) * ((RC B) ^ (-((1 : ℝ) / 2))) := hcomm'.symm.eq
    rw [h1]
    -- Now: LC A * (RC B)^(-1/2) * (RC B)^(-1/2) = LC A * ((RC B)^(-1/2) * (RC B)^(-1/2))
    rw [mul_assoc]
    -- (RC B)^(-1/2) * (RC B)^(-1/2) = (RC B)^(-1/2 + -1/2) = (RC B)^(-1)
    rw [← CFC.rpow_add hRC_sp.isUnit]
    congr 1
    congr 1
    ring
  -- Apply hmid.
  rw [hmid]
  -- Step 2: ((LC A) * (RC B)^(-1))^p = (LC A)^p * ((RC B)^(-1))^p
  -- by commute_rpow_mul_of_strictlyPositive.
  -- We need LC A and (RC B)^(-1) strictly positive.
  have hRCneg1_sp : IsStrictlyPositive ((RC B) ^ (-(1 : ℝ))) := by
    refine ⟨CFC.rpow_nonneg, ?_⟩
    exact hRC_sp.isUnit.cfcRpow (-(1 : ℝ)) hRC_sp.nonneg
  have hcomm_LC_RCneg1' : Commute (LC A) ((RC B) ^ (-(1 : ℝ))) := by
    have := hcomm 1 (-1)
    rw [CFC.rpow_one (LC A) hLC_sp.nonneg] at this
    exact this
  rw [CFC.commute_rpow_mul_of_strictlyPositive hLC_sp hRCneg1_sp hcomm_LC_RCneg1' p]
  -- Step 3: Combine factors.
  -- Goal: (RC B)^(1/2) * ((LC A)^p * ((RC B)^(-1))^p) * (RC B)^(1/2) = LC(A^p) * RC(B^(1-p))
  -- ((RC B)^(-1))^p = (RC B)^(-p) by rpow_rpow.
  have hRC_pow_neg : (((RC B) ^ (-(1 : ℝ))) ^ p : SuperAlg n)
                   = (RC B) ^ (-p) := by
    rw [CFC.rpow_rpow (RC B) (-(1:ℝ)) p hRC_sp.isUnit (by norm_num : (-(1:ℝ)) ≠ 0)
        hRC_sp.nonneg]
    congr 1; ring
  rw [hRC_pow_neg]
  -- Move (LC A)^p commuting with (RC B) powers to assemble:
  -- (RC B)^(1/2) * (LC A)^p * (RC B)^(-p) * (RC B)^(1/2)
  --   = (LC A)^p * (RC B)^(1/2) * (RC B)^(-p) * (RC B)^(1/2)  (commute)
  --   = (LC A)^p * (RC B)^(1/2 + (-p) + 1/2)                   (rpow_add x 2)
  --   = (LC A)^p * (RC B)^(1 - p).
  have hcomm_LCp_RChalf : Commute ((LC A) ^ p) ((RC B) ^ ((1:ℝ)/2)) := hcomm p ((1:ℝ)/2)
  -- Step 3a: pull (LC A)^p out of the front via commutation.
  have hreass : ((RC B) ^ ((1 : ℝ) / 2) * ((LC A) ^ p * (RC B) ^ (-p)) * (RC B) ^ ((1 : ℝ) / 2)
        : SuperAlg n)
      = ((LC A) ^ p) * ((RC B) ^ ((1 : ℝ) / 2) * (RC B) ^ (-p) * (RC B) ^ ((1 : ℝ) / 2)) := by
    have h := hcomm_LCp_RChalf.symm.eq  -- (RC B)^(1/2) * (LC A)^p = (LC A)^p * (RC B)^(1/2)
    calc (RC B) ^ ((1 : ℝ) / 2) * ((LC A) ^ p * (RC B) ^ (-p)) * (RC B) ^ ((1 : ℝ) / 2)
        = ((RC B) ^ ((1 : ℝ) / 2) * (LC A) ^ p) * ((RC B) ^ (-p) * (RC B) ^ ((1 : ℝ) / 2)) := by
            simp only [mul_assoc]
      _ = ((LC A) ^ p * (RC B) ^ ((1 : ℝ) / 2)) * ((RC B) ^ (-p) * (RC B) ^ ((1 : ℝ) / 2)) := by
            rw [h]
      _ = ((LC A) ^ p) * ((RC B) ^ ((1 : ℝ) / 2) * (RC B) ^ (-p) * (RC B) ^ ((1 : ℝ) / 2)) := by
            simp only [mul_assoc]
  rw [hreass]
  -- Combine (RC B) powers: (1/2) + (-p) + (1/2) = 1 - p.
  have hRC_combine : ((RC B) ^ ((1 : ℝ) / 2) * (RC B) ^ (-p) * (RC B) ^ ((1 : ℝ) / 2)
      : SuperAlg n) = (RC B) ^ ((1 : ℝ) - p) := by
    rw [mul_assoc, ← CFC.rpow_add hRC_sp.isUnit,
        ← CFC.rpow_add hRC_sp.isUnit]
    congr 1; ring
  rw [hRC_combine]
  -- Now: (LC A)^p * (RC B)^(1-p) = LC(A^p) * RC(B^(1-p)).
  rw [LC_rpow hp hA_psd, RC_rpow_pos hB]

end LiebSuperop
