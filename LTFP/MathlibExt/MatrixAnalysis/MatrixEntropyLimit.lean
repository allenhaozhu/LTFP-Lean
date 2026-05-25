/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Difference-quotient limit for matrix relative entropy

For strictly positive complex matrices `A, B : Matrix n n ℂ`, the
matrix-valued exponential family `ε ↦ A^(1-ε) · B^ε` interpolates from
`A^1 · B^0 = A · 1 = A` at `ε = 0` to `A^0 · B^1 = 1 · B = B` at
`ε = 1`. The first-order Taylor expansion at `ε = 0+` reads

  `A^(1-ε) · B^ε = A + ε · (A · log B - A · log A) + O(ε²)`,

so the trace difference quotient satisfies

  `(tr A - tr(A^(1-ε) · B^ε)) / ε  →  tr(A · log A - A · log B)`

as `ε → 0+`. The right-hand side is exactly the (real part of the)
matrix relative entropy `D(A ‖ B) := tr (A · (log A - log B))`.

## Strategy (Codex round 88, refined)

The clean algebraic identity:

```
A = A^(1-ε) · A^ε                       (rpow_add, A unit)
A - A^(1-ε) · B^ε = A^(1-ε) · (A^ε - B^ε)
ε⁻¹ • (A - A^(1-ε) · B^ε) = A^(1-ε) · (q A ε - q B ε)
```

where `q X ε := ε⁻¹ • (X^ε - 1)`. This factorisation needs no
commutation between `A` and `B`. Three limits then close the proof:

1. `q A ε → CFC.log A` as `ε → 0+`. We replicate the proof of
   Mathlib's `CFC.tendsto_cfc_rpow_sub_one_log` directly via
   `tendsto_cfc_fun` + `Real.tendstoLocallyUniformlyOn_rpow_sub_one_log`,
   which only need the `ContinuousFunctionalCalculus ℝ` instance on
   `Matrix n n ℂ` (auto-available) and avoid `CStarAlgebra`'s
   typeclass diamond on raw `Matrix n n ℂ`.

2. `q B ε → CFC.log B` analogously.

3. `A^(1-ε) → A` (from `A^ε → 1` and inverse-continuity).

Then `Continuous.matrix_trace` + `Complex.continuous_re` move the
limit to the scalar real expression.
-/
import LTFP.MathlibExt.MatrixAnalysis.LiebTraceComplementary
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import Mathlib.Analysis.SpecialFunctions.Log.RpowTendsto
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Instances.Matrix

namespace Matrix

open Filter
open scoped Topology Matrix.Norms.L2Operator MatrixOrder ComplexOrder

set_option maxHeartbeats 800000

/-! ## Helpers

We package the analytic content into three small helpers. -/

namespace EntropyLimit

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Direct matrix-level limit `(1/ε) • (X^ε - 1) → CFC.log X` as `ε → 0+`,
for a strictly positive matrix `X`. This is the Mathlib lemma
`CFC.tendsto_cfc_rpow_sub_one_log` re-proved at the matrix layer using
only `tendsto_cfc_fun` + `Real.tendstoLocallyUniformlyOn_rpow_sub_one_log`
(both available without `[CStarAlgebra (Matrix n n ℂ)]`). -/
lemma tendsto_q_log {X : Matrix n n ℂ} (hX : IsStrictlyPositive X) :
    Tendsto (fun ε : ℝ => ε⁻¹ • (X ^ ε - 1))
      (𝓝[>] (0 : ℝ)) (𝓝 (CFC.log X)) := by
  -- Step 1: positivity-of-spectrum.
  have hXnn : (0 : Matrix n n ℂ) ≤ X := hX.nonneg
  have hXsa : IsSelfAdjoint X := hX.isSelfAdjoint
  have hspec_pos : ∀ x ∈ spectrum ℝ X, 0 < x :=
    fun x hx => hX.spectrum_pos hx
  have hspec_sub : spectrum ℝ X ⊆ Set.Ioi (0 : ℝ) := fun x hx => hspec_pos x hx
  -- Step 2: get the cfc-level limit via tendsto_cfc_fun.
  have hcfc :
      Tendsto (fun p : ℝ => cfc (fun x : ℝ => p⁻¹ * (x ^ p - 1)) X)
        (𝓝[>] (0 : ℝ)) (𝓝 (CFC.log X)) := by
    -- Mirror the proof of CFC.tendsto_cfc_rpow_sub_one_log
    -- (Order.lean:39), reading the spectrum at ℝ.
    refine tendsto_cfc_fun ?tendsto ?cont
    case cont =>
      refine .of_forall fun p ↦ ?_
      -- Continuity of `x ↦ p⁻¹ * (x^p - 1)` on `spectrum ℝ X ⊆ (0, ∞)`.
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.sub _ continuousOn_const
      apply ContinuousOn.rpow_const continuousOn_id
      intro x hx
      exact Or.inl (hspec_pos x hx).ne'
    case tendsto =>
      have hmain :=
        Real.tendstoLocallyUniformlyOn_rpow_sub_one_log
      rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_Ioi] at hmain
      -- Specialize to the compact `spectrum ℝ X`.
      have hcompact : IsCompact (spectrum ℝ X) := spectrum.isCompact X
      exact hmain (spectrum ℝ X) hspec_sub hcompact
  -- Step 3: rewrite the goal LHS `ε⁻¹ • (X^ε - 1)` as
  -- `cfc (fun x => ε⁻¹ * (x^ε - 1)) X` via `cfc_smul`, `cfc_sub`,
  -- `cfc_const_one`, `rpow_eq_cfc_real`.
  refine hcfc.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  -- `(0 : ℝ) < ε`. The pointwise rewriting.
  -- ε⁻¹ • (X^ε - 1) = cfc (fun x => ε⁻¹ * (x^ε - 1)) X.
  have hcontrε : ContinuousOn (fun x : ℝ => x ^ ε) (spectrum ℝ X) := by
    apply ContinuousOn.rpow_const continuousOn_id
    intro x hx
    exact Or.inl (hspec_pos x hx).ne'
  have hcontrm1 : ContinuousOn (fun x : ℝ => x ^ ε - 1) (spectrum ℝ X) :=
    hcontrε.sub continuousOn_const
  -- The lhs we got from `tendsto_cfc_fun` is `cfc (fun x => ε⁻¹ * (x^ε - 1)) X`.
  -- We want `ε⁻¹ • (X^ε - 1)`. Use the standard cfc identities.
  -- Goal: (cfc (fun x => ε⁻¹ * (x^ε - 1)) X) = ε⁻¹ • (X^ε - 1).
  show cfc (fun x : ℝ => ε⁻¹ * (x ^ ε - 1)) X = ε⁻¹ • (X ^ ε - 1)
  -- Push `ε⁻¹ *` outside via `cfc_smul` (with `smul_eq_mul` for ℝ on ℝ).
  rw [show (fun x : ℝ => ε⁻¹ * (x ^ ε - 1)) = (fun x : ℝ => ε⁻¹ • (x ^ ε - 1)) from by
        funext x; rw [smul_eq_mul]]
  rw [cfc_smul (S := ℝ) ε⁻¹ (fun x : ℝ => x ^ ε - 1) X hcontrm1]
  rw [cfc_sub _ _ X hcontrε continuousOn_const]
  rw [cfc_const_one ℝ X]
  rw [CFC.rpow_eq_cfc_real (a := X) (y := ε) hXnn]

/-- `A^ε → 1` as `ε → 0+` for strictly positive `A`. -/
lemma tendsto_rpow_one {X : Matrix n n ℂ} (hX : IsStrictlyPositive X) :
    Tendsto (fun ε : ℝ => X ^ ε) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hq := tendsto_q_log hX
  have hε_zero : Tendsto (fun ε : ℝ => ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hsmul :
      Tendsto (fun ε : ℝ => ε • (ε⁻¹ • (X ^ ε - 1)))
        (𝓝[>] (0 : ℝ)) (𝓝 ((0 : ℝ) • CFC.log X)) :=
    hε_zero.smul hq
  rw [zero_smul] at hsmul
  have hsub :
      Tendsto (fun ε : ℝ => X ^ ε - 1)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : Matrix n n ℂ)) := by
    refine hsmul.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε_ne : (ε : ℝ) ≠ 0 := (show (0 : ℝ) < ε from hε).ne'
    rw [smul_smul, mul_inv_cancel₀ hε_ne, one_smul]
  have :
      Tendsto (fun ε : ℝ => (X ^ ε - 1) + 1)
        (𝓝[>] (0 : ℝ)) (𝓝 ((0 : Matrix n n ℂ) + 1)) :=
    hsub.add tendsto_const_nhds
  simpa [sub_add_cancel] using this

/-- `A^(1-ε) → A` as `ε → 0+` for strictly positive `A`. -/
lemma tendsto_rpow_front {X : Matrix n n ℂ} (hX : IsStrictlyPositive X) :
    Tendsto (fun ε : ℝ => X ^ ((1 : ℝ) - ε))
      (𝓝[>] (0 : ℝ)) (𝓝 X) := by
  have hXε := tendsto_rpow_one hX
  have hinv_cont : ContinuousAt (Ring.inverse : Matrix n n ℂ → Matrix n n ℂ)
      (1 : Matrix n n ℂ) := by
    have := NormedRing.inverse_continuousAt (R := Matrix n n ℂ) (1 : (Matrix n n ℂ)ˣ)
    simpa using this
  have h_inv :
      Tendsto (fun ε : ℝ => Ring.inverse (X ^ ε))
        (𝓝[>] (0 : ℝ)) (𝓝 (Ring.inverse (1 : Matrix n n ℂ))) :=
    hinv_cont.tendsto.comp hXε
  rw [Ring.inverse_one] at h_inv
  have h_mul :
      Tendsto (fun ε : ℝ => X * Ring.inverse (X ^ ε))
        (𝓝[>] (0 : ℝ)) (𝓝 (X * (1 : Matrix n n ℂ))) :=
    tendsto_const_nhds.mul h_inv
  rw [mul_one] at h_mul
  refine h_mul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε_pos : (0 : ℝ) < ε := hε
  have hXε_unit : IsUnit (X ^ ε) := (hX.rpow (y := ε)).isUnit
  have hsum : X ^ ((1 : ℝ) - ε) * X ^ ε = X := by
    rw [← CFC.rpow_add (a := X) (x := 1 - ε) (y := ε) hX.isUnit]
    rw [show (1 : ℝ) - ε + ε = 1 from by ring]
    exact CFC.rpow_one X hX.nonneg
  have hcalc : X ^ ((1 : ℝ) - ε) * X ^ ε * Ring.inverse (X ^ ε)
      = X * Ring.inverse (X ^ ε) := by
    rw [hsum]
  rw [mul_assoc, Ring.mul_inverse_cancel _ hXε_unit, mul_one] at hcalc
  exact hcalc.symm

/-- Key algebraic identity:

```
ε⁻¹ • (A - A^(1-ε) · B^ε) = A^(1-ε) · (q A ε - q B ε)
```

for `ε ≠ 0` and `A` a unit. -/
lemma diff_quotient_factor
    {A B : Matrix n n ℂ} (hA : IsStrictlyPositive A) {ε : ℝ} (_hε : ε ≠ 0) :
    ε⁻¹ • (A - A ^ ((1 : ℝ) - ε) * B ^ ε)
      = A ^ ((1 : ℝ) - ε) *
          (ε⁻¹ • (A ^ ε - 1) - ε⁻¹ • (B ^ ε - 1)) := by
  have hA_split : A = A ^ ((1 : ℝ) - ε) * A ^ ε := by
    rw [← CFC.rpow_add (a := A) (x := 1 - ε) (y := ε) hA.isUnit]
    rw [show (1 : ℝ) - ε + ε = 1 from by ring]
    exact (CFC.rpow_one A hA.nonneg).symm
  -- Rewrite via `show + rw` to target the bare `A` only.
  rw [show A - A ^ ((1 : ℝ) - ε) * B ^ ε
        = A ^ ((1 : ℝ) - ε) * A ^ ε - A ^ ((1 : ℝ) - ε) * B ^ ε from by
      rw [← hA_split]]
  rw [← mul_sub]
  rw [← mul_smul_comm]
  congr 1
  rw [show (A ^ ε - B ^ ε) = (A ^ ε - 1) - (B ^ ε - 1) from by abel]
  rw [smul_sub]

end EntropyLimit

/-! ## Main theorem -/

/-- **Difference-quotient limit for matrix relative entropy.**

For strictly positive complex matrices `A, B : Matrix n n ℂ`,

```
(1/ε) · (tr A - tr(A^(1-ε) · B^ε))  →  tr(A · log A - A · log B)
```

as `ε → 0+`. The limit value is the (real part of the) matrix relative
entropy `D(A ‖ B) = tr(A · (log A - log B))`.

This lemma is the analytic heart of the joint-convexity proof for
matrix relative entropy: combined with the closed-limit-of-convex
argument (Part 5b), it shows that
`(A, B) ↦ Re tr(A · log A - A · log B)` is convex on the
strictly-positive cone. -/
theorem tendsto_diff_quotient_to_relative_entropy
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A B : Matrix n n ℂ} (hA : IsStrictlyPositive A) (hB : IsStrictlyPositive B) :
    Filter.Tendsto
      (fun ε : ℝ =>
        ε⁻¹ *
          ((Matrix.trace A).re -
           (Matrix.trace (A ^ ((1 : ℝ) - ε) * B ^ ε)).re))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds
        ((Matrix.trace (A * CFC.log A - A * CFC.log B)).re)) := by
  -- Step 1: matrix-valued Tendsto.
  have hqA := EntropyLimit.tendsto_q_log hA
  have hqB := EntropyLimit.tendsto_q_log hB
  have hfront := EntropyLimit.tendsto_rpow_front hA
  have hqdiff := hqA.sub hqB
  have hmul := hfront.mul hqdiff
  -- Algebraic identity to recover the original difference quotient.
  have hmatrix :
      Tendsto (fun ε : ℝ => ε⁻¹ • (A - A ^ ((1 : ℝ) - ε) * B ^ ε))
        (𝓝[>] (0 : ℝ))
        (𝓝 (A * (CFC.log A - CFC.log B))) := by
    refine hmul.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε_pos : (0 : ℝ) < ε := hε
    exact (EntropyLimit.diff_quotient_factor (B := B) hA hε_pos.ne').symm
  have hrhs : A * (CFC.log A - CFC.log B) = A * CFC.log A - A * CFC.log B := by
    rw [mul_sub]
  rw [hrhs] at hmatrix
  -- Step 2: Apply `trace` and `.re`, both continuous.
  have htrace_cont : Continuous (fun M : Matrix n n ℂ => Matrix.trace M) :=
    Continuous.matrix_trace continuous_id
  have hre_cont : Continuous (fun z : ℂ => z.re) := Complex.continuous_re
  have hΦ : Continuous (fun M : Matrix n n ℂ => (Matrix.trace M).re) :=
    hre_cont.comp htrace_cont
  have htraceTendsto :
      Tendsto (fun ε : ℝ =>
          (Matrix.trace (ε⁻¹ • (A - A ^ ((1 : ℝ) - ε) * B ^ ε))).re)
        (𝓝[>] (0 : ℝ))
        (𝓝 ((Matrix.trace (A * CFC.log A - A * CFC.log B)).re)) :=
    (hΦ.tendsto _).comp hmatrix
  -- Step 3: pull the scalar `ε⁻¹` outside the trace.
  refine htraceTendsto.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε _hε
  rw [Matrix.trace_smul, Matrix.trace_sub, Complex.real_smul, Complex.mul_re]
  simp [Complex.sub_re, Complex.sub_im, mul_sub]

end Matrix
