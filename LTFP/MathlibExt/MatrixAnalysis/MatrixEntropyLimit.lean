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

/-! ## Closedness of `ConvexOn` (local helper)

Mathlib has `isClosed_concaveOn` only via the LTFP `CStarLogConcave.lean`
module (it is not in mainline Mathlib). The dual `isClosed_convexOn`
statement is not provided anywhere, so we add it here as a local
helper. The proof mirrors `isClosed_concaveOn`. -/

namespace EntropyLimit

section ConvexOnClosed

variable {E : Type*} {β : Type*}
variable [AddCommMonoid E] [Module ℝ E]
variable [TopologicalSpace β] [AddCommMonoid β] [Module ℝ β]
  [PartialOrder β] [OrderClosedTopology β]
  [ContinuousAdd β] [ContinuousConstSMul ℝ β]

/-- The set of functions convex on a fixed convex set `s` is closed
in the product (pointwise convergence) topology. Local dual of
`LTFP.MathlibExt.MatrixAnalysis.isClosed_concaveOn`. -/
theorem isClosed_convexOn {s : Set E} (hs : Convex ℝ s) :
    IsClosed {f : E → β | ConvexOn ℝ s f} := by
  simp only [isClosed_iff_clusterPt, clusterPt_principal_iff_frequently]
  intro g hg
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  have hmain (z) : Tendsto (fun f' : E → β => f' z) (𝓝 g) (𝓝 (g z)) :=
    continuousAt_apply z _
  have hlhs : Tendsto (fun f' : E → β => f' (a • x + b • y)) (𝓝 g)
      (𝓝 (g (a • x + b • y))) := hmain _
  have hrhs : Tendsto (fun f' : E → β => a • f' x + b • f' y) (𝓝 g)
      (𝓝 (a • g x + b • g y)) :=
    ((hmain x).const_smul a).add ((hmain y).const_smul b)
  refine le_of_tendsto_of_tendsto_of_frequently hlhs hrhs ?_
  refine hg.mono ?_
  intro f' hf'
  exact hf'.2 hx hy ha hb hab

end ConvexOnClosed

end EntropyLimit

/-! ## Main theorem — joint convexity of matrix relative entropy -/

/-- **Joint convexity of matrix relative entropy** (Lindblad form, with
linear shift).

For strictly positive complex matrices `A, B : Matrix n n ℂ`, the
shifted relative entropy

```
(A, B) ↦ Re Tr(A · log A - A · log B - A + B)
```

is jointly convex on the strictly-positive cone of pairs.

This is the matrix Bernstein chain Part 5b: assembling the
difference-quotient limit from Part 5a
(`tendsto_diff_quotient_to_relative_entropy`) with joint Lieb
concavity (`CFC.lieb_concavity_general` at `K = 1`,
`p = 1-ε`, `q = ε`) via the closed-limit-of-convex-functions argument
(local helper `isClosed_convexOn`).

The linear shift `- A + B` is irrelevant for convexity (linear terms
are both convex and concave), but it is the natural form that arises
when expressing the difference quotient at `ε = 0` and is the
canonical form of relative entropy in quantum information. -/
theorem matrix_relative_entropy_joint_convex
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] :
    ConvexOn ℝ
      {z : Matrix n n ℂ × Matrix n n ℂ |
        IsStrictlyPositive z.1 ∧ IsStrictlyPositive z.2}
      (fun z =>
        (Matrix.trace
            (z.1 * CFC.log z.1 - z.1 * CFC.log z.2 - z.1 + z.2)).re) := by
  classical
  -- The strictly-positive sub-domain.
  set s : Set (Matrix n n ℂ × Matrix n n ℂ) :=
    {z : Matrix n n ℂ × Matrix n n ℂ |
      IsStrictlyPositive z.1 ∧ IsStrictlyPositive z.2} with hs_def
  -- The PSD super-domain (where Lieb concavity lives).
  set t : Set (Matrix n n ℂ × Matrix n n ℂ) :=
    {z : Matrix n n ℂ × Matrix n n ℂ | z.1.PosSemidef ∧ z.2.PosSemidef} with ht_def
  -- Convexity of `s` and `t`, and inclusion.
  have hs_conv : Convex ℝ s := by
    have hSP := CFC.convex_setOf_isStrictlyPositive_matrix (n := n)
    have hprod := hSP.prod hSP
    convert hprod using 1
  have hst_sub : s ⊆ t := by
    rintro ⟨A, B⟩ ⟨hA, hB⟩
    exact ⟨Matrix.nonneg_iff_posSemidef.mp hA.nonneg,
           Matrix.nonneg_iff_posSemidef.mp hB.nonneg⟩
  -- Build the approximating family `F ε`. For ε > 0, define
  --   F ε z := ε⁻¹ * ((tr z.1).re - (tr (z.1^(1-ε) * z.2^ε)).re)
  --          + (tr z.2).re - (tr z.1).re
  let F : ℝ → Matrix n n ℂ × Matrix n n ℂ → ℝ := fun ε z =>
    ε⁻¹ *
      ((Matrix.trace z.1).re - (Matrix.trace (z.1 ^ ((1 : ℝ) - ε) * z.2 ^ ε)).re)
        + (Matrix.trace z.2).re - (Matrix.trace z.1).re
  -- The target functional, defined on all of `M × M`.
  let G : Matrix n n ℂ × Matrix n n ℂ → ℝ := fun z =>
    (Matrix.trace (z.1 * CFC.log z.1 - z.1 * CFC.log z.2 - z.1 + z.2)).re
  -- Step 1: each `F ε` (for ε ∈ (0, 1)) is convex on `s`.
  have h_F_convex : ∀ ε : ℝ, 0 < ε → ε < 1 → ConvexOn ℝ s (F ε) := by
    intro ε hε hε1
    -- Linear pieces: `(tr z.1).re` and `(tr z.2).re` are ℝ-linear in z.
    -- We use the LinearMap `Complex.reLm ∘ Matrix.traceLinearMap ∘ LinearMap.fst/snd`.
    let traceReLM_fst : Matrix n n ℂ × Matrix n n ℂ →ₗ[ℝ] ℝ :=
      (Complex.reLm.comp (Matrix.traceLinearMap n ℝ ℂ)).comp
        (LinearMap.fst ℝ (Matrix n n ℂ) (Matrix n n ℂ))
    let traceReLM_snd : Matrix n n ℂ × Matrix n n ℂ →ₗ[ℝ] ℝ :=
      (Complex.reLm.comp (Matrix.traceLinearMap n ℝ ℂ)).comp
        (LinearMap.snd ℝ (Matrix n n ℂ) (Matrix n n ℂ))
    have h_lin_fst : ∀ z, traceReLM_fst z = (Matrix.trace z.1).re := by
      intro z; rfl
    have h_lin_snd : ∀ z, traceReLM_snd z = (Matrix.trace z.2).re := by
      intro z; rfl
    have h_conv_fst : ConvexOn ℝ s (fun z => (Matrix.trace z.1).re) := by
      have := traceReLM_fst.convexOn hs_conv
      simpa [h_lin_fst] using this
    have h_conc_fst : ConcaveOn ℝ s (fun z => (Matrix.trace z.1).re) := by
      have := traceReLM_fst.concaveOn hs_conv
      simpa [h_lin_fst] using this
    have h_conv_snd : ConvexOn ℝ s (fun z => (Matrix.trace z.2).re) := by
      have := traceReLM_snd.convexOn hs_conv
      simpa [h_lin_snd] using this
    -- Lieb concavity at K = 1, p = 1-ε, q = ε.
    have hε' : (0 : ℝ) ≤ ε := le_of_lt hε
    have h1mε : (0 : ℝ) ≤ 1 - ε := by linarith
    have hpq : (1 - ε) + ε ≤ 1 := by linarith
    have h_lieb_t :
        ConcaveOn ℝ t
          (fun z : Matrix n n ℂ × Matrix n n ℂ =>
            (Matrix.trace
              (star (1 : Matrix n n ℂ) * (z.1 ^ ((1 : ℝ) - ε)) *
                (1 : Matrix n n ℂ) * (z.2 ^ ε))).re) :=
      CFC.lieb_concavity_general (n := n) (1 : Matrix n n ℂ) h1mε hε' hpq
    -- Drop the `star 1 * ... * 1` to plain `z.1^(1-ε) * z.2^ε`.
    have h_lieb_t' :
        ConcaveOn ℝ t
          (fun z : Matrix n n ℂ × Matrix n n ℂ =>
            (Matrix.trace (z.1 ^ ((1 : ℝ) - ε) * z.2 ^ ε)).re) := by
      refine h_lieb_t.congr ?_
      intro z _
      simp [star_one, one_mul, mul_one]
    -- Restrict from `t` to `s`.
    have h_lieb_s :
        ConcaveOn ℝ s
          (fun z : Matrix n n ℂ × Matrix n n ℂ =>
            (Matrix.trace (z.1 ^ ((1 : ℝ) - ε) * z.2 ^ ε)).re) :=
      h_lieb_t'.subset hst_sub hs_conv
    -- Now build `F ε` from these convexity ingredients.
    -- Step a: `ε⁻¹ * (tr z.1).re - ε⁻¹ * (tr (...)).re` is convex.
    have hεinv_nn : (0 : ℝ) ≤ ε⁻¹ := le_of_lt (inv_pos.mpr hε)
    -- The negated Lieb functional, scaled by ε⁻¹.
    have h_neg_lieb_s :
        ConvexOn ℝ s
          (fun z : Matrix n n ℂ × Matrix n n ℂ =>
            -(Matrix.trace (z.1 ^ ((1 : ℝ) - ε) * z.2 ^ ε)).re) :=
      h_lieb_s.neg
    have h_scaled_neg_lieb :
        ConvexOn ℝ s
          (fun z : Matrix n n ℂ × Matrix n n ℂ =>
            ε⁻¹ • -(Matrix.trace (z.1 ^ ((1 : ℝ) - ε) * z.2 ^ ε)).re) :=
      h_neg_lieb_s.smul hεinv_nn
    have h_scaled_fst :
        ConvexOn ℝ s
          (fun z : Matrix n n ℂ × Matrix n n ℂ =>
            ε⁻¹ • (Matrix.trace z.1).re) :=
      h_conv_fst.smul hεinv_nn
    -- Sum.
    have h_step1 :
        ConvexOn ℝ s
          (fun z : Matrix n n ℂ × Matrix n n ℂ =>
            ε⁻¹ • (Matrix.trace z.1).re +
            ε⁻¹ • -(Matrix.trace (z.1 ^ ((1 : ℝ) - ε) * z.2 ^ ε)).re) :=
      h_scaled_fst.add h_scaled_neg_lieb
    -- The linear shift `(tr z.2).re - (tr z.1).re` is convex (sum of linear + neg linear).
    have h_neg_fst :
        ConvexOn ℝ s (fun z : Matrix n n ℂ × Matrix n n ℂ =>
          -(Matrix.trace z.1).re) := by
      have h_aff : ConcaveOn ℝ s (fun z : Matrix n n ℂ × Matrix n n ℂ =>
          (Matrix.trace z.1).re) := h_conc_fst
      exact h_aff.neg
    have h_shift :
        ConvexOn ℝ s
          (fun z : Matrix n n ℂ × Matrix n n ℂ =>
            (Matrix.trace z.2).re + -(Matrix.trace z.1).re) :=
      h_conv_snd.add h_neg_fst
    have h_full :
        ConvexOn ℝ s
          (fun z : Matrix n n ℂ × Matrix n n ℂ =>
            (ε⁻¹ • (Matrix.trace z.1).re +
             ε⁻¹ • -(Matrix.trace (z.1 ^ ((1 : ℝ) - ε) * z.2 ^ ε)).re) +
            ((Matrix.trace z.2).re + -(Matrix.trace z.1).re)) :=
      h_step1.add h_shift
    -- Rewrite to match `F ε`.
    refine h_full.congr ?_
    intro z _
    show ε⁻¹ • (Matrix.trace z.1).re +
        ε⁻¹ • -(Matrix.trace (z.1 ^ ((1 : ℝ) - ε) * z.2 ^ ε)).re +
        ((Matrix.trace z.2).re + -(Matrix.trace z.1).re) = F ε z
    show _ = ε⁻¹ *
      ((Matrix.trace z.1).re - (Matrix.trace (z.1 ^ ((1 : ℝ) - ε) * z.2 ^ ε)).re)
        + (Matrix.trace z.2).re - (Matrix.trace z.1).re
    rw [smul_eq_mul, smul_eq_mul]; ring
  -- Step 2: pointwise convergence `F ε z → G z` for z ∈ s.
  have h_tendsto_at :
      ∀ z ∈ s, Filter.Tendsto (fun ε : ℝ => F ε z) (𝓝[>] (0 : ℝ)) (𝓝 (G z)) := by
    rintro ⟨A, B⟩ ⟨hA, hB⟩
    -- Part 5a gives the difference-quotient limit.
    have h5a := tendsto_diff_quotient_to_relative_entropy hA hB
    -- Add the constant shift `(tr B).re - (tr A).re`.
    have h_shift_tendsto :
        Filter.Tendsto
          (fun ε : ℝ => (Matrix.trace B).re - (Matrix.trace A).re)
          (𝓝[>] (0 : ℝ))
          (𝓝 ((Matrix.trace B).re - (Matrix.trace A).re)) :=
      tendsto_const_nhds
    have h_sum := h5a.add h_shift_tendsto
    -- Unfold both sides.
    have hG_val : G (A, B) =
        (Matrix.trace (A * CFC.log A - A * CFC.log B)).re +
          ((Matrix.trace B).re - (Matrix.trace A).re) := by
      show (Matrix.trace
        (A * CFC.log A - A * CFC.log B - A + B)).re = _
      rw [show A * CFC.log A - A * CFC.log B - A + B
            = (A * CFC.log A - A * CFC.log B) + (B - A) from by abel,
          Matrix.trace_add, Complex.add_re]
      simp [Matrix.trace_sub, Complex.sub_re]
    show Filter.Tendsto (fun ε : ℝ => F ε (A, B)) (𝓝[>] (0 : ℝ))
      (𝓝 (G (A, B)))
    rw [hG_val]
    -- The function `F ε (A, B)` is exactly the function in `h_sum`.
    show Filter.Tendsto
        (fun ε : ℝ => ε⁻¹ * ((Matrix.trace A).re
            - (Matrix.trace (A ^ ((1 : ℝ) - ε) * B ^ ε)).re)
              + (Matrix.trace B).re - (Matrix.trace A).re)
        (𝓝[>] (0 : ℝ))
        (𝓝 ((Matrix.trace (A * CFC.log A - A * CFC.log B)).re
              + ((Matrix.trace B).re - (Matrix.trace A).re)))
    have h_sum' : Filter.Tendsto
        (fun ε : ℝ => ε⁻¹ * ((Matrix.trace A).re
            - (Matrix.trace (A ^ ((1 : ℝ) - ε) * B ^ ε)).re)
              + ((Matrix.trace B).re - (Matrix.trace A).re))
        (𝓝[>] (0 : ℝ))
        (𝓝 ((Matrix.trace (A * CFC.log A - A * CFC.log B)).re
              + ((Matrix.trace B).re - (Matrix.trace A).re))) := h_sum
    refine h_sum'.congr ?_
    intro ε; ring
  -- Step 3: pass to the limit using `isClosed_convexOn`.
  -- We extend `F ε` and `G` to all of `M × M` by zero off `s`.
  let f_eps : ℝ → Matrix n n ℂ × Matrix n n ℂ → ℝ :=
    fun ε z => if z ∈ s then F ε z else 0
  let g_ext : Matrix n n ℂ × Matrix n n ℂ → ℝ :=
    fun z => if z ∈ s then G z else 0
  have hg_ext_eq : s.EqOn g_ext G := by
    intro z hz; simp [g_ext, hz]
  refine ConvexOn.congr ?_ hg_ext_eq
  -- Each `f_eps ε` is convex on `s` (for ε ∈ (0, 1)).
  have h_f_convex : ∀ ε : ℝ, 0 < ε → ε < 1 → ConvexOn ℝ s (f_eps ε) := by
    intro ε hε hε1
    refine (h_F_convex ε hε hε1).congr ?_
    intro z hz
    show F ε z = (if z ∈ s then F ε z else 0)
    simp [hz]
  -- Pointwise convergence of `f_eps ε → g_ext` as ε → 0⁺.
  have h_tendsto : Filter.Tendsto f_eps (𝓝[>] (0 : ℝ)) (𝓝 g_ext) := by
    rw [tendsto_pi_nhds]
    intro z
    by_cases hz : z ∈ s
    · have h_tn := h_tendsto_at z hz
      have hg_z : g_ext z = G z := by
        show (if z ∈ s then G z else 0) = G z
        simp [hz]
      rw [hg_z]
      refine h_tn.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε _hε
      show F ε z = (if z ∈ s then F ε z else 0)
      simp [hz]
    · have h_const : ∀ ε, f_eps ε z = 0 := by
        intro ε
        show (if z ∈ s then F ε z else 0) = 0
        simp [hz]
      have hg_z : g_ext z = 0 := by
        show (if z ∈ s then G z else 0) = 0
        simp [hz]
      rw [hg_z]
      simp only [h_const]
      exact tendsto_const_nhds
  -- Closedness of convexity.
  have h_closed :
      IsClosed {h : Matrix n n ℂ × Matrix n n ℂ → ℝ | ConvexOn ℝ s h} :=
    EntropyLimit.isClosed_convexOn (E := Matrix n n ℂ × Matrix n n ℂ) (β := ℝ)
      hs_conv
  -- Eventually, `f_eps ε` is convex (for ε ∈ (0, 1)).
  have h_eventually : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      f_eps ε ∈ {h : Matrix n n ℂ × Matrix n n ℂ → ℝ | ConvexOn ℝ s h} := by
    have h₁ : ∀ᶠ (ε : ℝ) in 𝓝[>] 0, 0 < ε ∧ ε < 1 :=
      nhdsGT_basis 0 |>.mem_of_mem zero_lt_one
    filter_upwards [h₁] with ε ⟨hε_pos, hε_lt⟩
    exact h_f_convex ε hε_pos hε_lt
  exact h_closed.mem_of_tendsto h_tendsto h_eventually

end Matrix
