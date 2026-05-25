/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Log-concavity of the trace-exponential via the Lindblad–Legendre route

For a fixed Hermitian matrix `H : Matrix n n ℂ`, the functional

  `A ↦ log (Re tr (exp (H + CFC.log A)))`

is concave on the cone of strictly positive matrices `A`.

This is the **logarithmic form** of the Lieb–Tropp trace-exp concavity:
it derives from the Gibbs variational identity, joint convexity of
matrix relative entropy (Part 5), and the partial-supremum-of-jointly-
concave-is-concave principle (`ConcaveOn.partial_sSup_concave`).

It is the natural intermediate between the elementary log-superop
concavity and the full direct concavity of `A ↦ Re tr (exp (H + log A))`
(which requires DPI / operator data-processing arguments).

## Proof outline

Let `D := {P | IsStrictlyPositive P ∧ Re tr P = 1}` be the set of
density matrices. Define

  `g(P, A) := Re tr (P · H) + Re tr (P · log A) − Re tr (P · log P)`.

Then:

* `D` is convex (Step 1): strict-pos cone is convex, unit-trace is
  preserved under convex combinations.
* `g` is jointly concave on `D × strict-pos` (Step 3): rewrite as
  `g = ψ − φ` where `ψ` is jointly affine and `φ` is the (jointly
  convex) Klein-shifted relative entropy.
* For each strict-pos `A`, the section `P ↦ g(P, A)` over `P ∈ D` is
  bounded above by `log (Re tr (exp (H + log A)))` (Gibbs `≤`,
  Part 4), and achieves this bound with equality at the Gibbs state
  (Part 4 extension), so the sSup equals the log.
* Apply `ConcaveOn.partial_sSup_concave`.

## Main result

* `Matrix.log_re_trace_exp_log_concave` — log-concavity of
  `A ↦ Real.log (Re tr (exp (H + CFC.log A)))` on strict-positive
  matrices.
-/
import LTFP.MathlibExt.Analysis.ConcaveOnPartialSup
import LTFP.MathlibExt.MatrixAnalysis.LiebTraceComplementary
import LTFP.MathlibExt.MatrixAnalysis.MatrixEntropyLimit
import LTFP.MathlibExt.MatrixAnalysis.MatrixExpPositivity
import LTFP.MathlibExt.MatrixAnalysis.MatrixRelEntropy

namespace Matrix

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

/-- **Log-concavity of `A ↦ Re log tr exp (H + log A)` on the strict-positive cone.**

For any Hermitian `H : Matrix n n ℂ`, the functional

  `A ↦ Real.log (Re tr (NormedSpace.exp (H + CFC.log A)))`

is concave on the convex cone `{A | IsStrictlyPositive A}`.

This is derived from:
* the Gibbs variational identity (Part 4: `gibbs_variational_inequality`
  and `gibbs_variational_equality`),
* joint convexity of matrix relative entropy (Part 5b:
  `matrix_relative_entropy_joint_convex`),
* the partial-supremum-of-jointly-concave-is-concave principle
  (`ConcaveOn.partial_sSup_concave`).

The full Lieb–Tropp direct concavity of
`A ↦ Re tr (exp (H + CFC.log A))` is *not* derived here — it requires
the DPI route. This log-form is the natural intermediate consequence
of the Lindblad–Legendre bridge already in the library. -/
theorem log_re_trace_exp_log_concave
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) :
    ConcaveOn ℝ
      {A : Matrix n n ℂ | IsStrictlyPositive A}
      (fun A => Real.log (Matrix.trace (NormedSpace.exp (H + CFC.log A) :
        Matrix n n ℂ)).re) := by
  classical
  -- The strict-positive cone.
  set SP : Set (Matrix n n ℂ) := {A : Matrix n n ℂ | IsStrictlyPositive A}
    with hSP_def
  -- The density-matrix set.
  set D : Set (Matrix n n ℂ) :=
    {P : Matrix n n ℂ | IsStrictlyPositive P ∧ (Matrix.trace P).re = 1}
    with hD_def
  -- The strict-pos × strict-pos product (where Part 5 lives).
  set SP2 : Set (Matrix n n ℂ × Matrix n n ℂ) :=
    {z : Matrix n n ℂ × Matrix n n ℂ |
      IsStrictlyPositive z.1 ∧ IsStrictlyPositive z.2}
    with hSP2_def
  -- The variational integrand.
  let g : Matrix n n ℂ × Matrix n n ℂ → ℝ := fun z =>
    (Matrix.trace (z.1 * H)).re +
      (Matrix.trace (z.1 * CFC.log z.2)).re -
      (Matrix.trace (z.1 * CFC.log z.1)).re
  -- ───────────────────────────────────────────────────────────────
  -- Step 1. Convexity of `D`.
  -- ───────────────────────────────────────────────────────────────
  have hSP_conv : Convex ℝ SP := CFC.convex_setOf_isStrictlyPositive_matrix
  have hD_conv : Convex ℝ D := by
    intro P₁ hP₁ P₂ hP₂ a b ha hb hab
    refine ⟨?_, ?_⟩
    · -- strict-positivity preserved.
      exact hSP_conv hP₁.1 hP₂.1 ha hb hab
    · -- unit trace preserved (real-linearity of `(trace _).re`).
      have h1 : (Matrix.trace P₁).re = 1 := hP₁.2
      have h2 : (Matrix.trace P₂).re = 1 := hP₂.2
      have : (Matrix.trace (a • P₁ + b • P₂ : Matrix n n ℂ)).re = a + b := by
        rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul]
        -- `(a • z + b • w).re = a*z.re + b*w.re`.
        show ((a : ℂ) * Matrix.trace P₁ + (b : ℂ) * Matrix.trace P₂).re = a + b
        rw [Complex.add_re, Complex.mul_re, Complex.mul_re,
            Complex.ofReal_re, Complex.ofReal_im,
            Complex.ofReal_re, Complex.ofReal_im]
        simp [h1, h2]
      rw [this]; linarith
  -- ───────────────────────────────────────────────────────────────
  -- Step 1b. `D ⊆ SP` and `D × SP ⊆ SP × SP`.
  -- ───────────────────────────────────────────────────────────────
  have hD_sub_SP : D ⊆ SP := fun P hP => hP.1
  have hDSP_sub_SP2 : D ×ˢ SP ⊆ SP2 := by
    rintro ⟨P, A⟩ ⟨hP, hA⟩
    exact ⟨hP.1, hA⟩
  -- `D × SP` is convex (product of convex sets).
  have hDSP_conv : Convex ℝ (D ×ˢ SP) := hD_conv.prod hSP_conv
  -- ───────────────────────────────────────────────────────────────
  -- Step 2/3. Joint concavity of `g` on `D × SP`.
  --
  -- Decomposition:  g = ψ − φ  where
  --   ψ(P, A) := Re tr(P·H) − Re tr(P) + Re tr(A)            (jointly affine)
  --   φ(P, A) := Re tr(P·log P − P·log A − P + A)            (Part 5b joint convex)
  -- ───────────────────────────────────────────────────────────────
  -- Part 5b gives joint convexity of `φ` on `SP × SP`. Restrict to `D × SP`.
  have hφ_SP2 :
      ConvexOn ℝ SP2
        (fun z : Matrix n n ℂ × Matrix n n ℂ =>
          (Matrix.trace (z.1 * CFC.log z.1 - z.1 * CFC.log z.2 - z.1 + z.2)).re) :=
    matrix_relative_entropy_joint_convex (n := n)
  have hφ_DSP :
      ConvexOn ℝ (D ×ˢ SP)
        (fun z : Matrix n n ℂ × Matrix n n ℂ =>
          (Matrix.trace (z.1 * CFC.log z.1 - z.1 * CFC.log z.2 - z.1 + z.2)).re) :=
    hφ_SP2.subset hDSP_sub_SP2 hDSP_conv
  -- The negation `-φ` is jointly concave.
  have hnegφ_DSP :
      ConcaveOn ℝ (D ×ˢ SP)
        (fun z : Matrix n n ℂ × Matrix n n ℂ =>
          -(Matrix.trace (z.1 * CFC.log z.1 - z.1 * CFC.log z.2 - z.1 + z.2)).re) :=
    hφ_DSP.neg
  -- The affine part `ψ(P, A) = Re tr(P·H) − Re tr(P) + Re tr(A)`.
  -- Build it from real-linear maps.
  let traceMulH_LM : Matrix n n ℂ × Matrix n n ℂ →ₗ[ℝ] ℝ :=
    (Complex.reLm.comp (Matrix.traceLinearMap n ℝ ℂ)).comp
      ({  toFun := fun z => z.1 * H
          map_add' := by intros; simp [add_mul]
          map_smul' := by intros; simp } :
        Matrix n n ℂ × Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)
  let tracefst_LM : Matrix n n ℂ × Matrix n n ℂ →ₗ[ℝ] ℝ :=
    (Complex.reLm.comp (Matrix.traceLinearMap n ℝ ℂ)).comp
      (LinearMap.fst ℝ (Matrix n n ℂ) (Matrix n n ℂ))
  let tracesnd_LM : Matrix n n ℂ × Matrix n n ℂ →ₗ[ℝ] ℝ :=
    (Complex.reLm.comp (Matrix.traceLinearMap n ℝ ℂ)).comp
      (LinearMap.snd ℝ (Matrix n n ℂ) (Matrix n n ℂ))
  have h_traceMulH_eq : ∀ z : Matrix n n ℂ × Matrix n n ℂ,
      traceMulH_LM z = (Matrix.trace (z.1 * H)).re := by
    intro z; rfl
  have h_tracefst_eq : ∀ z : Matrix n n ℂ × Matrix n n ℂ,
      tracefst_LM z = (Matrix.trace z.1).re := by
    intro z; rfl
  have h_tracesnd_eq : ∀ z : Matrix n n ℂ × Matrix n n ℂ,
      tracesnd_LM z = (Matrix.trace z.2).re := by
    intro z; rfl
  -- ψ is concave (linear maps are both convex and concave on convex sets).
  have hψ_DSP :
      ConcaveOn ℝ (D ×ˢ SP)
        (fun z : Matrix n n ℂ × Matrix n n ℂ =>
          (Matrix.trace (z.1 * H)).re - (Matrix.trace z.1).re +
            (Matrix.trace z.2).re) := by
    have h1 : ConcaveOn ℝ (D ×ˢ SP)
        (fun z : Matrix n n ℂ × Matrix n n ℂ => (Matrix.trace (z.1 * H)).re) := by
      have := traceMulH_LM.concaveOn hDSP_conv
      simpa [h_traceMulH_eq] using this
    have h2 : ConvexOn ℝ (D ×ˢ SP)
        (fun z : Matrix n n ℂ × Matrix n n ℂ => (Matrix.trace z.1).re) := by
      have := tracefst_LM.convexOn hDSP_conv
      simpa [h_tracefst_eq] using this
    have h3 : ConcaveOn ℝ (D ×ˢ SP)
        (fun z : Matrix n n ℂ × Matrix n n ℂ => (Matrix.trace z.2).re) := by
      have := tracesnd_LM.concaveOn hDSP_conv
      simpa [h_tracesnd_eq] using this
    -- `concave + (- convex) + concave`.
    have h12 : ConcaveOn ℝ (D ×ˢ SP)
        (fun z : Matrix n n ℂ × Matrix n n ℂ =>
          (Matrix.trace (z.1 * H)).re - (Matrix.trace z.1).re) :=
      h1.sub h2
    exact h12.add h3
  -- Combine ψ + (-φ) to get joint concavity of g.
  -- Need to identify `ψ + (-φ) = g` pointwise on `D × SP`.
  have hg_eq_psum :
      ∀ z ∈ D ×ˢ SP,
        ((Matrix.trace (z.1 * H)).re - (Matrix.trace z.1).re +
            (Matrix.trace z.2).re) +
        (-(Matrix.trace (z.1 * CFC.log z.1 - z.1 * CFC.log z.2 - z.1 + z.2)).re) =
          g z := by
    intro z _
    -- Expand the trace difference into the four pieces.
    have hexpand :
        (Matrix.trace (z.1 * CFC.log z.1 - z.1 * CFC.log z.2 - z.1 + z.2)).re
          = (Matrix.trace (z.1 * CFC.log z.1)).re -
              (Matrix.trace (z.1 * CFC.log z.2)).re -
              (Matrix.trace z.1).re + (Matrix.trace z.2).re := by
      simp [Matrix.trace_sub, Matrix.trace_add, Complex.sub_re, Complex.add_re]
    show ((Matrix.trace (z.1 * H)).re - (Matrix.trace z.1).re +
            (Matrix.trace z.2).re) +
          (-(Matrix.trace
                (z.1 * CFC.log z.1 - z.1 * CFC.log z.2 - z.1 + z.2)).re) = g z
    rw [hexpand]
    show ((Matrix.trace (z.1 * H)).re - (Matrix.trace z.1).re +
            (Matrix.trace z.2).re) +
          (-((Matrix.trace (z.1 * CFC.log z.1)).re -
              (Matrix.trace (z.1 * CFC.log z.2)).re -
              (Matrix.trace z.1).re + (Matrix.trace z.2).re)) =
        (Matrix.trace (z.1 * H)).re +
          (Matrix.trace (z.1 * CFC.log z.2)).re -
          (Matrix.trace (z.1 * CFC.log z.1)).re
    ring
  have hg_concave_DSP : ConcaveOn ℝ (D ×ˢ SP) g := by
    have hsum :
        ConcaveOn ℝ (D ×ˢ SP)
          (fun z => ((Matrix.trace (z.1 * H)).re - (Matrix.trace z.1).re +
              (Matrix.trace z.2).re) +
            (-(Matrix.trace
                  (z.1 * CFC.log z.1 - z.1 * CFC.log z.2 - z.1 + z.2)).re)) :=
      hψ_DSP.add hnegφ_DSP
    exact hsum.congr hg_eq_psum
  -- ───────────────────────────────────────────────────────────────
  -- Step 4. Boundedness of each section by `log Re tr exp (H + log A)`.
  --
  -- For each strict-pos A, the section of `g(·, A)` over `D` is
  -- bounded above by Gibbs (≤) and attains the bound (=).
  -- ───────────────────────────────────────────────────────────────
  -- Hermiticity of `H + CFC.log A` for strict-pos `A`.
  have hlogA_sa : ∀ A : Matrix n n ℂ, IsSelfAdjoint (CFC.log A) :=
    fun A => IsSelfAdjoint.log
  have hH_sa : IsSelfAdjoint H := hH
  have hHlog_herm : ∀ {A : Matrix n n ℂ}, IsStrictlyPositive A →
      (H + CFC.log A).IsHermitian := by
    intro A _
    -- IsSelfAdjoint H + IsSelfAdjoint (log A) → IsSelfAdjoint (sum) → IsHermitian.
    have hsa : IsSelfAdjoint (H + CFC.log A) := hH_sa.add (hlogA_sa A)
    exact hsa
  -- Upper bound on each section.
  have hg_le_log : ∀ A ∈ SP, ∀ P ∈ D,
      g (P, A) ≤ Real.log (Matrix.trace
        (NormedSpace.exp (H + CFC.log A) : Matrix n n ℂ)).re := by
    intro A hA P hP
    have hHlogA : (H + CFC.log A).IsHermitian := hHlog_herm hA
    have hgibbs := gibbs_variational_inequality (n := n)
      (H := H + CFC.log A) hHlogA hP.1 hP.2
    -- hgibbs : (tr (P * (H + log A))).re - (tr (P * log P)).re ≤ log (...).
    -- Expand `P * (H + log A) = PstarH + Pstarlog A`.
    have htr_expand :
        (Matrix.trace (P * (H + CFC.log A))).re
          = (Matrix.trace (P * H)).re + (Matrix.trace (P * CFC.log A)).re := by
      rw [mul_add, Matrix.trace_add, Complex.add_re]
    rw [htr_expand] at hgibbs
    -- g(P,A) = Re tr(P·H) + Re tr(P·log A) - Re tr(P·log P)
    --       = (Re tr(P·H) + Re tr(P·log A)) - Re tr(P·log P) ≤ log(...).
    show (Matrix.trace (P * H)).re + (Matrix.trace (P * CFC.log A)).re -
      (Matrix.trace (P * CFC.log P)).re ≤ _
    linarith
  -- Attainment.
  have hg_eq_log_exists : ∀ A ∈ SP,
      ∃ P ∈ D, g (P, A) = Real.log (Matrix.trace
        (NormedSpace.exp (H + CFC.log A) : Matrix n n ℂ)).re := by
    intro A hA
    have hHlogA : (H + CFC.log A).IsHermitian := hHlog_herm hA
    obtain ⟨P, hP_sp, hPtrace, hP_eq⟩ :=
      gibbs_variational_equality (n := n) (H := H + CFC.log A) hHlogA
    refine ⟨P, ⟨hP_sp, hPtrace⟩, ?_⟩
    -- Same expansion as above; reverse direction.
    have htr_expand :
        (Matrix.trace (P * (H + CFC.log A))).re
          = (Matrix.trace (P * H)).re + (Matrix.trace (P * CFC.log A)).re := by
      rw [mul_add, Matrix.trace_add, Complex.add_re]
    rw [htr_expand] at hP_eq
    show (Matrix.trace (P * H)).re + (Matrix.trace (P * CFC.log A)).re -
      (Matrix.trace (P * CFC.log P)).re = _
    linarith
  -- ───────────────────────────────────────────────────────────────
  -- Step 5. Identify sSup with log Re tr exp(H + log A) and apply
  --   the partial-sSup-of-jointly-concave lemma.
  -- ───────────────────────────────────────────────────────────────
  -- `D` is nonempty: the maximally-mixed state `(card n)⁻¹ • 1` is in `D`.
  have h_card_pos : (0 : ℝ) < (Fintype.card n : ℝ) := by
    have hne : 0 < Fintype.card n := Fintype.card_pos
    exact_mod_cast hne
  have h_card_ne : (Fintype.card n : ℝ) ≠ 0 := ne_of_gt h_card_pos
  have h_card_inv_pos : (0 : ℝ) < ((Fintype.card n : ℝ))⁻¹ := inv_pos.mpr h_card_pos
  set P₀ : Matrix n n ℂ :=
    ((Fintype.card n : ℝ))⁻¹ • (1 : Matrix n n ℂ) with hP₀_def
  have hP₀_sp : IsStrictlyPositive P₀ :=
    isStrictlyPositive_one.smul h_card_inv_pos
  have hP₀_trace : (Matrix.trace P₀).re = 1 := by
    rw [hP₀_def, Matrix.trace_smul, Matrix.trace_one, Complex.real_smul,
        Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    have hcast : (((Fintype.card n : ℕ) : ℂ)).re = (Fintype.card n : ℝ) := by rfl
    have hcastim : (((Fintype.card n : ℕ) : ℂ)).im = 0 := by rfl
    rw [hcast, hcastim]
    -- Goal here: `(card n)⁻¹ * (card n) - (card n)⁻¹ * 0 = 1` (post-rw).
    have hinv := inv_mul_cancel₀ h_card_ne
    field_simp
    linarith [hinv]
  have hD_ne : D.Nonempty := ⟨P₀, hP₀_sp, hP₀_trace⟩
  -- Boundedness above of each section.
  have hbdd : ∀ A ∈ SP, BddAbove ((fun P : Matrix n n ℂ => g (P, A)) '' D) := by
    intro A hA
    refine ⟨Real.log (Matrix.trace
      (NormedSpace.exp (H + CFC.log A) : Matrix n n ℂ)).re, ?_⟩
    rintro v ⟨P, hP, rfl⟩
    exact hg_le_log A hA P hP
  -- Apply the partial-sSup-of-jointly-concave lemma.
  have h_partial :=
    ConcaveOn.partial_sSup_concave (T := D) (S := SP) (f := g)
      hg_concave_DSP hD_conv hSP_conv hD_ne hbdd
  -- Identify the sSup with the log.
  have h_sSup_eq : ∀ A ∈ SP,
      sSup ((fun P : Matrix n n ℂ => g (P, A)) '' D) =
      Real.log (Matrix.trace
        (NormedSpace.exp (H + CFC.log A) : Matrix n n ℂ)).re := by
    intro A hA
    -- The value is achieved (Gibbs `=`) and is an upper bound (Gibbs `≤`).
    -- So it equals `sSup`.
    obtain ⟨Pstar, hPstar_mem, hPstar_eq⟩ := hg_eq_log_exists A hA
    refine le_antisymm ?_ ?_
    · -- `sSup ≤ log Z`.
      apply csSup_le
      · -- Nonempty image.
        exact ⟨g (Pstar, A), Pstar, hPstar_mem, rfl⟩
      · rintro v ⟨P, hP, rfl⟩
        exact hg_le_log A hA P hP
    · -- `log Z ≤ sSup`.
      have : g (Pstar, A) ∈ (fun P : Matrix n n ℂ => g (P, A)) '' D :=
        ⟨Pstar, hPstar_mem, rfl⟩
      have hbdd' := hbdd A hA
      have := le_csSup hbdd' this
      linarith [hPstar_eq, this]
  -- Final concavity, via `ConcaveOn.congr`.
  refine h_partial.congr ?_
  intro A hA
  exact h_sSup_eq A hA

/-! ### Lieb–Tropp partial victory: concavity on the commuting-with-`H` slice -/

/-- **Lieb–Tropp on the commuting-with-`H` slice.**

For a fixed Hermitian `H : Matrix n n ℂ`, the trace-exp functional

  `A ↦ (Matrix.trace (NormedSpace.exp (H + CFC.log A))).re`

is concave on the convex slice of strictly positive matrices that
*commute* with `H`:

  `{ A | IsStrictlyPositive A ∧ A * H = H * A }`.

This is the partial-victory form of Lieb–Tropp concavity that can be
proved without the full DPI / Lie–Trotter machinery: on the commuting
slice `A H = H A` lifts to `(log A) H = H (log A)` via `Commute.cfc_real`,
so `exp (H + log A) = exp H · exp (log A) = exp H · A`. The functional
then reduces to the real-linear functional `A ↦ Re tr (exp H · A)` of `A`,
and linear maps are concave on any convex set.

**Proof outline.**

1. The commuting slice is convex: strict-positivity is convex
   (`CFC.convex_setOf_isStrictlyPositive_matrix`), and `{A | A * H = H * A}`
   is a linear subspace (closed under addition and scalar multiplication).
2. For strict-pos `A` commuting with `H`: `Commute H (CFC.log A)` by
   `Commute.cfc_real` (since `log = cfc Real.log` and `H` is self-adjoint
   ↔ commutes with `star H = H`).
3. `NormedSpace.exp (H + CFC.log A) = NormedSpace.exp H * A`
   via `NormedSpace.exp_add_of_commute` and `CFC.exp_log` (strict-pos `A`).
4. The map `A ↦ (trace (exp H * A)).re` is ℝ-linear (composition of
   left-mul by `exp H`, the linear trace, and `Complex.re`).
5. Linear ⇒ concave on any convex set via `LinearMap.concaveOn`.
-/
theorem re_trace_exp_log_concave_commuting
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) :
    ConcaveOn ℝ
      {A : Matrix n n ℂ | IsStrictlyPositive A ∧ A * H = H * A}
      (fun A => (Matrix.trace (NormedSpace.exp (H + CFC.log A) :
        Matrix n n ℂ)).re) := by
  classical
  -- The strict-positive cone (convex, by Mathlib).
  set SP : Set (Matrix n n ℂ) := {A : Matrix n n ℂ | IsStrictlyPositive A}
    with hSP_def
  -- The commuting subspace `{A | A * H = H * A}` (linear, hence convex).
  set CH : Set (Matrix n n ℂ) := {A : Matrix n n ℂ | A * H = H * A}
    with hCH_def
  -- The target slice = SP ∩ CH.
  set S : Set (Matrix n n ℂ) := SP ∩ CH with hS_def
  -- ── Step 1.  Convexity of `S`. ─────────────────────────────────────
  have hSP_conv : Convex ℝ SP := CFC.convex_setOf_isStrictlyPositive_matrix
  have hCH_conv : Convex ℝ CH := by
    -- `CH` is closed under convex (in fact linear) combinations because
    -- `A ↦ A*H - H*A` is ℝ-linear and vanishes on both endpoints.
    intro A₁ hA₁ A₂ hA₂ a b _ _ _
    show (a • A₁ + b • A₂) * H = H * (a • A₁ + b • A₂)
    have hA₁eq : A₁ * H = H * A₁ := hA₁
    have hA₂eq : A₂ * H = H * A₂ := hA₂
    rw [add_mul, mul_add, Matrix.smul_mul, Matrix.smul_mul,
        Matrix.mul_smul, Matrix.mul_smul, hA₁eq, hA₂eq]
  have hS_conv : Convex ℝ S := hSP_conv.inter hCH_conv
  -- The set in the statement matches `S` (`mem`-coincide).
  have hS_eq : S = {A : Matrix n n ℂ | IsStrictlyPositive A ∧ A * H = H * A} := by
    ext A; simp [hS_def, hSP_def, hCH_def]
  -- ── Step 2.  Pointwise factorization on `S`. ──────────────────────
  --   For `A ∈ S`:  exp (H + log A) = exp H * A.
  have hH_sa : IsSelfAdjoint H := hH.isSelfAdjoint
  have hkey :
      ∀ A ∈ S,
        (NormedSpace.exp (H + CFC.log A) : Matrix n n ℂ) =
          NormedSpace.exp H * A := by
    intro A hA
    obtain ⟨hA_sp, hAH⟩ : IsStrictlyPositive A ∧ A * H = H * A := hA
    -- Commute H A from `A * H = H * A`.
    have hcomm_HA : Commute H A := (hAH).symm
    -- Lift commutation to `CFC.log A` via `Commute.cfc_real`.
    -- `CFC.log a = cfc Real.log a`.
    have hcomm_HlogA : Commute H (CFC.log A) := by
      show Commute H (cfc Real.log A)
      -- `Commute.cfc_real` gives `Commute (cfc f a) b` from `Commute a b`.
      -- We want `Commute H (cfc Real.log A)`, i.e. the *other* direction.
      -- Take `a := A`, `b := H`, then symmetrize.
      have h₁ : Commute A H := hAH
      have h₂ : Commute (cfc Real.log A) H := h₁.cfc_real _
      exact h₂.symm
    -- `exp` is additive on commuting pairs.
    -- `NormedSpace.exp_add_of_commute` requires `NormedAlgebra ℚ 𝔸`; we
    -- restrict the natural `NormedAlgebra ℂ (Matrix n n ℂ)` to ℚ (same
    -- trick as in `MatrixExpPositivity.continuous_re_trace_exp`).
    let +nondep : NormedAlgebra ℚ (Matrix n n ℂ) :=
      NormedAlgebra.restrictScalars ℚ ℂ (Matrix n n ℂ)
    have hexp_add :
        (NormedSpace.exp (H + CFC.log A) : Matrix n n ℂ) =
          NormedSpace.exp H * NormedSpace.exp (CFC.log A) :=
      NormedSpace.exp_add_of_commute hcomm_HlogA
    -- `exp ∘ log = id` on strict-positives (CFC).
    have hexp_log : (NormedSpace.exp (CFC.log A) : Matrix n n ℂ) = A :=
      CFC.exp_log A hA_sp
    rw [hexp_add, hexp_log]
  -- ── Step 3.  Re tr (exp H · A) is ℝ-linear in A. ──────────────────
  -- Build the ℝ-linear map  A ↦ Re tr (exp H · A).
  let expH : Matrix n n ℂ := NormedSpace.exp H
  -- Left multiplication by `expH` as an ℝ-linear endomorphism.
  let leftMul : Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ :=
    { toFun := fun A => expH * A
      map_add' := by intros; simp [mul_add]
      map_smul' := by intros; simp }
  -- Compose:  Re ∘ trace ∘ leftMul  is ℝ-linear.
  let traceExpHmul_LM : Matrix n n ℂ →ₗ[ℝ] ℝ :=
    (Complex.reLm.comp (Matrix.traceLinearMap n ℝ ℂ)).comp leftMul
  have hLM_eq : ∀ A : Matrix n n ℂ,
      traceExpHmul_LM A = (Matrix.trace (expH * A)).re := by
    intro A; rfl
  -- The linear functional is concave on `S` (and on any convex set).
  have hlin_concave :
      ConcaveOn ℝ S (fun A => (Matrix.trace (expH * A)).re) := by
    have := traceExpHmul_LM.concaveOn (s := S) hS_conv
    simpa [hLM_eq] using this
  -- ── Step 4.  Rewrite the target along `hkey` and conclude. ───────
  -- On `S`, the target equals the linear functional.
  have hcongr : ∀ A ∈ S,
      (Matrix.trace (expH * A)).re =
        (Matrix.trace (NormedSpace.exp (H + CFC.log A) :
          Matrix n n ℂ)).re := by
    intro A hA
    rw [hkey A hA]
  have hconcave_S :
      ConcaveOn ℝ S
        (fun A => (Matrix.trace (NormedSpace.exp (H + CFC.log A) :
          Matrix n n ℂ)).re) :=
    hlin_concave.congr hcongr
  -- Transport across the set-equality `S = {A | sp A ∧ A*H = H*A}`.
  rw [hS_eq] at hconcave_S
  exact hconcave_S

end Matrix
