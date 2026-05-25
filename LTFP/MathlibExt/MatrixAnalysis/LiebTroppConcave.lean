/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Lieb–Tropp direct concavity of `A ↦ Re tr exp (H + log A)`

For a fixed Hermitian matrix `H : Matrix n n ℂ`, the functional

  `A ↦ (Matrix.trace (NormedSpace.exp (H + CFC.log A))).re`

is concave on the cone of strictly positive matrices `A`.

This is the **direct** (non-logarithmic) form of the Lieb–Tropp
trace-exponential concavity.  The proof follows **Tropp 2012,
Proposition 5 / Lemma 6** (the *unnormalized* variational route over
the *full* strict-positive cone, rather than the unit-trace
density-matrix slice that yields the logarithmic form).

## Proof outline (Tropp 2012, unnormalized variational form)

Define the integrand

  `g(P, A) := Re tr (P · H) + Re tr (P · log A) − Re tr (P · log P) + Re tr P`.

This is the unnormalized Gibbs functional: the constant `+ Re tr P`
replaces the `−1` Lagrange multiplier of the unit-trace constraint, so
the supremum is taken over the full strict-positive cone of `P`
(rather than over density matrices).

* **Joint concavity (Step 2).** Decompose `g = ψ + (−φ)` where
  - `ψ(P, A) := Re tr (P · H) − Re tr (P · log P) + Re tr P` —
    hmm, that's not jointly affine; instead, decompose via the
    *shifted* relative entropy `D_s(P‖A) := Re tr (P log P − P log A
    − P + A)`, which is jointly convex (Part 5b
    `matrix_relative_entropy_joint_convex`):

      `g(P, A) = Re tr (P · H) − D_s(P‖A) + Re tr (A)`.

    Then `Re tr (P · H)` and `Re tr A` are jointly real-linear
    (hence jointly affine), and `−D_s` is jointly concave (negation
    of a jointly convex function).

* **Klein upper bound (Step 3).** Let `Y := NormedSpace.exp (H + log A)`.
  Then `H + log A` is Hermitian (sum of Hermitian) and `Y` is
  strictly positive (`Matrix.IsHermitian.isStrictlyPositive_exp`).
  Applying `matrix_relative_entropy_nonneg` (Part 4d) to `(P, Y)`:

    `0 ≤ Re tr (P log P − P log Y − P + Y)
       = Re tr (P log P) − Re tr (P · (H + log A)) − Re tr P + Re tr Y`,

  which rearranges to `g(P, A) ≤ Re tr Y`.

* **Equality at `P := Y` (Step 4).** Direct computation:
  `log Y = H + log A` via `CFC.log_exp`, so

    `Re tr (Y · log Y) = Re tr (Y · H) + Re tr (Y · log A)`,

  and hence `g(Y, A) = Re tr Y`.

* **Conclusion (Step 5).** Apply `ConcaveOn.partial_sSup_concave` to
  conclude that

    `A ↦ sSup { g (P, A) | P ∈ strict-pos }  =  Re tr exp (H + log A)`

  is concave on `strict-pos`.

## Main result

* `Matrix.lieb_tropp_concave` — direct concavity of
  `A ↦ (Matrix.trace (NormedSpace.exp (H + CFC.log A))).re`
  on `{A | IsStrictlyPositive A}`.

## Reference

* J. A. Tropp, *From joint convexity of quantum relative entropy to a
  concavity theorem of Lieb*, Proc. Amer. Math. Soc. (2012),
  Proposition 5 and Lemma 6.
  <https://tropp.caltech.edu/papers/Tro12-Joint-Convexity.pdf>
-/
import LTFP.MathlibExt.Analysis.ConcaveOnPartialSup
import LTFP.MathlibExt.MatrixAnalysis.LiebTraceComplementary
import LTFP.MathlibExt.MatrixAnalysis.LogTraceExpConcave
import LTFP.MathlibExt.MatrixAnalysis.MatrixEntropyLimit
import LTFP.MathlibExt.MatrixAnalysis.MatrixExpPositivity
import LTFP.MathlibExt.MatrixAnalysis.MatrixRelEntropy

namespace Matrix

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

/-- **Direct Lieb–Tropp trace-exp concavity.**

For any Hermitian `H : Matrix n n ℂ`, the functional

  `A ↦ (Matrix.trace (NormedSpace.exp (H + CFC.log A))).re`

is concave on the convex cone `{A | IsStrictlyPositive A}`.

This is the *direct* (non-logarithmic) form of Lieb's concavity
theorem.  The proof follows Tropp 2012, Prop. 5 / Lemma 6: a
*unnormalized* variational identity over the strict-positive cone
of auxiliary states `P`, using joint convexity of matrix relative
entropy (Part 5b) and the partial-supremum-of-jointly-concave-is-
concave principle (`ConcaveOn.partial_sSup_concave`).

Reference: J. A. Tropp, *From joint convexity of quantum relative
entropy to a concavity theorem of Lieb*, 2012,
<https://tropp.caltech.edu/papers/Tro12-Joint-Convexity.pdf>. -/
theorem lieb_tropp_concave
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (H : Matrix n n ℂ) (hH : H.IsHermitian) :
    ConcaveOn ℝ
      {A : Matrix n n ℂ | IsStrictlyPositive A}
      (fun A => (Matrix.trace (NormedSpace.exp (H + CFC.log A) :
        Matrix n n ℂ)).re) := by
  classical
  -- The strict-positive cone (the FULL domain — no unit-trace constraint).
  set SP : Set (Matrix n n ℂ) := {A : Matrix n n ℂ | IsStrictlyPositive A}
    with hSP_def
  -- The strict-pos × strict-pos product where Part 5b lives.
  set SP2 : Set (Matrix n n ℂ × Matrix n n ℂ) :=
    {z : Matrix n n ℂ × Matrix n n ℂ |
      IsStrictlyPositive z.1 ∧ IsStrictlyPositive z.2}
    with hSP2_def
  -- The unnormalized variational integrand
  -- g(P, A) := Re tr(P·H) + Re tr(P·log A) − Re tr(P·log P) + Re tr P.
  let g : Matrix n n ℂ × Matrix n n ℂ → ℝ := fun z =>
    (Matrix.trace (z.1 * H)).re +
      (Matrix.trace (z.1 * CFC.log z.2)).re -
      (Matrix.trace (z.1 * CFC.log z.1)).re +
      (Matrix.trace z.1).re
  -- ───────────────────────────────────────────────────────────────
  -- Step 1.  Convexity of `SP` and `SP × SP`.
  -- ───────────────────────────────────────────────────────────────
  have hSP_conv : Convex ℝ SP := CFC.convex_setOf_isStrictlyPositive_matrix
  have hSP2_eq : SP2 = SP ×ˢ SP := by
    ext z; simp [hSP_def, hSP2_def]
  have hSP2_conv : Convex ℝ SP2 := by
    rw [hSP2_eq]; exact hSP_conv.prod hSP_conv
  -- ───────────────────────────────────────────────────────────────
  -- Step 2.  Joint concavity of `g` on `SP × SP`.
  --
  -- Decomposition:  g = ψ + (-φ)  where
  --   ψ(P, A) := Re tr(P·H) + Re tr(A)             (jointly affine, ℝ-linear)
  --   φ(P, A) := Re tr(P·log P − P·log A − P + A)  (Part 5b joint convex)
  -- and the algebraic identity ψ − φ = g on `SP × SP`.
  -- ───────────────────────────────────────────────────────────────
  -- Part 5b: joint convexity of the shifted matrix relative entropy on SP × SP.
  have hφ_SP2 :
      ConvexOn ℝ SP2
        (fun z : Matrix n n ℂ × Matrix n n ℂ =>
          (Matrix.trace (z.1 * CFC.log z.1 - z.1 * CFC.log z.2 - z.1 + z.2)).re) :=
    matrix_relative_entropy_joint_convex (n := n)
  -- Its negation is jointly concave.
  have hnegφ_SP2 :
      ConcaveOn ℝ SP2
        (fun z : Matrix n n ℂ × Matrix n n ℂ =>
          -(Matrix.trace (z.1 * CFC.log z.1 - z.1 * CFC.log z.2 - z.1 + z.2)).re) :=
    hφ_SP2.neg
  -- ψ(P, A) := Re tr (P · H) + Re tr A. Build it from ℝ-linear maps on `Matrix × Matrix`.
  let traceMulH_LM : Matrix n n ℂ × Matrix n n ℂ →ₗ[ℝ] ℝ :=
    (Complex.reLm.comp (Matrix.traceLinearMap n ℝ ℂ)).comp
      ({  toFun := fun z => z.1 * H
          map_add' := by intros; simp [add_mul]
          map_smul' := by intros; simp } :
        Matrix n n ℂ × Matrix n n ℂ →ₗ[ℝ] Matrix n n ℂ)
  let tracesnd_LM : Matrix n n ℂ × Matrix n n ℂ →ₗ[ℝ] ℝ :=
    (Complex.reLm.comp (Matrix.traceLinearMap n ℝ ℂ)).comp
      (LinearMap.snd ℝ (Matrix n n ℂ) (Matrix n n ℂ))
  have h_traceMulH_eq : ∀ z : Matrix n n ℂ × Matrix n n ℂ,
      traceMulH_LM z = (Matrix.trace (z.1 * H)).re := by
    intro z; rfl
  have h_tracesnd_eq : ∀ z : Matrix n n ℂ × Matrix n n ℂ,
      tracesnd_LM z = (Matrix.trace z.2).re := by
    intro z; rfl
  -- ψ is concave (it is ℝ-linear, hence convex AND concave).
  have hψ_SP2 :
      ConcaveOn ℝ SP2
        (fun z : Matrix n n ℂ × Matrix n n ℂ =>
          (Matrix.trace (z.1 * H)).re + (Matrix.trace z.2).re) := by
    have h1 : ConcaveOn ℝ SP2
        (fun z : Matrix n n ℂ × Matrix n n ℂ => (Matrix.trace (z.1 * H)).re) := by
      have := traceMulH_LM.concaveOn hSP2_conv
      simpa [h_traceMulH_eq] using this
    have h2 : ConcaveOn ℝ SP2
        (fun z : Matrix n n ℂ × Matrix n n ℂ => (Matrix.trace z.2).re) := by
      have := tracesnd_LM.concaveOn hSP2_conv
      simpa [h_tracesnd_eq] using this
    exact h1.add h2
  -- Combine ψ + (-φ) to get joint concavity of g.
  -- Algebraic identity:  ψ + (-φ) = g pointwise on `SP × SP`.
  have hg_eq_psum :
      ∀ z ∈ SP2,
        ((Matrix.trace (z.1 * H)).re + (Matrix.trace z.2).re) +
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
    show ((Matrix.trace (z.1 * H)).re + (Matrix.trace z.2).re) +
          (-(Matrix.trace
                (z.1 * CFC.log z.1 - z.1 * CFC.log z.2 - z.1 + z.2)).re) = g z
    rw [hexpand]
    show ((Matrix.trace (z.1 * H)).re + (Matrix.trace z.2).re) +
          (-((Matrix.trace (z.1 * CFC.log z.1)).re -
              (Matrix.trace (z.1 * CFC.log z.2)).re -
              (Matrix.trace z.1).re + (Matrix.trace z.2).re)) =
        (Matrix.trace (z.1 * H)).re +
          (Matrix.trace (z.1 * CFC.log z.2)).re -
          (Matrix.trace (z.1 * CFC.log z.1)).re +
          (Matrix.trace z.1).re
    ring
  have hg_concave_SP2 : ConcaveOn ℝ SP2 g := by
    have hsum :
        ConcaveOn ℝ SP2
          (fun z => ((Matrix.trace (z.1 * H)).re + (Matrix.trace z.2).re) +
            (-(Matrix.trace
                  (z.1 * CFC.log z.1 - z.1 * CFC.log z.2 - z.1 + z.2)).re)) :=
      hψ_SP2.add hnegφ_SP2
    exact hsum.congr hg_eq_psum
  -- Cast to `SP ×ˢ SP` (the form `partial_sSup_concave` wants).
  have hg_concave_DSP : ConcaveOn ℝ (SP ×ˢ SP) g := by
    rw [hSP2_eq] at hg_concave_SP2
    exact hg_concave_SP2
  -- ───────────────────────────────────────────────────────────────
  -- Step 3.  Klein upper bound:
  --   for every (P, A) ∈ SP × SP,  g(P, A) ≤ Re tr (exp (H + log A)).
  --
  -- Proof:  let Y := exp (H + log A).  Then Y is strict-pos and
  -- log Y = H + log A.  Apply `matrix_relative_entropy_nonneg` to (P, Y).
  -- ───────────────────────────────────────────────────────────────
  -- Hermiticity preservation for `H + CFC.log A` (for any A).
  have hH_sa : IsSelfAdjoint H := hH
  have hlogA_sa : ∀ A : Matrix n n ℂ, IsSelfAdjoint (CFC.log A) :=
    fun _ => IsSelfAdjoint.log
  have hHlogA_sa : ∀ A : Matrix n n ℂ, IsSelfAdjoint (H + CFC.log A) :=
    fun A => hH_sa.add (hlogA_sa A)
  have hHlogA_herm : ∀ A : Matrix n n ℂ, (H + CFC.log A).IsHermitian :=
    fun A => hHlogA_sa A
  -- For each A ∈ SP, Y := exp (H + log A) is strict-pos.
  have hY_sp : ∀ A ∈ SP,
      IsStrictlyPositive (NormedSpace.exp (H + CFC.log A) : Matrix n n ℂ) := by
    intro A _
    exact Matrix.IsHermitian.isStrictlyPositive_exp (hHlogA_herm A)
  -- log Y = H + log A for Y := exp (H + log A).
  have hlog_Y : ∀ A : Matrix n n ℂ,
      CFC.log (NormedSpace.exp (H + CFC.log A) : Matrix n n ℂ) = H + CFC.log A := by
    intro A
    exact CFC.log_exp (H + CFC.log A) (hHlogA_sa A)
  -- The Klein upper bound: g(P, A) ≤ Re tr Y, for all P ∈ SP.
  have hg_le_traceExp : ∀ A ∈ SP, ∀ P ∈ SP,
      g (P, A) ≤ (Matrix.trace
        (NormedSpace.exp (H + CFC.log A) : Matrix n n ℂ)).re := by
    intro A hA P hP
    -- Let Y := exp (H + log A); strict-pos and log Y = H + log A.
    set Y : Matrix n n ℂ := NormedSpace.exp (H + CFC.log A) with hY_def
    have hY_sp' : IsStrictlyPositive Y := hY_sp A hA
    have hlogY : CFC.log Y = H + CFC.log A := hlog_Y A
    -- Apply the Klein/relative-entropy nonnegativity to (P, Y).
    have hKlein :
        0 ≤ (Matrix.trace (P * CFC.log P - P * CFC.log Y - P + Y)).re :=
      matrix_relative_entropy_nonneg hP hY_sp'
    -- Substitute log Y = H + log A and expand the trace.
    -- Re tr(P · (H + log A)) = Re tr(P · H) + Re tr(P · log A).
    have hPtr_HlogA :
        (Matrix.trace (P * (H + CFC.log A))).re
          = (Matrix.trace (P * H)).re + (Matrix.trace (P * CFC.log A)).re := by
      rw [mul_add, Matrix.trace_add, Complex.add_re]
    -- Re tr (P log P - P log Y - P + Y) =
    --   Re tr (P log P) - Re tr (P · (H + log A)) - Re tr P + Re tr Y.
    have hexp :
        (Matrix.trace (P * CFC.log P - P * CFC.log Y - P + Y)).re
          = (Matrix.trace (P * CFC.log P)).re
            - (Matrix.trace (P * CFC.log Y)).re
            - (Matrix.trace P).re
            + (Matrix.trace Y).re := by
      simp [Matrix.trace_sub, Matrix.trace_add, Complex.sub_re, Complex.add_re]
    -- Substitute log Y.
    have hPlogY_eq :
        (Matrix.trace (P * CFC.log Y)).re
          = (Matrix.trace (P * H)).re + (Matrix.trace (P * CFC.log A)).re := by
      rw [hlogY, hPtr_HlogA]
    -- Combine.
    rw [hexp, hPlogY_eq] at hKlein
    -- Rearrange the inequality:
    --   0 ≤ Re tr(P log P) - Re tr(P·H) - Re tr(P·log A) - Re tr P + Re tr Y
    -- ↔ Re tr(P·H) + Re tr(P·log A) - Re tr(P log P) + Re tr P ≤ Re tr Y
    -- which is g(P, A) ≤ Re tr Y.
    show (Matrix.trace (P * H)).re + (Matrix.trace (P * CFC.log A)).re -
          (Matrix.trace (P * CFC.log P)).re + (Matrix.trace P).re ≤
        (Matrix.trace Y).re
    linarith
  -- ───────────────────────────────────────────────────────────────
  -- Step 4.  Equality at `P := Y` (where Y := exp (H + log A)).
  --
  --   g(Y, A) = Re tr Y.
  --
  -- Proof: log Y = H + log A, so Re tr(Y · log Y) =
  -- Re tr(Y · H) + Re tr(Y · log A), and the algebraic substitution
  -- yields g(Y, A) = Re tr Y.
  -- ───────────────────────────────────────────────────────────────
  have hg_eq_at_Y : ∀ A ∈ SP,
      g ((NormedSpace.exp (H + CFC.log A) : Matrix n n ℂ), A) =
        (Matrix.trace (NormedSpace.exp (H + CFC.log A) :
          Matrix n n ℂ)).re := by
    intro A hA
    set Y : Matrix n n ℂ := NormedSpace.exp (H + CFC.log A) with hY_def
    have hlogY : CFC.log Y = H + CFC.log A := hlog_Y A
    -- Re tr (Y · (H + log A)) = Re tr (Y · H) + Re tr (Y · log A).
    have hYtr_HlogA :
        (Matrix.trace (Y * (H + CFC.log A))).re
          = (Matrix.trace (Y * H)).re + (Matrix.trace (Y * CFC.log A)).re := by
      rw [mul_add, Matrix.trace_add, Complex.add_re]
    -- Re tr (Y · log Y) = Re tr (Y · (H + log A)).
    have hYlogY :
        (Matrix.trace (Y * CFC.log Y)).re
          = (Matrix.trace (Y * H)).re + (Matrix.trace (Y * CFC.log A)).re := by
      rw [hlogY, hYtr_HlogA]
    -- Unfold g(Y, A) = Re tr(Y H) + Re tr(Y log A) - Re tr(Y log Y) + Re tr Y.
    show (Matrix.trace (Y * H)).re + (Matrix.trace (Y * CFC.log A)).re -
          (Matrix.trace (Y * CFC.log Y)).re + (Matrix.trace Y).re =
        (Matrix.trace Y).re
    rw [hYlogY]; ring
  -- ───────────────────────────────────────────────────────────────
  -- Step 5.  Apply `partial_sSup_concave`.
  -- ───────────────────────────────────────────────────────────────
  -- SP nonempty: the identity matrix is strict-positive.
  have hSP_ne : SP.Nonempty := ⟨1, isStrictlyPositive_one⟩
  -- Boundedness above of each section.
  have hbdd : ∀ A ∈ SP, BddAbove ((fun P : Matrix n n ℂ => g (P, A)) '' SP) := by
    intro A hA
    refine ⟨(Matrix.trace
      (NormedSpace.exp (H + CFC.log A) : Matrix n n ℂ)).re, ?_⟩
    rintro v ⟨P, hP, rfl⟩
    exact hg_le_traceExp A hA P hP
  -- The partial-sSup-of-jointly-concave lemma.
  have h_partial :=
    ConcaveOn.partial_sSup_concave (T := SP) (S := SP) (f := g)
      hg_concave_DSP hSP_conv hSP_conv hSP_ne hbdd
  -- ───────────────────────────────────────────────────────────────
  -- Step 6.  Identify the partial sup with `Re tr exp (H + log A)`.
  -- ───────────────────────────────────────────────────────────────
  have h_sSup_eq : ∀ A ∈ SP,
      sSup ((fun P : Matrix n n ℂ => g (P, A)) '' SP) =
      (Matrix.trace (NormedSpace.exp (H + CFC.log A) :
        Matrix n n ℂ)).re := by
    intro A hA
    -- The upper bound (Step 3) and the attainment at P = Y (Step 4).
    set Y : Matrix n n ℂ := NormedSpace.exp (H + CFC.log A) with hY_def
    have hY_mem : Y ∈ SP := hY_sp A hA
    have hY_eq : g (Y, A) = (Matrix.trace Y).re := hg_eq_at_Y A hA
    refine le_antisymm ?_ ?_
    · -- sSup ≤ Re tr Y, from the universal upper bound.
      apply csSup_le
      · -- The image is nonempty.
        exact ⟨g (Y, A), Y, hY_mem, rfl⟩
      · rintro v ⟨P, hP, rfl⟩
        exact hg_le_traceExp A hA P hP
    · -- Re tr Y ≤ sSup, from the attainment at Y.
      have : g (Y, A) ∈ (fun P : Matrix n n ℂ => g (P, A)) '' SP :=
        ⟨Y, hY_mem, rfl⟩
      have hbdd' := hbdd A hA
      have hle := le_csSup hbdd' this
      linarith [hY_eq, hle]
  -- ───────────────────────────────────────────────────────────────
  -- Step 7.  Conclude via `ConcaveOn.congr`.
  -- ───────────────────────────────────────────────────────────────
  refine h_partial.congr ?_
  intro A hA
  exact h_sSup_eq A hA

end Matrix
