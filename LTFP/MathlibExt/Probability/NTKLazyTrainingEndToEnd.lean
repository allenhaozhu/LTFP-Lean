/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.ResidualGronwallDecay
import LTFP.MathlibExt.MatrixAnalysis.LoewnerPerturbation
import LTFP.MathlibExt.MatrixAnalysis.MapOfRealNorm
import LTFP.MathlibExt.Probability.FullNetwork

/-!
# End-to-end NTK lazy training carrier (parametric on the residual ODE)

**R4 NTK Option A.2 — end-to-end lazy training closure.**

This module composes the two parametric pieces of the NTK
lazy-training pipeline:

* **E3e.1 — Loewner coercivity transfer.**
  `Matrix.PosSemidef.le_smul_one_perturb` converts the initial
  coercivity bound `ρ • 1 ≤ K(0)` into a coercivity bound on `K(t)`
  whenever the operator-norm drift `‖K(t) - K(0)‖` is at most `ρ/2`,
  yielding `(ρ/2) • 1 ≤ K(t)`.

* **Strategy 1 — Grönwall exponential residual decay.**
  `LTFP.ntk_residual_gronwall_decay` then converts this coercivity
  floor into the exponential decay `‖r(T)‖² ≤ ‖r(0)‖² · exp(-ρ T)`
  of the residual along a gradient-flow trajectory satisfying
  `r'(t) = -K(t) · r(t)`.

The Loewner perturbation lemma lives over `Matrix n n ℂ` (since its
proof routes through the continuous functional calculus), whereas
the full training kernel `fullTrainingKernel` returns a real matrix.
We therefore bridge the two via the entrywise embedding
`(·:ℝ→ℂ)` and the operator-norm-preserving lemma
`Matrix.l2_opNorm_map_complex_ofReal`.

## Main result

* `ntk_lazy_training_carrier_parametric` —
  given initial coercivity `ρ • 1 ≤ K(0)`, a uniform drift bound
  `‖K(t) - K(0)‖ ≤ ρ/2`, and a differentiable residual
  `r` satisfying the linear ODE `r'(t) = -K(t) · r(t)`, the residual
  decays exponentially in norm:

      `‖r(T)‖² ≤ ‖r(0)‖² · exp(-(ρ T))` for all `T ≥ 0`.

This is the end-to-end parametric closure of the NTK lazy-training
convergence chain — the user supplies the ODE relation; the rest is
purely deterministic.

## Note on the drift hypothesis

The drift bound `hK_drift_small` is stated for all `t : ℝ` (not just
`t ≥ 0`). Strategy 1 (`ntk_residual_gronwall_decay`) requires the
coercivity floor `(ρ/2) • 1 ≤ K t` for ALL `t`, since its underlying
`antitone_of_deriv_nonpos` argument needs the Lyapunov derivative
bound to hold globally. The drift hypothesis must therefore be
universal in `t`. In practice the bootstrap argument in the
NTK pipeline establishes this uniform drift via control on the
parameter trajectory, so the universal form is the natural
interface.

## References

* Bach (2024) *Learning Theory from First Principles*, §12 (NTK lazy
  training).
* `LTFP.MathlibExt.MatrixAnalysis.LoewnerPerturbation` — E3e.1.
* `LTFP.MathlibExt.Probability.ResidualGronwallDecay` — Strategy 1.
* `LTFP.MathlibExt.Probability.FullNetwork` — `fullTrainingKernel`.
-/

open scoped InnerProductSpace MatrixOrder Matrix.Norms.L2Operator ComplexOrder
open Matrix ProbabilityTheory

namespace LTFP

/-! ### Helper: real ↔ complex bridge for Loewner inequalities

The Loewner perturbation lemma `Matrix.PosSemidef.le_smul_one_perturb`
is stated for `Matrix n n ℂ`. To apply it to the real-valued
`fullTrainingKernel`, we cast entrywise via `(·:ℝ→ℂ)` and pull the
conclusion back to ℝ via the dot-product characterization of
positive semidefiniteness. -/

section RealComplexBridge

variable {n : ℕ} [Nonempty (Fin n)]

/-- The entrywise `ℝ ↪ ℂ` cast of a Hermitian real matrix is
Hermitian. -/
private lemma isHermitian_map_ofReal
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian) :
    (M.map (fun r : ℝ => (r : ℂ))).IsHermitian := by
  refine IsHermitian.map hM (fun r : ℝ => (r : ℂ)) ?_
  -- Function.Semiconj (·:ℝ→ℂ) star star.
  intro r
  -- `star r = r` on ℝ and `star (r : ℂ) = conj (r : ℂ) = (r : ℂ)`.
  show ((star r : ℝ) : ℂ) = star ((r : ℂ))
  rw [show (star r : ℝ) = r from rfl, RCLike.star_def, Complex.conj_ofReal]

/-- The entrywise `ℝ ↪ ℂ` cast of a real matrix subtraction
distributes over `map`. -/
private lemma map_ofReal_sub
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    (A - B).map (fun r : ℝ => (r : ℂ))
      = A.map (fun r : ℝ => (r : ℂ)) - B.map (fun r : ℝ => (r : ℂ)) := by
  ext i j
  simp [Matrix.map_apply, Matrix.sub_apply, Complex.ofReal_sub]

/-- The entrywise `ℝ ↪ ℂ` cast sends the real identity matrix to the
complex identity matrix. -/
private lemma map_ofReal_one :
    ((1 : Matrix (Fin n) (Fin n) ℝ).map (fun r : ℝ => (r : ℂ)))
      = (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.map_apply, Matrix.one_apply_eq]
  · simp [Matrix.map_apply, Matrix.one_apply_ne hij]

/-- The entrywise `ℝ ↪ ℂ` cast commutes with real-scalar multiplication
by a real number on the identity matrix. -/
private lemma map_ofReal_smul_one (c : ℝ) :
    ((c • (1 : Matrix (Fin n) (Fin n) ℝ)).map (fun r : ℝ => (r : ℂ)))
      = (c : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply_eq]
  · simp [Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply_ne hij]

/-- **Loewner forward cast (ℝ → ℂ).**

If `c • 1 ≤ A` in the Loewner order on `Matrix (Fin n) (Fin n) ℝ`,
then the same inequality holds after entrywise casting to ℂ. -/
private lemma loewner_forward_cast
    {A : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (h : (c : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ A) :
    (c : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ)
      ≤ A.map (fun r : ℝ => (r : ℂ)) := by
  -- `(A - c • 1).PosSemidef` over ℝ; show `(A.map ofReal - (c • 1).map ofReal).PosSemidef`.
  have hPSD : (A - c • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr h)
  -- Hermitian.
  have h_herm_R : (A - c • (1 : Matrix (Fin n) (Fin n) ℝ)).IsHermitian := hPSD.1
  -- Cast Hermitian to ℂ.
  have h_herm_C : ((A - c • (1 : Matrix (Fin n) (Fin n) ℝ)).map
      (fun r : ℝ => (r : ℂ))).IsHermitian := isHermitian_map_ofReal h_herm_R
  -- The dot-product nonneg over ℝ implies dot-product nonneg over ℂ for real lifts.
  rw [Matrix.le_iff]
  -- Rewrite the difference under the map.
  have h_diff_map :
      A.map (fun r : ℝ => (r : ℂ)) - (c : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ)
        = (A - c • (1 : Matrix (Fin n) (Fin n) ℝ)).map (fun r : ℝ => (r : ℂ)) := by
    rw [map_ofReal_sub, map_ofReal_smul_one]
  rw [h_diff_map]
  -- Now prove `((A - c • 1).map ofReal).PosSemidef`.
  set M : Matrix (Fin n) (Fin n) ℝ := A - c • (1 : Matrix (Fin n) (Fin n) ℝ) with hM_def
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg h_herm_C
  intro y
  -- Decompose `y` componentwise: `y i = y_re i + I * y_im i`.
  set yRe : Fin n → ℝ := fun i => (y i).re with hyRe
  set yIm : Fin n → ℝ := fun i => (y i).im with hyIm
  -- Real PSD on M.
  have hM_PSD : M.PosSemidef := hPSD
  have h_real_yRe : 0 ≤ yRe ⬝ᵥ (M *ᵥ yRe) := by
    have := hM_PSD.dotProduct_mulVec_nonneg yRe
    have hstar : (star yRe : Fin n → ℝ) = yRe := by funext i; simp
    rwa [hstar] at this
  have h_real_yIm : 0 ≤ yIm ⬝ᵥ (M *ᵥ yIm) := by
    have := hM_PSD.dotProduct_mulVec_nonneg yIm
    have hstar : (star yIm : Fin n → ℝ) = yIm := by funext i; simp
    rwa [hstar] at this
  -- Set up component matrices.
  set Mr : Fin n → ℝ := M *ᵥ yRe with hMr
  set Mi : Fin n → ℝ := M *ᵥ yIm with hMi
  -- Componentwise: `(M.map ofReal *ᵥ y) i = (Mr i : ℂ) + I * (Mi i : ℂ)`.
  have hMV : ∀ i, (M.map (fun r : ℝ => (r : ℂ)) *ᵥ y) i
      = (Mr i : ℂ) + Complex.I * (Mi i : ℂ) := by
    intro i
    simp only [Matrix.mulVec, Matrix.map_apply, dotProduct]
    have h_split :
        ∀ j, ((M i j : ℂ) * y j)
            = ((M i j : ℝ) * yRe j : ℂ)
              + Complex.I * ((M i j : ℝ) * yIm j : ℂ) := by
      intro j
      have hyj : y j = (yRe j : ℂ) + (yIm j : ℂ) * Complex.I := by
        rw [hyRe, hyIm]
        exact (Complex.re_add_im (y j)).symm
      rw [hyj]
      push_cast
      ring
    simp_rw [h_split]
    rw [Finset.sum_add_distrib]
    congr 1
    · push_cast
      simp [hMr, Matrix.mulVec, dotProduct]
    · rw [← Finset.mul_sum]
      push_cast
      simp [hMi, Matrix.mulVec, dotProduct]
  -- `star y i = (yRe i : ℂ) - I * (yIm i : ℂ)`.
  have hStarY : ∀ i, (star y) i
      = (yRe i : ℂ) - Complex.I * (yIm i : ℂ) := by
    intro i
    show star (y i) = _
    rw [hyRe, hyIm]
    rw [RCLike.star_def]
    apply Complex.ext
    · simp
    · simp
  -- Compute the dot product.
  have hDP :
      star y ⬝ᵥ (M.map (fun r : ℝ => (r : ℂ)) *ᵥ y)
        = ((yRe ⬝ᵥ Mr + yIm ⬝ᵥ Mi : ℝ) : ℂ)
          + Complex.I * ((yRe ⬝ᵥ Mi - yIm ⬝ᵥ Mr : ℝ) : ℂ) := by
    unfold dotProduct
    simp_rw [hStarY, hMV]
    have h_each : ∀ i,
        ((yRe i : ℂ) - Complex.I * (yIm i : ℂ))
            * ((Mr i : ℂ) + Complex.I * (Mi i : ℂ))
          = ((yRe i * Mr i + yIm i * Mi i : ℝ) : ℂ)
            + Complex.I * ((yRe i * Mi i - yIm i * Mr i : ℝ) : ℂ) := by
      intro i
      have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
      push_cast
      ring_nf
      rw [show Complex.I ^ 2 = -1 from by rw [sq]; exact hI2]
      ring
    simp_rw [h_each]
    rw [Finset.sum_add_distrib]
    congr 1
    · -- ∑ i, ((yRe i * Mr i + yIm i * Mi i : ℝ) : ℂ)
      --   = ((yRe ⬝ᵥ Mr + yIm ⬝ᵥ Mi : ℝ) : ℂ).
      push_cast
      rw [Finset.sum_add_distrib]
    · -- I * ∑ i, ((yRe i * Mi i - yIm i * Mr i : ℝ) : ℂ)
      --   = I * ((yRe ⬝ᵥ Mi - yIm ⬝ᵥ Mr : ℝ) : ℂ).
      rw [← Finset.mul_sum]
      push_cast
      congr 1
      rw [Finset.sum_sub_distrib]
  -- Symmetry: `yRe ⬝ᵥ Mi = yIm ⬝ᵥ Mr` (since M is symmetric).
  have h_sym : yRe ⬝ᵥ Mi = yIm ⬝ᵥ Mr := by
    rw [hMr, hMi]
    have hMt : Mᵀ = M := by
      have h := hM_PSD.1
      have : Mᴴ = M := h
      have hH : Mᴴ = Mᵀ := by
        ext i j
        simp [Matrix.conjTranspose_apply, Matrix.transpose_apply]
      rw [← hH]
      exact this
    -- Direct expansion using symmetry of M (Mᵀ = M).
    -- ∑ i, yRe i * (∑ j, M i j * yIm j)
    --   = ∑ i ∑ j, yRe i * (M i j * yIm j)
    --   = ∑ j ∑ i, yRe i * (M i j * yIm j)   [Finset.sum_comm]
    --   = ∑ j, yIm j * (∑ i, M j i * yRe i)  [symmetry of M, ring]
    --   = ∑ j, yIm j * (M *ᵥ yRe) j.
    unfold dotProduct Matrix.mulVec
    simp only [dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    -- Goal: ∑ x, yRe x * (M x j * yIm j) = ∑ i, yIm j * (M j i * yRe i)
    have hMsym : ∀ i, M i j = M j i := by
      intro i
      have h := congrFun (congrFun hMt i) j
      simp [Matrix.transpose_apply] at h
      exact h.symm
    apply Finset.sum_congr rfl
    intro i _
    rw [hMsym i]
    ring
  -- Imaginary part vanishes.
  have hImZero : (yRe ⬝ᵥ Mi - yIm ⬝ᵥ Mr : ℝ) = 0 := by linarith [h_sym]
  -- Real part nonneg.
  have hReNN : 0 ≤ (yRe ⬝ᵥ Mr + yIm ⬝ᵥ Mi : ℝ) := by
    rw [hMr, hMi]
    linarith [h_real_yRe, h_real_yIm]
  rw [hDP, hImZero]
  simp only [Complex.ofReal_zero, mul_zero, add_zero]
  rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) from rfl]
  exact_mod_cast hReNN

/-- **Loewner backward cast (ℂ → ℝ).**

If `M : Matrix (Fin n) (Fin n) ℝ` is Hermitian and
`c • 1 ≤ M.map (·:ℝ→ℂ)` holds in the Loewner order on
`Matrix (Fin n) (Fin n) ℂ`, then `c • 1 ≤ M` over ℝ. -/
private lemma loewner_backward_cast
    {M : Matrix (Fin n) (Fin n) ℝ} (hM_herm : M.IsHermitian) {c : ℝ}
    (h : (c : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ)
      ≤ M.map (fun r : ℝ => (r : ℂ))) :
    (c : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ M := by
  -- It suffices to show, for each x : Fin n → ℝ,
  --   c * (x ⬝ᵥ x) ≤ x ⬝ᵥ M *ᵥ x.
  rw [Matrix.le_iff]
  -- `M - c • 1` is Hermitian over ℝ.
  have hCSmul_herm : (c • (1 : Matrix (Fin n) (Fin n) ℝ)).IsHermitian := by
    ext i j
    show (c • (1 : Matrix (Fin n) (Fin n) ℝ))ᵀ i j = c • (1 : Matrix _ _ ℝ) i j
    by_cases hij : i = j
    · subst hij
      simp [Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply_eq]
    · have hji : ¬ j = i := fun h => hij h.symm
      simp [Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply_ne hji,
            Matrix.one_apply_ne hij]
  have h_sub_herm : (M - c • (1 : Matrix (Fin n) (Fin n) ℝ)).IsHermitian :=
    hM_herm.sub hCSmul_herm
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg h_sub_herm
  intro x
  -- Lift x to ℂ via ofReal.
  set xC : Fin n → ℂ := fun i => ((x i : ℝ) : ℂ) with hxC_def
  -- From `h` we know `(M.map ofReal - c • 1).PosSemidef` over ℂ.
  have hPSD_C : (M.map (fun r : ℝ => (r : ℂ))
      - (c : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ)).PosSemidef := by
    rw [← Matrix.le_iff]
    exact h
  -- The complex dotProduct nonneg for xC.
  have hDP_C : 0 ≤ star xC ⬝ᵥ
      ((M.map (fun r : ℝ => (r : ℂ))
        - (c : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ xC) :=
    hPSD_C.dotProduct_mulVec_nonneg xC
  -- Star of a real lift is the lift again.
  have h_star_xC : (star xC : Fin n → ℂ) = xC := by
    funext i
    show star (xC i) = xC i
    rw [hxC_def]
    show star ((x i : ℂ)) = ((x i : ℝ) : ℂ)
    rw [RCLike.star_def, Complex.conj_ofReal]
  rw [h_star_xC] at hDP_C
  -- Star x = x on ℝ.
  have h_star_x : (star x : Fin n → ℝ) = x := by funext i; simp
  -- `(M.map ofReal *ᵥ xC) i = ((M *ᵥ x) i : ℂ)`.
  have h_mulVec_lift : ∀ i,
      ((M.map (fun r : ℝ => (r : ℂ))) *ᵥ xC) i = ((M *ᵥ x) i : ℂ) := by
    intro i
    have h := RingHom.map_mulVec Complex.ofRealHom M x i
    simp only [Matrix.map, Function.comp_def, Complex.ofRealHom_eq_coe] at h
    show ((M.map (fun r : ℝ => (r : ℂ))) *ᵥ xC) i = ((M *ᵥ x) i : ℂ)
    rw [hxC_def]
    exact h.symm
  -- `((c • 1) *ᵥ xC) i = c * xC i`.
  have h_mulVec_smul_one : ∀ i,
      (((c : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ xC) i = (c : ℂ) * xC i := by
    intro i
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
    show (c : ℝ) • xC i = (c : ℂ) * xC i
    rw [Complex.real_smul]
  -- Compute the complex dotProduct.
  have hDP_eq : xC ⬝ᵥ ((M.map (fun r : ℝ => (r : ℂ))
        - (c : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ)) *ᵥ xC)
      = ((x ⬝ᵥ (M *ᵥ x) - c * (x ⬝ᵥ x) : ℝ) : ℂ) := by
    rw [Matrix.sub_mulVec]
    unfold dotProduct
    rw [Finset.sum_congr rfl (g := fun i => xC i *
        (((M *ᵥ x) i : ℂ) - (c : ℂ) * xC i)) (by
      intro i _
      rw [Pi.sub_apply, h_mulVec_lift i, h_mulVec_smul_one i])]
    -- Goal: ∑ i, xC i * (((M *ᵥ x) i : ℂ) - (c : ℂ) * xC i) = ...
    have h_each : ∀ i,
        xC i * (((M *ᵥ x) i : ℂ) - (c : ℂ) * xC i)
          = ((x i * (M *ᵥ x) i - c * (x i * x i) : ℝ) : ℂ) := by
      intro i
      rw [hxC_def]
      push_cast
      ring
    simp_rw [h_each]
    rw [← Complex.ofReal_sum]
    congr 1
    -- ∑ i, (x i * (M *ᵥ x) i - c * (x i * x i)) = x ⬝ᵥ (M *ᵥ x) - c * (x ⬝ᵥ x).
    rw [Finset.sum_sub_distrib]
    rw [← Finset.mul_sum]
  rw [hDP_eq] at hDP_C
  -- Convert to real nonneg.
  have hReNN : 0 ≤ (x ⬝ᵥ (M *ᵥ x) - c * (x ⬝ᵥ x) : ℝ) := by
    have := hDP_C
    rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) from rfl] at this
    exact_mod_cast this
  -- Conclude.
  rw [h_star_x]
  have h_sub_mulVec :
      ((M - c • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x)
        = (M *ᵥ x) - c • x := by
    rw [Matrix.sub_mulVec]
    congr 1
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [h_sub_mulVec, dotProduct_sub]
  have h_smul_dot : x ⬝ᵥ (c • x) = c * (x ⬝ᵥ x) := by
    rw [dotProduct_smul]
    rfl
  rw [h_smul_dot]
  linarith

end RealComplexBridge

/-! ### Coercivity transfer (ℝ-version) -/

set_option maxHeartbeats 400000 in
/-- **Real-valued Loewner coercivity transfer under operator-norm
perturbation.**

If `A` and `B` are real Hermitian matrices, `A ≽ ρ • 1` in the
Loewner order on `Matrix (Fin n) (Fin n) ℝ`, and `‖A - B‖ ≤ ε`
(L2 operator norm), then `B ≽ (ρ - ε) • 1`.

This is the ℝ-analogue of `Matrix.PosSemidef.le_smul_one_perturb`,
obtained by the entrywise `ℝ ↪ ℂ` cast and the operator-norm
preserving bridge `Matrix.l2_opNorm_map_complex_ofReal`. -/
theorem real_le_smul_one_perturb
    {n : ℕ} [Nonempty (Fin n)]
    {A B : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian)
    {ρ ε : ℝ}
    (hAρ : (ρ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ A)
    (hAB : ‖A - B‖ ≤ ε) :
    ((ρ - ε) : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ B := by
  -- Cast both matrices to ℂ.
  set AC : Matrix (Fin n) (Fin n) ℂ := A.map (fun r : ℝ => (r : ℂ)) with hAC
  set BC : Matrix (Fin n) (Fin n) ℂ := B.map (fun r : ℝ => (r : ℂ)) with hBC
  -- Hermitian carries over.
  have hAC_herm : AC.IsHermitian := isHermitian_map_ofReal hA
  have hBC_herm : BC.IsHermitian := isHermitian_map_ofReal hB
  -- Loewner coercivity carries over.
  have hAρ_C : (ρ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ AC :=
    loewner_forward_cast hAρ
  -- Norm carries over.
  have h_norm_C : ‖AC - BC‖ ≤ ε := by
    rw [hAC, hBC, ← map_ofReal_sub, Matrix.l2_opNorm_map_complex_ofReal]
    exact hAB
  -- Apply the complex-version perturbation lemma.
  have hBC_C : ((ρ - ε) : ℝ) • (1 : Matrix (Fin n) (Fin n) ℂ) ≤ BC :=
    Matrix.PosSemidef.le_smul_one_perturb hAC_herm hBC_herm hAρ_C h_norm_C
  -- Pull back to ℝ.
  exact loewner_backward_cast hB hBC_C

/-! ### End-to-end NTK lazy training carrier -/

set_option maxHeartbeats 400000 in
/-- **End-to-end NTK lazy training carrier (parametric on the
residual ODE).**

Given:

* a parameter trajectory `θ : ℝ → Param d m`;
* Hermitian dynamic NTK `K(t) := fullTrainingKernel σ σ' b (θ t) xs`
  for every `t`;
* initial coercivity `K(0) ≽ ρ • 1` with `0 < ρ`;
* uniform drift bound `‖K(t) - K(0)‖ ≤ ρ / 2` (for every `t`);
* a differentiable residual trajectory `r : ℝ → EuclideanSpace ℝ (Fin n)`
  satisfying the linear ODE `r'(t) = -(K(t) · r(t))`;

then for every `T ≥ 0` the residual decays exponentially in norm:

  `‖r(T)‖² ≤ ‖r(0)‖² · exp(-(ρ T))`.

This is the end-to-end deterministic core of the NTK lazy-training
convergence theorem (Bach 2024, §12). The user supplies the ODE
relation as a hypothesis; the present theorem composes
`real_le_smul_one_perturb` (coercivity transfer at every `t` along the
trajectory) with `LTFP.ntk_residual_gronwall_decay` (deterministic
exponential Grönwall decay).

## ρ-convention

Strategy 1 (`ntk_residual_gronwall_decay`) consumes a `(ρ_S₁ / 2) • 1`
floor and outputs the decay rate `exp(-ρ_S₁ T)`. We instantiate
`ρ_S₁ := ρ` so that the perturbation lemma's output
`(ρ - ρ/2) • 1 = (ρ/2) • 1` matches Strategy 1's required floor, and
the conclusion is the clean `exp(-(ρ T))`. -/
theorem ntk_lazy_training_carrier_parametric
    {d n m : ℕ}
    [Nonempty (Fin n)]
    (σ σ' : ℝ → ℝ)
    (b : Fin m → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (θ : ℝ → Param d m)
    (hK_herm : ∀ t,
      (fullTrainingKernel σ σ' b (θ t) xs).IsHermitian)
    {ρ : ℝ} (hρ_pos : 0 < ρ)
    (hK_init_coercive :
      (ρ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤
        fullTrainingKernel σ σ' b (θ 0) xs)
    (hK_drift_small : ∀ t : ℝ,
      ‖fullTrainingKernel σ σ' b (θ t) xs -
       fullTrainingKernel σ σ' b (θ 0) xs‖ ≤ ρ / 2)
    (r : ℝ → EuclideanSpace ℝ (Fin n))
    (hr_diff : Differentiable ℝ r)
    (hr_ODE : ∀ t,
      deriv r t = -(WithLp.toLp 2
        ((fullTrainingKernel σ σ' b (θ t) xs) *ᵥ WithLp.ofLp (r t))))
    (T : ℝ) (hT : 0 ≤ T) :
    ‖r T‖ ^ 2 ≤ ‖r 0‖ ^ 2 * Real.exp (-(ρ * T)) := by
  -- Abbreviate the NTK trajectory.
  set K : ℝ → Matrix (Fin n) (Fin n) ℝ :=
    fun t => fullTrainingKernel σ σ' b (θ t) xs with hK_def
  -- Strategy 1's required coercivity floor at every t:
  -- `(ρ/2) • 1 ≤ K t`.
  have h_floor : ∀ t : ℝ,
      (ρ / 2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ K t := by
    intro t
    -- Apply real_le_smul_one_perturb with A = K(0), B = K(t),
    -- ρ_perturb = ρ, ε = ρ/2.
    -- We need ‖K(0) - K(t)‖ ≤ ρ/2; the hypothesis gives ‖K(t) - K(0)‖ ≤ ρ/2.
    have h_drift_sym : ‖K 0 - K t‖ ≤ ρ / 2 := by
      rw [norm_sub_rev]; exact hK_drift_small t
    have h_perturb :
        ((ρ - ρ / 2) : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ K t :=
      real_le_smul_one_perturb (hK_herm 0) (hK_herm t)
        hK_init_coercive h_drift_sym
    -- (ρ - ρ/2) = ρ/2.
    have h_eq : (ρ - ρ / 2 : ℝ) = ρ / 2 := by ring
    rw [h_eq] at h_perturb
    exact h_perturb
  -- Apply Strategy 1.
  exact ntk_residual_gronwall_decay K hK_herm hρ_pos h_floor r hr_diff hr_ODE T hT

end LTFP
