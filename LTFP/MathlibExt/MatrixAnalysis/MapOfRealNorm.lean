/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Complex.Basic

/-!
# L2 operator norm is preserved by the entrywise `ℝ ↪ ℂ` matrix embedding

For a real matrix `A : Matrix m n ℝ`, casting each entry to a complex
number `A.map (fun r => (r : ℂ))` produces a complex matrix whose
L2 operator norm coincides with the L2 operator norm of `A`.

## Main result

* `Matrix.l2_opNorm_map_complex_ofReal` —
  `‖A.map (fun r : ℝ => (r : ℂ))‖ = ‖A‖`
  for `A : Matrix m n ℝ` under the scoped instance
  `Matrix.Norms.L2Operator`.

## Proof outline

Direct two-sided proof via `ContinuousLinearMap.opNorm_le_bound`:

* **`≤` direction.** For any `v : EuclideanSpace ℂ n`, write
  `v = vRe + I • vIm` with `vRe, vIm : EuclideanSpace ℝ n` the
  componentwise real and imaginary parts. Then `(A.map ofReal) *ᵥ v`
  splits into the same real-imaginary pieces via the `ℝ →+* ℂ`
  ring-hom commutation with `mulVec`. Pythagorean identity on the
  pieces gives the bound `‖A.map ofReal v‖² ≤ ‖A‖²·‖v‖²`.

* **`≥` direction.** For any real `v : EuclideanSpace ℝ n`, the
  componentwise lift `vC : EuclideanSpace ℂ n := toLp 2 ((·:ℝ→ℂ) ∘ ofLp v)`
  satisfies `‖vC‖ = ‖v‖` and `(A.map ofReal) *ᵥ vC` is the lift of
  `A *ᵥ v`, so `‖(A.map ofReal) *ᵥ vC‖ = ‖A *ᵥ v‖`. Taking sup over real `v`
  gives `‖A‖ ≤ ‖A.map ofReal‖`.

This is purely an "isometric ring extension" fact; no Mathlib lemma
delivers it directly, so we build it from `EuclideanSpace.norm_eq`,
`norm_ofReal`, and the operator-norm characterisation.
-/

open scoped Matrix.Norms.L2Operator

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n]

section MapOfReal

/-- Pointwise: the squared norm of `(a : ℂ) + I · (b : ℂ)` for real `a`, `b`
is `a^2 + b^2`. Used to apply Pythagoras to the entrywise decomposition. -/
private lemma normSq_ofReal_add_I_mul_ofReal (a b : ℝ) :
    ‖((a : ℂ) + Complex.I * (b : ℂ))‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, one_mul, sub_zero, zero_add, mul_zero, add_zero]
  ring

/-- Pointwise: the squared norm of a complex number is the sum of squares of
real and imaginary parts. -/
private lemma sq_norm_eq_re_sq_add_im_sq (z : ℂ) :
    ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply]
  ring

variable [DecidableEq n]

/-- Cast a real Euclidean vector to a complex Euclidean vector by
applying `Complex.ofReal` componentwise. -/
private noncomputable def realToComplexVec (v : EuclideanSpace ℝ n) :
    EuclideanSpace ℂ n :=
  WithLp.toLp 2 (fun i => ((WithLp.ofLp v) i : ℂ))

omit [Fintype n] [DecidableEq n] in
@[simp] private lemma realToComplexVec_apply (v : EuclideanSpace ℝ n) (i : n) :
    WithLp.ofLp (realToComplexVec v) i = ((WithLp.ofLp v) i : ℂ) := rfl

omit [DecidableEq n] in
/-- The complex lift of a real Euclidean vector has the same norm. -/
private lemma norm_realToComplexVec (v : EuclideanSpace ℝ n) :
    ‖realToComplexVec v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  show ‖((WithLp.ofLp v) i : ℂ)‖ ^ 2 = ‖(WithLp.ofLp v) i‖ ^ 2
  rw [Complex.norm_real]

omit [Fintype m] [DecidableEq n] in
/-- The mulVec of a real matrix's complex lift, applied to a real-lift
vector, is itself the real-lift of `A *ᵥ v`. -/
private lemma map_ofReal_mulVec_realToComplexVec
    (A : Matrix m n ℝ) (v : EuclideanSpace ℝ n) :
    (A.map (fun r : ℝ => (r : ℂ))) *ᵥ
        (fun i => ((WithLp.ofLp v) i : ℂ))
      = (fun i => (((A *ᵥ WithLp.ofLp v) i : ℝ) : ℂ)) := by
  funext i
  -- entry-wise `RingHom.map_mulVec` applied with `Complex.ofRealHom`.
  have h := RingHom.map_mulVec Complex.ofRealHom A (WithLp.ofLp v) i
  -- Goal: `(A.map fun r => (r : ℂ)) *ᵥ (fun j => ((v j) : ℂ))) i = ((A *ᵥ v) i : ℂ)`.
  -- `h` says: `((A *ᵥ v) i : ℂ) = ((Complex.ofRealHom ∘ v) ᵥ* A.map _) i`,
  -- but actually `h : ofRealHom ((A *ᵥ v) i) = (A.map ofRealHom *ᵥ (ofRealHom ∘ v)) i`.
  simp only [Matrix.map, Function.comp_def, Complex.ofRealHom_eq_coe] at h
  exact h.symm

set_option maxHeartbeats 800000 in
/-- **Bridge lemma.** The L2 operator norm is invariant under the
entrywise `ℝ ↪ ℂ` matrix embedding. -/
theorem l2_opNorm_map_complex_ofReal (A : Matrix m n ℝ) :
    ‖A.map (fun r : ℝ => (r : ℂ))‖ = ‖A‖ := by
  -- Let `T : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ m` be the bundled
  -- continuous linear map for the lifted matrix; and `S` for the real one.
  set T : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ m :=
    (Matrix.toEuclideanLin
      (𝕜 := ℂ) (m := m) (n := n)).trans LinearMap.toContinuousLinearMap
        (A.map (fun r : ℝ => (r : ℂ))) with hT_def
  set S : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ m :=
    (Matrix.toEuclideanLin
      (𝕜 := ℝ) (m := m) (n := n)).trans LinearMap.toContinuousLinearMap A with hS_def
  have hT_norm : ‖A.map (fun r : ℝ => (r : ℂ))‖ = ‖T‖ := rfl
  have hS_norm : ‖A‖ = ‖S‖ := rfl
  rw [hT_norm, hS_norm]
  -- Two-sided proof.
  refine le_antisymm ?_ ?_
  · -- `‖T‖ ≤ ‖S‖`. For every `v : EuclideanSpace ℂ n`, show `‖T v‖ ≤ ‖S‖ ‖v‖`.
    refine ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg _) ?_
    intro v
    -- Componentwise real and imaginary parts.
    set vRe : EuclideanSpace ℝ n :=
      WithLp.toLp 2 (fun i => ((WithLp.ofLp v) i).re) with hvRe_def
    set vIm : EuclideanSpace ℝ n :=
      WithLp.toLp 2 (fun i => ((WithLp.ofLp v) i).im) with hvIm_def
    -- Decompose `(T v) i = (S vRe) i + I · (S vIm) i` (cast to ℂ).
    have hTv : ∀ i, WithLp.ofLp (T v) i
        = ((WithLp.ofLp (S vRe)) i : ℂ) + Complex.I * ((WithLp.ofLp (S vIm)) i : ℂ) := by
      intro i
      show ((A.map (fun r : ℝ => (r : ℂ))) *ᵥ (WithLp.ofLp v)) i
          = ((A *ᵥ (WithLp.ofLp vRe)) i : ℂ) +
              Complex.I * ((A *ᵥ (WithLp.ofLp vIm)) i : ℂ)
      have hvRe_ofLp : WithLp.ofLp vRe = (fun j => ((WithLp.ofLp v) j).re) := rfl
      have hvIm_ofLp : WithLp.ofLp vIm = (fun j => ((WithLp.ofLp v) j).im) := rfl
      rw [hvRe_ofLp, hvIm_ofLp]
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
      -- Sum form: ∑ j, (A i j : ℂ) * (v j); RHS uses (v j) = re + I * im.
      -- Convert RHS to a sum, then match termwise.
      have h_re_sum : ((∑ j, A i j * ((WithLp.ofLp v) j).re : ℝ) : ℂ)
          = ∑ j, (A i j : ℂ) * (((WithLp.ofLp v) j).re : ℂ) := by
        push_cast; rfl
      have h_im_sum : ((∑ j, A i j * ((WithLp.ofLp v) j).im : ℝ) : ℂ)
          = ∑ j, (A i j : ℂ) * (((WithLp.ofLp v) j).im : ℂ) := by
        push_cast; rfl
      rw [h_re_sum, h_im_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      -- Termwise: (A i j : ℂ) * (v j) = (A i j : ℂ) * (v j).re + I * ((A i j : ℂ) * (v j).im).
      -- Use `re_add_im` then `ring` only on the LHS.
      set a : ℂ := (A i j : ℂ) with ha
      set re : ℝ := ((WithLp.ofLp v) j).re with hre
      set im : ℝ := ((WithLp.ofLp v) j).im with him
      have hvj : ((WithLp.ofLp v) j) = (re : ℂ) + (im : ℂ) * Complex.I :=
        (Complex.re_add_im _).symm
      rw [hvj]
      ring
    -- Pythagoras: ‖T v‖² = ‖S vRe‖² + ‖S vIm‖².
    have hsum_norm_sq : ‖T v‖ ^ 2 = ‖S vRe‖ ^ 2 + ‖S vIm‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hTv i]
      have hra : ‖((WithLp.ofLp (S vRe)) i : ℝ)‖ ^ 2 = ((WithLp.ofLp (S vRe)) i) ^ 2 := by
        rw [Real.norm_eq_abs, sq_abs]
      have hrb : ‖((WithLp.ofLp (S vIm)) i : ℝ)‖ ^ 2 = ((WithLp.ofLp (S vIm)) i) ^ 2 := by
        rw [Real.norm_eq_abs, sq_abs]
      rw [normSq_ofReal_add_I_mul_ofReal, hra, hrb]
    -- ‖v‖² = ‖vRe‖² + ‖vIm‖².
    have hv_norm_sq : ‖v‖ ^ 2 = ‖vRe‖ ^ 2 + ‖vIm‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hvRe_ofLp : (WithLp.ofLp vRe) i = ((WithLp.ofLp v) i).re := rfl
      have hvIm_ofLp : (WithLp.ofLp vIm) i = ((WithLp.ofLp v) i).im := rfl
      rw [hvRe_ofLp, hvIm_ofLp, sq_norm_eq_re_sq_add_im_sq]
      have hra : ‖((WithLp.ofLp v) i).re‖ ^ 2 = ((WithLp.ofLp v) i).re ^ 2 := by
        rw [Real.norm_eq_abs, sq_abs]
      have hrb : ‖((WithLp.ofLp v) i).im‖ ^ 2 = ((WithLp.ofLp v) i).im ^ 2 := by
        rw [Real.norm_eq_abs, sq_abs]
      rw [hra, hrb]
    -- Now combine via `‖S w‖ ≤ ‖S‖ · ‖w‖`.
    have hSvRe : ‖S vRe‖ ≤ ‖S‖ * ‖vRe‖ := S.le_opNorm _
    have hSvIm : ‖S vIm‖ ≤ ‖S‖ * ‖vIm‖ := S.le_opNorm _
    have hT_nn : 0 ≤ ‖T v‖ := norm_nonneg _
    have hS_nn : 0 ≤ ‖S‖ := ContinuousLinearMap.opNorm_nonneg _
    have hv_nn : 0 ≤ ‖v‖ := norm_nonneg _
    have hvRe_nn : 0 ≤ ‖vRe‖ := norm_nonneg _
    have hvIm_nn : 0 ≤ ‖vIm‖ := norm_nonneg _
    have hSvRe_nn : 0 ≤ ‖S vRe‖ := norm_nonneg _
    have hSvIm_nn : 0 ≤ ‖S vIm‖ := norm_nonneg _
    -- ‖T v‖² ≤ (‖S‖ * ‖v‖)².
    have hsq : ‖T v‖ ^ 2 ≤ (‖S‖ * ‖v‖) ^ 2 := by
      have hRe : ‖S vRe‖ ^ 2 ≤ ‖S‖ ^ 2 * ‖vRe‖ ^ 2 := by
        have := sq_le_sq' (by linarith : -(‖S‖ * ‖vRe‖) ≤ ‖S vRe‖) hSvRe
        nlinarith [this]
      have hIm : ‖S vIm‖ ^ 2 ≤ ‖S‖ ^ 2 * ‖vIm‖ ^ 2 := by
        have := sq_le_sq' (by linarith : -(‖S‖ * ‖vIm‖) ≤ ‖S vIm‖) hSvIm
        nlinarith [this]
      calc ‖T v‖ ^ 2 = ‖S vRe‖ ^ 2 + ‖S vIm‖ ^ 2 := hsum_norm_sq
        _ ≤ ‖S‖ ^ 2 * ‖vRe‖ ^ 2 + ‖S‖ ^ 2 * ‖vIm‖ ^ 2 := by linarith
        _ = ‖S‖ ^ 2 * (‖vRe‖ ^ 2 + ‖vIm‖ ^ 2) := by ring
        _ = ‖S‖ ^ 2 * ‖v‖ ^ 2 := by rw [← hv_norm_sq]
        _ = (‖S‖ * ‖v‖) ^ 2 := by ring
    -- Lift back to `‖T v‖ ≤ ‖S‖ · ‖v‖` from the squared form.
    have hbnd_nn : 0 ≤ ‖S‖ * ‖v‖ := mul_nonneg hS_nn hv_nn
    nlinarith [hsq, hT_nn, hbnd_nn, sq_nonneg (‖S‖ * ‖v‖ - ‖T v‖),
      sq_nonneg (‖S‖ * ‖v‖ + ‖T v‖)]
  · -- `‖S‖ ≤ ‖T‖`. For every real `w`, show `‖S w‖ ≤ ‖T‖ · ‖w‖`.
    refine ContinuousLinearMap.opNorm_le_bound _ (ContinuousLinearMap.opNorm_nonneg _) ?_
    intro w
    -- Complex-lift `w` and use `T`'s bound.
    set wC : EuclideanSpace ℂ n := realToComplexVec w with hwC_def
    have hwC_norm : ‖wC‖ = ‖w‖ := norm_realToComplexVec w
    -- `‖S w‖ = ‖T wC‖`.
    have hTwC : T wC = realToComplexVec (S w) := by
      apply (WithLp.linearEquiv 2 ℂ (m → ℂ)).injective
      funext i
      change (((A.map (fun r : ℝ => (r : ℂ))) *ᵥ (WithLp.ofLp wC)) i)
          = ((WithLp.ofLp (S w)) i : ℂ)
      have hwC_entry : WithLp.ofLp wC = (fun j => ((WithLp.ofLp w) j : ℂ)) := by
        funext j
        rw [hwC_def]
        rfl
      rw [hwC_entry]
      have h := map_ofReal_mulVec_realToComplexVec A w
      have h_apply := congrArg (fun f => f i) h
      simp only at h_apply
      rw [h_apply]
      rfl
    have hSw_norm : ‖S w‖ = ‖T wC‖ := by
      rw [hTwC, norm_realToComplexVec]
    rw [hSw_norm, ← hwC_norm]
    exact T.le_opNorm wC

end MapOfReal

end Matrix
