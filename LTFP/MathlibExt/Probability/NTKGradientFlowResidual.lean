/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.FullNetworkFrechet
import LTFP.MathlibExt.Probability.NTKLinearizedRKHS
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Residual ODE for `fullNet` along an explicit gradient flow on `[0, T]`

The parameter space `Param d m` carries the sup norm, so Mathlib's
`gradient` is not available. We therefore write gradient flow on the
squared loss explicitly through the vector field

  `gfFieldFullNet σ b y xs θ = ∑ i, (y i - fullNet σ b θ (xs i)) • gradFullNet … (xs i)`,

and certify that it is the negative gradient for the blockwise Euclidean
pairing `LTFP.paramInner` (`fderiv_sqLossFullNet_apply`).

All derivative statements are one-sided and pointwise in `t`, so they
apply to a trajectory defined only on a compact interval `[0, T]`.

## Main definitions

* `sqLossFullNet` — the squared loss `(1/2) ∑ i (y i - fullNet σ b θ (xs i))²`.
* `gfFieldFullNet` — the explicit negative-gradient vector field.
* `residualFullNet` — the residual `fullNet σ b θ (xs i) - y i` as a
  vector of `EuclideanSpace ℝ (Fin n)`.

## Main results

* `fullTrainingKernel_isHermitian` — the training kernel is symmetric.
* `fderiv_sqLossFullNet_apply` — `fderiv L θ v = - paramInner (gfFieldFullNet θ) v`.
* `hasDerivWithinAt_residualFullNet` — along the flow, the residual
  satisfies `r' = -K(θ t) r` (one-sided, pointwise in `t`).
* `residualFullNet_ode_on_Icc` — the same statement on `[0, T)`.
* `continuousOn_residualFullNet` — continuity of the residual on a set
  where the trajectory is continuous.
-/

namespace ProbabilityTheory

open BigOperators Real Matrix LTFP

variable {d n m : ℕ}

/-! ### Definitions -/

/-- Squared loss of `fullNet` on the training set `(xs, y)`. -/
noncomputable def sqLossFullNet
    (σ : ℝ → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) (θ : Param d m) : ℝ :=
  ∑ i, (1 / 2 : ℝ) * (y i - fullNet σ b θ (xs i)) ^ 2

/-- Explicit negative-gradient vector field of `sqLossFullNet`. -/
noncomputable def gfFieldFullNet
    (σ : ℝ → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) (θ : Param d m) : Param d m :=
  ∑ i, (y i - fullNet σ b θ (xs i)) • gradFullNet σ (deriv σ) b θ (xs i)

/-- Residual vector `fullNet σ b θ (xs i) - y i`, as a Euclidean vector. -/
noncomputable def residualFullNet
    (σ : ℝ → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) (θ : Param d m) :
    EuclideanSpace ℝ (Fin n) :=
  (EuclideanSpace.equiv (Fin n) ℝ).symm (fun i => fullNet σ b θ (xs i) - y i)

@[simp]
theorem residualFullNet_apply
    (σ : ℝ → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) (θ : Param d m) (i : Fin n) :
    residualFullNet σ b y xs θ i = fullNet σ b θ (xs i) - y i := rfl

/-! ### Symmetry of the training kernel -/

/-- The dynamic training kernel is symmetric. -/
theorem fullTrainingKernel_isHermitian
    (σ σ' : ℝ → ℝ) (b : Fin m → ℝ) (θ : Param d m)
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) :
    (fullTrainingKernel σ σ' b θ xs).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [star_trivial, fullTrainingKernel]
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  · congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [real_inner_comm (xs i) (xs j)]
    ring

/-! ### Blockwise pairing -/

/-- `paramInner` is symmetric. -/
theorem paramInner_comm' (u v : Param d m) : paramInner u v = paramInner v u := by
  unfold paramInner
  congr 1
  · exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · exact Finset.sum_congr rfl fun j _ => real_inner_comm _ _

/-- The Fréchet derivative of one network output, applied to `v`, is the
pairing of the explicit gradient with `v`. -/
theorem fderiv_fullNet_apply_eq_paramInner
    (σ : ℝ → ℝ) (hσ : Differentiable ℝ σ) (b : Fin m → ℝ)
    (θ : Param d m) (x : EuclideanSpace ℝ (Fin d)) (v : Param d m) :
    fderiv ℝ (fun θ' : Param d m => fullNet σ b θ' x) θ v =
      paramInner (gradFullNet σ (deriv σ) b θ x) v :=
  fullNet_fderiv_eq σ hσ b θ x v

/-- Pairing the gradient at `xs i` with the flow field gives
`∑ k, K i k * (y k - fullNet … (xs k))`. -/
theorem paramInner_gradFullNet_gfFieldFullNet
    (σ : ℝ → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) (θ : Param d m) (hm : 0 < m)
    (i : Fin n) :
    paramInner (gradFullNet σ (deriv σ) b θ (xs i)) (gfFieldFullNet σ b y xs θ) =
      ∑ k, fullTrainingKernel σ (deriv σ) b θ xs i k *
        (y k - fullNet σ b θ (xs k)) := by
  unfold gfFieldFullNet
  rw [paramInner_finset_sum_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show paramInner (gradFullNet σ (deriv σ) b θ (xs i))
        (gradFullNet σ (deriv σ) b θ (xs k)) =
      fullTrainingKernel σ (deriv σ) b θ xs i k from
    gradFullNet_inner_eq_fullTrainingKernel σ (deriv σ) b xs θ i k hm]
  ring

/-! ### The flow field is the negative gradient -/

/-- Derivative of the squared loss as a `HasFDerivAt` statement. -/
theorem hasFDerivAt_sqLossFullNet
    (σ : ℝ → ℝ) (hσ : Differentiable ℝ σ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) (θ : Param d m) :
    HasFDerivAt (sqLossFullNet σ b y xs)
      (∑ i, (-(y i - fullNet σ b θ (xs i))) •
        fderiv ℝ (fun θ' : Param d m => fullNet σ b θ' (xs i)) θ) θ := by
  have h : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      HasFDerivAt (fun θ' : Param d m => (1 / 2 : ℝ) * (y i - fullNet σ b θ' (xs i)) ^ 2)
        ((-(y i - fullNet σ b θ (xs i))) •
          fderiv ℝ (fun θ' : Param d m => fullNet σ b θ' (xs i)) θ) θ := by
    intro i _
    have hf : HasFDerivAt (fun θ' : Param d m => fullNet σ b θ' (xs i))
        (fderiv ℝ (fun θ' : Param d m => fullNet σ b θ' (xs i)) θ) θ :=
      (fullNet_differentiable_param σ hσ b (xs i) θ).hasFDerivAt
    have hg : HasDerivAt (fun s : ℝ => (1 / 2 : ℝ) * (y i - s) ^ 2)
        (-(y i - fullNet σ b θ (xs i))) (fullNet σ b θ (xs i)) := by
      have h1 : HasDerivAt (fun s : ℝ => y i - s) (-1) (fullNet σ b θ (xs i)) := by
        simpa using (hasDerivAt_id (fullNet σ b θ (xs i))).const_sub (y i)
      have h2 := (h1.pow 2).const_mul (1 / 2 : ℝ)
      convert h2 using 1
      push_cast
      ring
    have hc := hg.comp_hasFDerivAt θ hf
    exact hc
  have := HasFDerivAt.sum h
  convert this using 1
  funext θ'
  simp [sqLossFullNet]

/-- **The flow field is `-∇L` for the blockwise pairing.**
`fderiv L θ v = - paramInner (gfFieldFullNet θ) v`. -/
theorem fderiv_sqLossFullNet_apply
    (σ : ℝ → ℝ) (hσ : Differentiable ℝ σ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) (θ v : Param d m) :
    fderiv ℝ (sqLossFullNet σ b y xs) θ v =
      -paramInner (gfFieldFullNet σ b y xs θ) v := by
  rw [(hasFDerivAt_sqLossFullNet σ hσ b y xs θ).fderiv, paramInner_comm']
  unfold gfFieldFullNet
  rw [paramInner_finset_sum_smul, ← Finset.sum_neg_distrib,
    ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.smul_apply, smul_eq_mul,
    fderiv_fullNet_apply_eq_paramInner σ hσ, paramInner_comm']
  ring

/-! ### Residual ODE, one-sided and pointwise in `t` -/

/-- Coordinatewise residual ODE within an arbitrary set `s`. -/
theorem hasDerivWithinAt_residualFullNet_coord
    (σ : ℝ → ℝ) (hσ : Differentiable ℝ σ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) (hm : 0 < m)
    (θ : ℝ → Param d m) (s : Set ℝ) (t : ℝ)
    (hθ : HasDerivWithinAt θ (gfFieldFullNet σ b y xs (θ t)) s t) (i : Fin n) :
    HasDerivWithinAt (fun u => fullNet σ b (θ u) (xs i) - y i)
      (-((fullTrainingKernel σ (deriv σ) b (θ t) xs) *ᵥ
        (fun k => fullNet σ b (θ t) (xs k) - y k)) i) s t := by
  have hf : HasFDerivAt (fun θ' : Param d m => fullNet σ b θ' (xs i))
      (fderiv ℝ (fun θ' : Param d m => fullNet σ b θ' (xs i)) (θ t)) (θ t) :=
    (fullNet_differentiable_param σ hσ b (xs i) (θ t)).hasFDerivAt
  have hc := (hf.comp_hasDerivWithinAt t hθ).sub_const (y i)
  convert hc using 1
  rw [fderiv_fullNet_apply_eq_paramInner σ hσ,
    paramInner_gradFullNet_gfFieldFullNet σ b y xs (θ t) hm i]
  simp only [mulVec, dotProduct]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- **Residual ODE (G1a).** If the trajectory has the explicit
gradient-flow derivative within `s` at `t`, then the Euclidean residual
satisfies `r'(t) = -K(θ t) r(t)` within `s` at `t`. -/
theorem hasDerivWithinAt_residualFullNet
    (σ : ℝ → ℝ) (hσ : Differentiable ℝ σ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) (hm : 0 < m)
    (θ : ℝ → Param d m) (s : Set ℝ) (t : ℝ)
    (hθ : HasDerivWithinAt θ (gfFieldFullNet σ b y xs (θ t)) s t) :
    HasDerivWithinAt (fun u => residualFullNet σ b y xs (θ u))
      (-(Matrix.toEuclideanLin (fullTrainingKernel σ (deriv σ) b (θ t) xs))
        (residualFullNet σ b y xs (θ t))) s t := by
  have hpi : HasDerivWithinAt (fun u => fun i => fullNet σ b (θ u) (xs i) - y i)
      (-((fullTrainingKernel σ (deriv σ) b (θ t) xs) *ᵥ
        (fun k => fullNet σ b (θ t) (xs k) - y k))) s t :=
    hasDerivWithinAt_pi.2 fun i =>
      hasDerivWithinAt_residualFullNet_coord σ hσ b y xs hm θ s t hθ i
  have hE := (EuclideanSpace.equiv (Fin n) ℝ).symm.hasFDerivAt.comp_hasDerivWithinAt t hpi
  convert hE using 1

/-- **Residual ODE on `[0, T)` (G1a, interval form).** -/
theorem residualFullNet_ode_on_Icc
    (σ : ℝ → ℝ) (hσ : Differentiable ℝ σ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) (hm : 0 < m)
    (θ : ℝ → Param d m) (T : ℝ)
    (hθ : ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt θ (gfFieldFullNet σ b y xs (θ t)) (Set.Ici t) t) :
    ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun u => residualFullNet σ b y xs (θ u))
        (-(Matrix.toEuclideanLin (fullTrainingKernel σ (deriv σ) b (θ t) xs))
          (residualFullNet σ b y xs (θ t))) (Set.Ici t) t :=
  fun t ht => hasDerivWithinAt_residualFullNet σ hσ b y xs hm θ _ t (hθ t ht)

/-! ### Continuity of the residual -/

/-- `fullNet` is continuous in the parameters for a continuous activation. -/
theorem continuous_fullNet_param
    (σ : ℝ → ℝ) (hσ : Continuous σ) (b : Fin m → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    Continuous (fun θ : Param d m => fullNet σ b θ x) := by
  unfold fullNet
  fun_prop

/-- **Continuity of the residual (G1d).** -/
theorem continuousOn_residualFullNet
    (σ : ℝ → ℝ) (hσ : Continuous σ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (θ : ℝ → Param d m) (s : Set ℝ) (hθ : ContinuousOn θ s) :
    ContinuousOn (fun u => residualFullNet σ b y xs (θ u)) s := by
  have hpi : ContinuousOn (fun u => fun i => fullNet σ b (θ u) (xs i) - y i) s :=
    continuousOn_pi.2 fun i =>
      ((continuous_fullNet_param σ hσ b (xs i)).comp_continuousOn hθ).sub
        continuousOn_const
  exact (EuclideanSpace.equiv (Fin n) ℝ).symm.continuous.comp_continuousOn hpi

/-- Continuity of the residual on `[0, T]`. -/
theorem continuousOn_Icc_residualFullNet
    (σ : ℝ → ℝ) (hσ : Continuous σ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (θ : ℝ → Param d m) (T : ℝ) (hθ : ContinuousOn θ (Set.Icc 0 T)) :
    ContinuousOn (fun u => residualFullNet σ b y xs (θ u)) (Set.Icc 0 T) :=
  continuousOn_residualFullNet σ hσ b y xs θ _ hθ

end ProbabilityTheory
