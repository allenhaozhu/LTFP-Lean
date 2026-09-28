/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.NTKGradientFlowResidual

/-!
# Antisymmetric (doubled) initialisation of the two-layer network

Given `k` sampled neurons `ω : Fin k → ℝᵈ × ℝ` (input weight and bias),
the *antisymmetric* initialisation is the width-`k + k` network whose
hidden units are two copies of the sample, with output weight `+1` on the
first copy and `-1` on the second copy.

This initialisation has two convenient properties:

* the network output vanishes identically, so the initial residual is
  `-y` and its norm is `‖y‖`, independent of the sample;
* the output weights satisfy `a_j ^ 2 = 1`, and the training kernel of the
  doubled network equals the empirical full NTK of the `k`-sample: the
  `1 / (k + k)` normalisation of the doubled sum cancels the duplication.

## Main definitions

* `antisymInitParam ω` — the doubled parameter in `Param d (k + k)`.
* `antisymInitBias ω` — the doubled bias vector.

## Main results

* `fullNet_antisymInit` — the doubled network is identically zero.
* `residualFullNet_antisymInit` and `norm_residualFullNet_antisymInit` —
  the initial residual is `-y`, with norm `‖y‖`.
* `abs_antisymInitParam_fst` — `|a_j| = 1`.
* `fullTrainingKernel_antisymInit` — the training kernel of the doubled
  network equals `empiricalFullNTK σ σ' xs ω`.
-/

namespace ProbabilityTheory

open BigOperators Real Matrix

variable {d n k : ℕ}

/-- Doubled parameter: two copies of the sampled input weights, with output
weights `+1` on the first copy and `-1` on the second copy. -/
noncomputable def antisymInitParam
    (ω : Fin k → EuclideanSpace ℝ (Fin d) × ℝ) : Param d (k + k) :=
  (Fin.append (fun _ => (1 : ℝ)) (fun _ => (-1 : ℝ)),
    Fin.append (fun i => (ω i).1) (fun i => (ω i).1))

/-- Doubled bias vector: two copies of the sampled biases. -/
noncomputable def antisymInitBias
    (ω : Fin k → EuclideanSpace ℝ (Fin d) × ℝ) : Fin (k + k) → ℝ :=
  Fin.append (fun i => (ω i).2) (fun i => (ω i).2)

/-- `Fin.append` on the second block, indexed through `Fin.addNat` (the form
produced by `Fin.sum_univ_add` when both blocks have the same length). -/
theorem fin_append_addNat_self {α : Type*} (u v : Fin k → α) (i : Fin k) :
    Fin.append u v (i.addNat k) = v i := by
  have h : i.addNat k = Fin.natAdd k i := by
    ext
    simp [Nat.add_comm]
  rw [h, Fin.append_right]

/-- The output weights of the doubled parameter have absolute value `1`. -/
theorem abs_antisymInitParam_fst
    (ω : Fin k → EuclideanSpace ℝ (Fin d) × ℝ) (j : Fin (k + k)) :
    |(antisymInitParam ω).1 j| = 1 := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp [antisymInitParam]
  · simp [antisymInitParam, fin_append_addNat_self]

/-- The output weights of the doubled parameter square to `1`. -/
theorem antisymInitParam_initParam
    (ω : Fin k → EuclideanSpace ℝ (Fin d) × ℝ) :
    InitParam (antisymInitParam ω).1 (antisymInitParam ω).2 := by
  intro j
  have h := abs_antisymInitParam_fst ω j
  rw [← sq_abs, h, one_pow]

/-- The antisymmetric network is identically zero. -/
theorem fullNet_antisymInit
    (σ : ℝ → ℝ) (ω : Fin k → EuclideanSpace ℝ (Fin d) × ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    fullNet σ (antisymInitBias ω) (antisymInitParam ω) x = 0 := by
  unfold fullNet
  rw [Fin.sum_univ_add]
  simp [antisymInitParam, antisymInitBias, Fin.append_left, fin_append_addNat_self]

/-- The initial residual of the antisymmetric network is `-y`. -/
theorem residualFullNet_antisymInit
    (σ : ℝ → ℝ) (ω : Fin k → EuclideanSpace ℝ (Fin d) × ℝ)
    (y : Fin n → ℝ) (xs : Fin n → EuclideanSpace ℝ (Fin d)) :
    residualFullNet σ (antisymInitBias ω) y xs (antisymInitParam ω) =
      -(EuclideanSpace.equiv (Fin n) ℝ).symm y := by
  ext i
  simp [residualFullNet_apply, fullNet_antisymInit]

/-- The initial residual of the antisymmetric network has norm `‖y‖`
(Euclidean norm of the label vector). -/
theorem norm_residualFullNet_antisymInit
    (σ : ℝ → ℝ) (ω : Fin k → EuclideanSpace ℝ (Fin d) × ℝ)
    (y : Fin n → ℝ) (xs : Fin n → EuclideanSpace ℝ (Fin d)) :
    ‖residualFullNet σ (antisymInitBias ω) y xs (antisymInitParam ω)‖ =
      ‖(EuclideanSpace.equiv (Fin n) ℝ).symm y‖ := by
  rw [residualFullNet_antisymInit, norm_neg]

/-- **Training kernel of the antisymmetric initialisation.**

The training kernel of the width-`k + k` doubled network coincides with the
empirical full NTK of the `k`-sample: the duplicated sums are divided by
`k + k`, which gives back the `1 / k` average. -/
theorem fullTrainingKernel_antisymInit
    (σ σ' : ℝ → ℝ) (ω : Fin k → EuclideanSpace ℝ (Fin d) × ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) :
    fullTrainingKernel σ σ' (antisymInitBias ω) (antisymInitParam ω) xs =
      empiricalFullNTK σ σ' xs ω := by
  ext r s
  show _ = (empiricalNTK σ xs ω + empiricalGradNTK σ' xs ω) r s
  rw [Matrix.add_apply]
  unfold fullTrainingKernel empiricalNTK empiricalGradNTK neuronNTK gradNeuronNTK
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [antisymInitParam, antisymInitBias, Fin.append_left, Fin.append_right]
  push_cast
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    simp
  · have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    simp only [neg_one_sq, one_pow, one_mul]
    field_simp
    have key : ∀ x : Fin k,
        σ' (inner ℝ (ω x).1 (xs r) + (ω x).2) * σ' (inner ℝ (ω x).1 (xs s) + (ω x).2) *
            inner ℝ (xs r) (xs s) =
          inner ℝ (xs r) (xs s) * σ' (inner ℝ (ω x).1 (xs r) + (ω x).2) *
            σ' (inner ℝ (ω x).1 (xs s) + (ω x).2) := fun x => by ring
    rw [Finset.sum_congr rfl (fun x _ => key x)]
    ring

end ProbabilityTheory
