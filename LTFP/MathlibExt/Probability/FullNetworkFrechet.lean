/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.FullNetwork
import LTFP.MathlibExt.Probability.FullNetworkGradient
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Fréchet differentiability of `fullNet` and gradient identification

**R4 NTK Part E3e — Strategy 3A — Fréchet route.**

`FullNetwork.lean` defines the single-hidden-layer predictor
`fullNet σ b θ x = (1/√m) Σ_j a_j σ(⟨w_j, x⟩ + b_j)` and
`FullNetworkGradient.lean` defines the explicit parameter gradient
`gradFullNet σ σ' b θ x : Param d m` and proves the Gram identity
`⟨gradFullNet θ x_r, gradFullNet θ x_s⟩ = fullTrainingKernel θ x_r x_s`
*algebraically*, without any reference to Fréchet differentiability.

This file closes the outstanding differentiability claim: under the
hypothesis that `σ` is differentiable with derivative `deriv σ`, the
network `fullNet σ b · x` is Fréchet differentiable in `θ`, and its
Fréchet gradient (when paired against a tangent vector `v` via the
canonical inner product on `Param d m`) coincides with
`gradFullNet σ (deriv σ) b θ x`.

## Main results

* `fullNet_differentiable_param` — for every fixed input `x` and bias
  `b`, the map `θ ↦ fullNet σ b θ x` is Fréchet differentiable on
  `Param d m`.
* `fullNet_fderiv_eq` — the Fréchet derivative of `fullNet` at `θ`,
  evaluated on a tangent vector `v : Param d m`, equals the inner
  product `⟨gradFullNet σ (deriv σ) b θ x, v⟩` written out as the sum
  of an `a`-block scalar contribution and a `w`-block inner-product
  contribution.

Together with the Gram identity in `FullNetworkGradient.lean`, these
results justify calling `fullTrainingKernel σ (deriv σ) b θ xs` the
"NTK at the current parameter" — it is the Gram matrix of the
*actual* Fréchet gradients of `fullNet`.
-/

namespace ProbabilityTheory

open BigOperators Real

variable {d : ℕ}

/-! ### Auxiliary differentiability of building blocks -/

/-- Projecting onto the `a`-coordinate `j` is differentiable in `θ`. -/
private theorem differentiable_param_fst_apply
    {m : ℕ} (j : Fin m) :
    Differentiable ℝ (fun θ : Param d m => θ.1 j) := by
  fun_prop

/-- Projecting onto the `w`-coordinate `j` is differentiable in `θ`. -/
private theorem differentiable_param_snd_apply
    {m : ℕ} (j : Fin m) :
    Differentiable ℝ
      (fun θ : Param d m => θ.2 j) := by
  fun_prop

/-- `θ ↦ ⟨θ.2 j, x⟩` is differentiable in `θ`. -/
private theorem differentiable_inner_w
    {m : ℕ} (j : Fin m)
    (x : EuclideanSpace ℝ (Fin d)) :
    Differentiable ℝ
      (fun θ : Param d m => inner ℝ (θ.2 j) x) :=
  (differentiable_param_snd_apply (d := d) j).inner ℝ
    (differentiable_const x)

/-- `θ ↦ ⟨θ.2 j, x⟩ + b j` is differentiable in `θ`. -/
private theorem differentiable_preact
    {m : ℕ} (b : Fin m → ℝ) (j : Fin m)
    (x : EuclideanSpace ℝ (Fin d)) :
    Differentiable ℝ
      (fun θ : Param d m => inner ℝ (θ.2 j) x + b j) :=
  (differentiable_inner_w j x).add_const (b j)

/-! ### Theorem 1 — Fréchet differentiability of `fullNet` in `θ` -/

/-- **Fréchet differentiability of the full network in its parameters.**

If `σ : ℝ → ℝ` is differentiable, then for every fixed bias vector
`b` and input `x`, the map `θ ↦ fullNet σ b θ x` is Fréchet
differentiable on `Param d m = (Fin m → ℝ) × (Fin m → EuclideanSpace ℝ (Fin d))`.

The proof composes:
* projections `θ ↦ θ.1 j` and `θ ↦ θ.2 j` (linear and differentiable),
* the inner product `θ ↦ ⟨θ.2 j, x⟩` (bilinear with one slot fixed),
* addition with a constant bias `b j`,
* the activation `σ` (hypothesis),
* the product `θ ↦ θ.1 j · σ(⟨θ.2 j, x⟩ + b j)`,
* the finite sum over `j : Fin m`,
* multiplication by the scalar `1 / √m`. -/
theorem fullNet_differentiable_param
    {m : ℕ}
    (σ : ℝ → ℝ)
    (hσ_diff : Differentiable ℝ σ)
    (b : Fin m → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    Differentiable ℝ (fun θ : Param d m => fullNet σ b θ x) := by
  classical
  unfold fullNet
  have h_summand_diff : ∀ j : Fin m,
      Differentiable ℝ
        (fun θ : Param d m =>
          θ.1 j * σ (inner ℝ (θ.2 j) x + b j)) := by
    intro j
    have h_a : Differentiable ℝ (fun θ : Param d m => θ.1 j) :=
      differentiable_param_fst_apply j
    have h_pre :
        Differentiable ℝ
          (fun θ : Param d m => inner ℝ (θ.2 j) x + b j) :=
      differentiable_preact b j x
    have h_sigma :
        Differentiable ℝ
          (fun θ : Param d m => σ (inner ℝ (θ.2 j) x + b j)) :=
      hσ_diff.comp h_pre
    exact h_a.mul h_sigma
  have h_sum_diff :
      Differentiable ℝ
        (fun θ : Param d m =>
          ∑ j, θ.1 j * σ (inner ℝ (θ.2 j) x + b j)) :=
    Differentiable.fun_sum (u := Finset.univ)
      (fun j _ => h_summand_diff j)
  exact h_sum_diff.const_mul (1 / Real.sqrt (m : ℝ))

/-! ### Theorem 2 — Identification of the Fréchet derivative -/

/-- **Identification of the Fréchet derivative with `gradFullNet`.**

The Fréchet derivative of `fullNet σ b · x` at `θ`, applied as a
continuous linear functional to a tangent vector `v : Param d m`,
equals the canonical inner product of `gradFullNet σ (deriv σ) b θ x`
with `v`:

  `fderiv ℝ (fun θ' => fullNet σ b θ' x) θ v`
    `= Σ_j (gradFullNet …).1 j · v.1 j + Σ_j ⟨(gradFullNet …).2 j, v.2 j⟩`.

This is the precise sense in which `gradFullNet` IS the Fréchet
gradient: it is the vector dual to the linear functional `fderiv`
under the standard inner product on `Param d m`.

The proof computes `fderiv` summand by summand via the product rule
and chain rule, then assembles via linearity of `fderiv` under sums
and constant scalar multiplication. -/
theorem fullNet_fderiv_eq
    {m : ℕ}
    (σ : ℝ → ℝ)
    (hσ_diff : Differentiable ℝ σ)
    (b : Fin m → ℝ)
    (θ : Param d m)
    (x : EuclideanSpace ℝ (Fin d))
    (v : Param d m) :
    fderiv ℝ (fun θ' : Param d m => fullNet σ b θ' x) θ v =
      (∑ j, (gradFullNet σ (deriv σ) b θ x).1 j * v.1 j) +
      (∑ j, inner ℝ ((gradFullNet σ (deriv σ) b θ x).2 j) (v.2 j)) := by
  classical
  set c : ℝ := 1 / Real.sqrt (m : ℝ) with hc_def
  -- Differentiability of building blocks (at θ).
  have h_a_diff : ∀ j : Fin m,
      DifferentiableAt ℝ (fun θ' : Param d m => θ'.1 j) θ :=
    fun j => (differentiable_param_fst_apply j) θ
  have h_w_diff : ∀ j : Fin m,
      DifferentiableAt ℝ (fun θ' : Param d m => θ'.2 j) θ :=
    fun j => (differentiable_param_snd_apply j) θ
  have h_inner_diff : ∀ j : Fin m,
      DifferentiableAt ℝ
        (fun θ' : Param d m => inner ℝ (θ'.2 j) x) θ :=
    fun j => (differentiable_inner_w j x) θ
  have h_pre_diff : ∀ j : Fin m,
      DifferentiableAt ℝ
        (fun θ' : Param d m => inner ℝ (θ'.2 j) x + b j) θ :=
    fun j => (differentiable_preact b j x) θ
  have h_sigma_diff : ∀ j : Fin m,
      DifferentiableAt ℝ
        (fun θ' : Param d m => σ (inner ℝ (θ'.2 j) x + b j)) θ :=
    fun j => (hσ_diff.comp (differentiable_preact b j x)) θ
  have h_summand_diff : ∀ j : Fin m,
      DifferentiableAt ℝ
        (fun θ' : Param d m =>
          θ'.1 j * σ (inner ℝ (θ'.2 j) x + b j)) θ :=
    fun j => (h_a_diff j).mul (h_sigma_diff j)
  -- fderiv of projections (with the directional value at v).
  have h_fd_a : ∀ j : Fin m,
      fderiv ℝ (fun θ' : Param d m => θ'.1 j) θ v = v.1 j := by
    intro j
    -- θ ↦ θ.1 is the linear projection `fst`, and apply at `j` is a CLM too.
    have h1 : HasFDerivAt (fun θ' : Param d m => θ'.1)
        (ContinuousLinearMap.fst ℝ (Fin m → ℝ) _) θ :=
      hasFDerivAt_fst
    have h2 : HasFDerivAt (fun f : Fin m → ℝ => f j)
        (ContinuousLinearMap.proj j) θ.1 :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j).hasFDerivAt
    have h3 : HasFDerivAt (fun θ' : Param d m => θ'.1 j)
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) j).comp
          (ContinuousLinearMap.fst ℝ (Fin m → ℝ) _)) θ :=
      h2.comp θ h1
    rw [h3.fderiv]; rfl
  have h_fd_w : ∀ j : Fin m,
      fderiv ℝ (fun θ' : Param d m => θ'.2 j) θ v = v.2 j := by
    intro j
    have h1 : HasFDerivAt (fun θ' : Param d m => θ'.2)
        (ContinuousLinearMap.snd ℝ _ (Fin m → EuclideanSpace ℝ (Fin d))) θ :=
      hasFDerivAt_snd
    have h2 : HasFDerivAt
        (fun f : Fin m → EuclideanSpace ℝ (Fin d) => f j)
        (ContinuousLinearMap.proj (R := ℝ)
          (φ := fun _ : Fin m => EuclideanSpace ℝ (Fin d)) j) θ.2 :=
      (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin m => EuclideanSpace ℝ (Fin d)) j).hasFDerivAt
    have h3 : HasFDerivAt (fun θ' : Param d m => θ'.2 j)
        ((ContinuousLinearMap.proj (R := ℝ)
            (φ := fun _ : Fin m => EuclideanSpace ℝ (Fin d)) j).comp
          (ContinuousLinearMap.snd ℝ _ (Fin m → EuclideanSpace ℝ (Fin d))))
        θ :=
      h2.comp θ h1
    rw [h3.fderiv]; rfl
  -- fderiv of the pre-activation θ ↦ ⟨θ.2 j, x⟩ + b j at direction v.
  have h_fd_inner : ∀ j : Fin m,
      fderiv ℝ (fun θ' : Param d m => inner ℝ (θ'.2 j) x) θ v =
        inner ℝ (v.2 j) x := by
    intro j
    -- fderiv_inner_apply: ⟨fderiv ℝ (θ' ↦ θ'.2 j) θ v, x⟩ + ⟨θ.2 j, 0⟩
    rw [fderiv_inner_apply ℝ (h_w_diff j) (differentiableAt_const x)]
    rw [fderiv_fun_const]
    rw [h_fd_w j]
    simp
  have h_fd_pre : ∀ j : Fin m,
      fderiv ℝ
        (fun θ' : Param d m => inner ℝ (θ'.2 j) x + b j) θ v =
        inner ℝ (v.2 j) x := by
    intro j
    rw [show (fun θ' : Param d m => inner ℝ (θ'.2 j) x + b j) =
            (fun θ' : Param d m => inner ℝ (θ'.2 j) x) +
              (fun _ : Param d m => b j) from rfl]
    rw [fderiv_add (h_inner_diff j) (differentiableAt_const (b j))]
    rw [fderiv_fun_const]
    rw [ContinuousLinearMap.add_apply]
    simp
    exact h_fd_inner j
  -- fderiv of σ(pre) via chain rule.
  have h_fd_sigma : ∀ j : Fin m,
      fderiv ℝ
        (fun θ' : Param d m => σ (inner ℝ (θ'.2 j) x + b j)) θ v =
        deriv σ (inner ℝ (θ.2 j) x + b j) * inner ℝ (v.2 j) x := by
    intro j
    have h_sigma_d : HasDerivAt σ (deriv σ (inner ℝ (θ.2 j) x + b j))
        (inner ℝ (θ.2 j) x + b j) := (hσ_diff _).hasDerivAt
    have h_pre_d : HasFDerivAt
        (fun θ' : Param d m => inner ℝ (θ'.2 j) x + b j)
        (fderiv ℝ
          (fun θ' : Param d m => inner ℝ (θ'.2 j) x + b j) θ) θ :=
      (h_pre_diff j).hasFDerivAt
    have h_comp := h_sigma_d.comp_hasFDerivAt (h₂ := σ) θ h_pre_d
    have : fderiv ℝ
        (σ ∘ (fun θ' : Param d m => inner ℝ (θ'.2 j) x + b j)) θ =
        (deriv σ (inner ℝ (θ.2 j) x + b j)) •
          fderiv ℝ
            (fun θ' : Param d m => inner ℝ (θ'.2 j) x + b j) θ :=
      h_comp.fderiv
    show fderiv ℝ
        ((fun y => σ y) ∘
          (fun θ' : Param d m => inner ℝ (θ'.2 j) x + b j)) θ v = _
    rw [this]
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [h_fd_pre j]
  -- fderiv of the summand F j = (θ' ↦ θ'.1 j * σ(pre)) by product rule.
  have h_fd_F : ∀ j : Fin m,
      fderiv ℝ
        (fun θ' : Param d m =>
          θ'.1 j * σ (inner ℝ (θ'.2 j) x + b j)) θ v =
        v.1 j * σ (inner ℝ (θ.2 j) x + b j) +
        θ.1 j *
          (deriv σ (inner ℝ (θ.2 j) x + b j) *
            inner ℝ (v.2 j) x) := by
    intro j
    rw [fderiv_fun_mul (h_a_diff j) (h_sigma_diff j)]
    rw [ContinuousLinearMap.add_apply]
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
    rw [h_fd_a j, h_fd_sigma j]
    simp [smul_eq_mul]
    ring
  -- fderiv distributes over the finite sum.
  have h_sum_diff_at :
      DifferentiableAt ℝ
        (fun θ' : Param d m =>
          ∑ j, θ'.1 j * σ (inner ℝ (θ'.2 j) x + b j)) θ :=
    DifferentiableAt.fun_sum (u := Finset.univ)
      (fun j _ => h_summand_diff j)
  have h_fd_sum :
      fderiv ℝ
        (fun θ' : Param d m =>
          ∑ j, θ'.1 j * σ (inner ℝ (θ'.2 j) x + b j)) θ v =
        ∑ j,
          fderiv ℝ
            (fun θ' : Param d m =>
              θ'.1 j * σ (inner ℝ (θ'.2 j) x + b j)) θ v := by
    rw [fderiv_fun_sum (u := Finset.univ)
        (fun j _ => h_summand_diff j)]
    exact ContinuousLinearMap.sum_apply _ _ _
  -- Pull out the constant `c = 1/√m`.
  have h_fullNet_fd :
      fderiv ℝ (fun θ' : Param d m => fullNet σ b θ' x) θ v =
        c * fderiv ℝ
          (fun θ' : Param d m =>
            ∑ j, θ'.1 j * σ (inner ℝ (θ'.2 j) x + b j)) θ v := by
    show fderiv ℝ
        (fun θ' : Param d m =>
          c * ∑ j, θ'.1 j * σ (inner ℝ (θ'.2 j) x + b j)) θ v = _
    rw [fderiv_const_mul h_sum_diff_at c]
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
  -- Assemble.
  rw [h_fullNet_fd, h_fd_sum]
  -- Substitute the per-summand explicit fderiv.
  have h_rhs :
      ∑ j,
        fderiv ℝ
          (fun θ' : Param d m =>
            θ'.1 j * σ (inner ℝ (θ'.2 j) x + b j)) θ v =
      ∑ j, (v.1 j * σ (inner ℝ (θ.2 j) x + b j) +
            θ.1 j *
              (deriv σ (inner ℝ (θ.2 j) x + b j) *
                inner ℝ (v.2 j) x)) :=
    Finset.sum_congr rfl (fun j _ => h_fd_F j)
  rw [h_rhs]
  rw [Finset.sum_add_distrib]
  rw [mul_add]
  -- Unfold gradFullNet.
  unfold gradFullNet
  simp only
  congr 1
  · -- a-block: c * Σ j, v.1 j * σ(z_j) = Σ j, (c * σ(z_j)) * v.1 j
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  · -- w-block: c * Σ j, θ.1 j * (σ'(z_j) * ⟨v.2 j, x⟩)
    --        = Σ j, ⟨(c * θ.1 j * σ'(z_j)) • x, v.2 j⟩
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [real_inner_smul_left]
    rw [real_inner_comm x (v.2 j)]
    ring

end ProbabilityTheory
