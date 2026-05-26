/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.FullNetwork
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Explicit parameter gradient of the full network and Gram identity

**R4 NTK Part E3e.2 — full-network gradient (explicit) + Gram identity
with `fullTrainingKernel`.**

`FullNetwork.lean` defines `fullTrainingKernel σ σ' b θ xs` informally
as "the NTK at θ" — i.e., the Gram matrix of the parameter gradients of
`fullNet`. To use it in residual dynamics we need the corresponding
algebraic identity made explicit:

  `fullTrainingKernel σ σ' b θ xs r s`
    `= ⟨∇_θ fullNet(θ, x_r), ∇_θ fullNet(θ, x_s)⟩`.

This file defines the parameter gradient
`gradFullNet σ σ' b θ x : Param d m` *explicitly*, bypassing the Fréchet
derivative machinery, and proves the Gram identity above. The lemma
identifying `gradFullNet` with the actual Fréchet gradient of
`fullNet`, which would require differentiability of `σ` and `σ'`, is
deferred — it is not needed for the residual-dynamics arguments that
consume this Gram identity.

## Main definitions

* `gradFullNet σ σ' b θ x` — the explicit parameter gradient of
  `fullNet` at `(θ, x)`, with `a`-block
  `j ↦ (1/√m) · σ(⟨w_j, x⟩ + b_j)` and `w`-block
  `j ↦ (1/√m) · a_j · σ'(⟨w_j, x⟩ + b_j) · x`.

## Main results

* `gradFullNet_inner_eq_fullTrainingKernel` — the Gram identity
  `⟨∇fullNet θ x_r, ∇fullNet θ x_s⟩ = fullTrainingKernel σ σ' b θ xs r s`,
  with the inner product on `Param d m = (Fin m → ℝ) × (Fin m → ℝ^d)`
  written out as the sum of the `a`-block scalar product and the
  `w`-block inner product summed over `j`.
-/

namespace ProbabilityTheory

open BigOperators Real

variable {d : ℕ}

/-! ### Explicit parameter gradient -/

/-- **Explicit parameter gradient of `fullNet`.**

For `fullNet σ b θ x = (1/√m) · Σ_j a_j · σ(⟨w_j, x⟩ + b_j)`, the
parameter gradient at `(θ, x)` has two blocks:

* `a`-block: `∂fullNet/∂a_j = (1/√m) · σ(⟨w_j, x⟩ + b_j)` (a scalar
  for each `j`).
* `w`-block: `∂fullNet/∂w_j = (1/√m) · a_j · σ'(⟨w_j, x⟩ + b_j) · x`
  (a vector in `EuclideanSpace ℝ (Fin d)` for each `j`).

This definition is *purely algebraic* — it does not rely on Fréchet
differentiability of `σ` or `σ'`. The lemma identifying `gradFullNet`
with the actual Fréchet gradient under differentiability hypotheses is
deferred to a separate file. -/
noncomputable def gradFullNet
    {m : ℕ}
    (σ σ' : ℝ → ℝ)
    (b : Fin m → ℝ)
    (θ : Param d m)
    (x : EuclideanSpace ℝ (Fin d)) :
    Param d m :=
  ((fun j => (1 / Real.sqrt (m : ℝ)) * σ (inner ℝ (θ.2 j) x + b j)),
   (fun j => ((1 / Real.sqrt (m : ℝ)) * θ.1 j *
              σ' (inner ℝ (θ.2 j) x + b j)) • x))

/-! ### Gram identity -/

/-- **Gram identity: `⟨∇fullNet, ∇fullNet⟩ = fullTrainingKernel`.**

The inner product on `Param d m = (Fin m → ℝ) × (Fin m → ℝ^d)` is the
sum of the standard Euclidean inner product on each block:

  `⟨(a, w), (a', w')⟩`
    `= Σ_j a_j · a'_j + Σ_j ⟨w_j, w'_j⟩`.

Plugging `gradFullNet σ σ' b θ x_r` and `gradFullNet σ σ' b θ x_s` into
this formula and collecting the `(1/√m)²= 1/m` factors recovers the two
blocks of `fullTrainingKernel`:

* the `a`-block sum gives `(1/m) · Σ_j σ(z_{jr}) · σ(z_{js})` — the σ
  block of the training kernel;
* the `w`-block sum gives `(1/m) · Σ_j a_j² · σ'(z_{jr}) · σ'(z_{js})
  · ⟨x_r, x_s⟩` — the σ' block of the training kernel.

Here `z_{jr} := ⟨w_j, x_r⟩ + b_j`. -/
theorem gradFullNet_inner_eq_fullTrainingKernel
    {n m : ℕ}
    (σ σ' : ℝ → ℝ)
    (b : Fin m → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (θ : Param d m) (r s : Fin n)
    (hm : 0 < m) :
    (∑ j, (gradFullNet σ σ' b θ (xs r)).1 j *
            (gradFullNet σ σ' b θ (xs s)).1 j) +
    (∑ j, inner ℝ ((gradFullNet σ σ' b θ (xs r)).2 j)
                  ((gradFullNet σ σ' b θ (xs s)).2 j))
      = fullTrainingKernel σ σ' b θ xs r s := by
  classical
  -- Notation for the inner-product+bias arguments.
  -- Compute `(1/√m)² = 1/m` using `0 < m`.
  have hm_real_nn : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.le
  have hsqrt_sq : (1 / Real.sqrt (m : ℝ)) ^ 2 = 1 / (m : ℝ) := by
    have : (Real.sqrt (m : ℝ)) ^ 2 = (m : ℝ) := Real.sq_sqrt hm_real_nn
    field_simp
    -- Goal: `1 / Real.sqrt (m : ℝ) ^ 2 = 1 / (m : ℝ)` (after field_simp).
    rw [this]
  have hsqrt_mul : (1 / Real.sqrt (m : ℝ)) * (1 / Real.sqrt (m : ℝ))
      = 1 / (m : ℝ) := by
    have := hsqrt_sq
    rw [sq] at this
    exact this
  -- Unfold `gradFullNet`. The LHS reduces to:
  --   Σ_j (1/√m) σ(z_jr) · (1/√m) σ(z_js)
  -- + Σ_j ⟨ ((1/√m) a_j σ'(z_jr)) • x_r,
  --         ((1/√m) a_j σ'(z_js)) • x_s ⟩
  -- where z_jr := ⟨w_j, x_r⟩ + b_j and similarly z_js.
  unfold gradFullNet
  -- σ-block: rewrite product of (1/√m) factors as (1/m).
  have h_sigma_sum :
      ∑ j, (1 / Real.sqrt (m : ℝ)) * σ (inner ℝ (θ.2 j) (xs r) + b j) *
            ((1 / Real.sqrt (m : ℝ)) * σ (inner ℝ (θ.2 j) (xs s) + b j))
        = (1 / (m : ℝ)) *
            ∑ j, σ (inner ℝ (θ.2 j) (xs r) + b j) *
                  σ (inner ℝ (θ.2 j) (xs s) + b j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    -- Rearrange the four-way product.
    have :
        (1 / Real.sqrt (m : ℝ)) * σ (inner ℝ (θ.2 j) (xs r) + b j) *
          ((1 / Real.sqrt (m : ℝ)) * σ (inner ℝ (θ.2 j) (xs s) + b j))
          = ((1 / Real.sqrt (m : ℝ)) * (1 / Real.sqrt (m : ℝ))) *
              (σ (inner ℝ (θ.2 j) (xs r) + b j) *
               σ (inner ℝ (θ.2 j) (xs s) + b j)) := by ring
    rw [this, hsqrt_mul]
  -- σ'-block: pull scalars out of the inner product via
  -- `real_inner_smul_left` and `real_inner_smul_right`, then rewrite
  -- (1/√m)² · a_j² as (1/m) · a_j².
  have h_grad_sum :
      ∑ j,
        inner ℝ
          (((1 / Real.sqrt (m : ℝ)) * θ.1 j *
             σ' (inner ℝ (θ.2 j) (xs r) + b j)) • xs r)
          (((1 / Real.sqrt (m : ℝ)) * θ.1 j *
             σ' (inner ℝ (θ.2 j) (xs s) + b j)) • xs s)
        = (1 / (m : ℝ)) *
            ∑ j, θ.1 j ^ 2 *
                  σ' (inner ℝ (θ.2 j) (xs r) + b j) *
                  σ' (inner ℝ (θ.2 j) (xs s) + b j) *
                  inner ℝ (xs r) (xs s) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    -- Pull the left scalar out.
    rw [real_inner_smul_left, real_inner_smul_right]
    -- Goal:
    --   ((1/√m) * a_j * σ'(z_jr)) *
    --   (((1/√m) * a_j * σ'(z_js)) * ⟨xs r, xs s⟩)
    --   = (1/m) * (a_j^2 * σ'(z_jr) * σ'(z_js) * ⟨xs r, xs s⟩)
    have hreorg :
        ((1 / Real.sqrt (m : ℝ)) * θ.1 j *
             σ' (inner ℝ (θ.2 j) (xs r) + b j)) *
          (((1 / Real.sqrt (m : ℝ)) * θ.1 j *
             σ' (inner ℝ (θ.2 j) (xs s) + b j)) *
             inner ℝ (xs r) (xs s))
          = ((1 / Real.sqrt (m : ℝ)) * (1 / Real.sqrt (m : ℝ))) *
              (θ.1 j ^ 2 *
                σ' (inner ℝ (θ.2 j) (xs r) + b j) *
                σ' (inner ℝ (θ.2 j) (xs s) + b j) *
                inner ℝ (xs r) (xs s)) := by ring
    rw [hreorg, hsqrt_mul]
  -- Assemble both blocks against `fullTrainingKernel`.
  rw [h_sigma_sum, h_grad_sum]
  -- Unfold the RHS; both sides match definitionally.
  rfl

end ProbabilityTheory
