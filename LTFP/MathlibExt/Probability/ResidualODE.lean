/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.FullNetwork
import LTFP.MathlibExt.Probability.FullNetworkGradient
import LTFP.MathlibExt.Probability.FullNetworkFrechet
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Residual ODE from gradient flow on the squared loss

**R4 NTK Option A.1 — derivation of the parametric residual ODE
`r'(t) = -K(θ(t)) · r(t)` from gradient flow on the squared loss for the
single-hidden-layer `fullNet`.**

This is the deterministic core of NTK lazy training: when the parameter
trajectory `θ : ℝ → Param d m` follows gradient flow on the squared loss
`L(θ) := (1/2) Σ_i (y_i - fullNet σ b θ (xs i))²`, the residual
`r_i(t) := y_i - fullNet σ b (θ t) (xs i)` evolves linearly under the
dynamic training kernel `K(θ) := fullTrainingKernel σ (deriv σ) b θ xs`,

  `r'(t) = -K(θ(t)) · r(t)`.

The strategy:

1. **Chain rule** (`HasFDerivAt.comp_hasDerivAt`):
   `d/dt fullNet σ b (θ t) (xs i) = fderiv L_i (θ t) (deriv θ t)`,
   where `L_i := fun θ' => fullNet σ b θ' (xs i)`.

2. **Strategy 3A** (`fullNet_fderiv_eq`): the Fréchet derivative of
   `L_i` at `θ t`, applied to a tangent vector `v`, is the canonical
   inner product on `Param d m` against `gradFullNet σ (deriv σ) b (θ t) (xs i)`.

3. **Substitute the gradient flow** `deriv θ t =
     ∑_k r_k(t) • gradFullNet σ (deriv σ) b (θ t) (xs k)`. Bilinearity
   of the Param-inner product turns the sum into
   `∑_k r_k(t) · ⟨gradFullNet i, gradFullNet k⟩`.

4. **Gram identity** (`gradFullNet_inner_eq_fullTrainingKernel`):
   each inner product `⟨gradFullNet i, gradFullNet k⟩` equals
   `fullTrainingKernel σ (deriv σ) b (θ t) xs i k`.

5. The resulting `∑_k K i k · r_k` is exactly the `i`-th entry of
   `(K *ᵥ r)`, so `d/dt fullNet = (K · r)_i`. Subtracting from the
   constant `y_i` flips the sign and gives the residual ODE.

## Main result

* `residual_ode_from_gradient_flow` — the residual ODE
  `r'(t) = -K(θ(t)) · r(t)` from squared-loss gradient flow on `fullNet`.
-/

namespace ProbabilityTheory

open BigOperators Real Matrix

variable {d : ℕ}

/-- **Residual ODE from squared-loss gradient flow on `fullNet`.**

For a single-hidden-layer network `fullNet σ b θ x`, the squared loss
`L(θ) := (1/2) Σ_i (y_i - fullNet σ b θ (xs i))²` has gradient
`∇L(θ) = -Σ_i (y_i - fullNet σ b θ (xs i)) · gradFullNet σ (deriv σ) b θ (xs i)`.

Under gradient flow `θ'(t) = -∇L(θ(t))`, the residual
`r_i(t) := y_i - fullNet σ b (θ t) (xs i)` satisfies the linear ODE

  `r_i'(t) = -(K(θ(t)) *ᵥ r(t))_i`,

where `K(θ) := fullTrainingKernel σ (deriv σ) b θ xs` is the dynamic
training kernel of `FullNetwork.lean`.

The hypothesis `hθ_ODE` is stated in the form
`deriv θ t = ∑_i r_i(t) • gradFullNet …`, which is `-∇L(θ t)` — i.e.,
the gradient-flow hypothesis with the sign absorbed into the
representation of the gradient.

Differentiability of `σ` is required so that the explicit gradient
`gradFullNet σ (deriv σ) …` coincides with the actual Fréchet gradient
of `fullNet`. -/
theorem residual_ode_from_gradient_flow
    {n m : ℕ}
    (σ : ℝ → ℝ)
    (hσ_diff : Differentiable ℝ σ)
    (b : Fin m → ℝ)
    (y : Fin n → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (θ : ℝ → Param d m)
    (hθ_diff : Differentiable ℝ θ)
    (hθ_ODE : ∀ t, deriv θ t =
      ∑ i, (y i - fullNet σ b (θ t) (xs i)) •
        gradFullNet σ (deriv σ) b (θ t) (xs i))
    (hm : 0 < m)
    (t : ℝ) (i : Fin n) :
    deriv (fun s => y i - fullNet σ b (θ s) (xs i)) t =
      -(fullTrainingKernel σ (deriv σ) b (θ t) xs).mulVec
        (fun j => y j - fullNet σ b (θ t) (xs j)) i := by
  classical
  -- Abbreviations.
  set r : Fin n → ℝ := fun j => y j - fullNet σ b (θ t) (xs j) with hr_def
  set g : Fin n → Param d m := fun k => gradFullNet σ (deriv σ) b (θ t) (xs k)
    with hg_def
  -- Step 1: `deriv (fun s => y i - fullNet σ b (θ s) (xs i)) t = -deriv (...) t`.
  -- Reduce to computing `deriv (fun s => fullNet σ b (θ s) (xs i)) t`.
  rw [deriv_const_sub]
  -- Step 2: chain rule. Let `L_i := fun θ' => fullNet σ b θ' (xs i)`.
  -- Then `fun s => fullNet σ b (θ s) (xs i) = L_i ∘ θ`, and
  -- `deriv (L_i ∘ θ) t = fderiv ℝ L_i (θ t) (deriv θ t)`.
  have hL_diff :
      Differentiable ℝ (fun θ' : Param d m => fullNet σ b θ' (xs i)) :=
    fullNet_differentiable_param σ hσ_diff b (xs i)
  have hL_fda : HasFDerivAt
      (fun θ' : Param d m => fullNet σ b θ' (xs i))
      (fderiv ℝ (fun θ' : Param d m => fullNet σ b θ' (xs i)) (θ t)) (θ t) :=
    (hL_diff (θ t)).hasFDerivAt
  have hθ_hda : HasDerivAt θ (deriv θ t) t := (hθ_diff t).hasDerivAt
  have h_chain : HasDerivAt
      ((fun θ' : Param d m => fullNet σ b θ' (xs i)) ∘ θ)
      (fderiv ℝ (fun θ' : Param d m => fullNet σ b θ' (xs i)) (θ t)
        (deriv θ t)) t :=
    hL_fda.comp_hasDerivAt t hθ_hda
  -- Convert from `(L_i ∘ θ)` to `fun s => fullNet σ b (θ s) (xs i)` (defeq).
  have h_chain' : HasDerivAt
      (fun s => fullNet σ b (θ s) (xs i))
      (fderiv ℝ (fun θ' : Param d m => fullNet σ b θ' (xs i)) (θ t)
        (deriv θ t)) t := h_chain
  -- Convert to deriv-equation form.
  rw [h_chain'.deriv]
  -- Step 3: substitute the gradient-flow ODE.
  rw [hθ_ODE t]
  -- The argument is now `∑ k, r k • g k`.
  -- Step 4: CLM distributes over `∑` and pulls `•` into scalar `*`.
  --   fderiv ℝ L_i (θ t) (∑ k, r k • g k)
  --     = ∑ k, fderiv ℝ L_i (θ t) (r k • g k)
  --     = ∑ k, r k • fderiv ℝ L_i (θ t) (g k)
  --     = ∑ k, r k * fderiv ℝ L_i (θ t) (g k).
  set L : Param d m →L[ℝ] ℝ :=
    fderiv ℝ (fun θ' : Param d m => fullNet σ b θ' (xs i)) (θ t) with hL_def
  show -(L (∑ k, (y k - fullNet σ b (θ t) (xs k)) •
        gradFullNet σ (deriv σ) b (θ t) (xs k))) = _
  -- Fold `r` and `g` into the sum.
  have h_sum_rewrite :
      (∑ k, (y k - fullNet σ b (θ t) (xs k)) •
        gradFullNet σ (deriv σ) b (θ t) (xs k))
        = ∑ k, r k • g k := by
    refine Finset.sum_congr rfl ?_
    intro k _
    rfl
  rw [h_sum_rewrite]
  -- CLM is additive over finite sums.
  rw [map_sum L (fun k => r k • g k) Finset.univ]
  -- Each summand: L (r k • g k) = r k • L (g k) = r k * L (g k).
  have h_each : ∀ k : Fin n, L (r k • g k) = r k * L (g k) := by
    intro k
    rw [L.map_smul]
    rfl
  -- Step 5: identify `L (g k)` with the Param-inner product against `g i`,
  -- using Strategy 3A (`fullNet_fderiv_eq`).
  have h_L_apply : ∀ k : Fin n,
      L (g k) =
        (∑ j, (gradFullNet σ (deriv σ) b (θ t) (xs i)).1 j * (g k).1 j) +
        (∑ j, inner ℝ
            ((gradFullNet σ (deriv σ) b (θ t) (xs i)).2 j) ((g k).2 j)) := by
    intro k
    -- Direct application of `fullNet_fderiv_eq`.
    have h := fullNet_fderiv_eq (σ := σ) (m := m)
      hσ_diff b (θ t) (xs i) (g k)
    exact h
  -- Step 6: apply the Gram identity to identify the RHS with K i k.
  -- For each k, the inner product equals fullTrainingKernel σ (deriv σ) b (θ t) xs i k.
  have h_Gram : ∀ k : Fin n,
      L (g k) = fullTrainingKernel σ (deriv σ) b (θ t) xs i k := by
    intro k
    rw [h_L_apply k]
    -- Unfold `g k` to the literal `gradFullNet ... (xs k)` form.
    show (∑ j, (gradFullNet σ (deriv σ) b (θ t) (xs i)).1 j *
            (gradFullNet σ (deriv σ) b (θ t) (xs k)).1 j) +
         (∑ j, inner ℝ
            ((gradFullNet σ (deriv σ) b (θ t) (xs i)).2 j)
            ((gradFullNet σ (deriv σ) b (θ t) (xs k)).2 j))
        = fullTrainingKernel σ (deriv σ) b (θ t) xs i k
    exact gradFullNet_inner_eq_fullTrainingKernel σ (deriv σ) b xs (θ t) i k hm
  -- Step 7: combine. The sum becomes `∑ k, r k * K i k = (K *ᵥ r) i`.
  have h_sum_eq :
      (∑ k, L (r k • g k))
        = ∑ k, r k * fullTrainingKernel σ (deriv σ) b (θ t) xs i k := by
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [h_each k, h_Gram k]
  rw [h_sum_eq]
  -- Identify `∑ k, r k * K i k` with `(K *ᵥ r) i` (modulo the symmetry of `K i k * r k`).
  -- `(K *ᵥ r) i = (fun j => K i j) ⬝ᵥ r = ∑ k, K i k * r k`.
  have h_mulVec :
      (fullTrainingKernel σ (deriv σ) b (θ t) xs).mulVec r i =
        ∑ k, fullTrainingKernel σ (deriv σ) b (θ t) xs i k * r k := by
    show (fun k => fullTrainingKernel σ (deriv σ) b (θ t) xs i k) ⬝ᵥ r = _
    rfl
  -- Rearrange: ∑ k, r k * K i k = ∑ k, K i k * r k.
  have h_swap :
      (∑ k, r k * fullTrainingKernel σ (deriv σ) b (θ t) xs i k)
        = ∑ k, fullTrainingKernel σ (deriv σ) b (θ t) xs i k * r k := by
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  rw [h_swap, ← h_mulVec]

end ProbabilityTheory
