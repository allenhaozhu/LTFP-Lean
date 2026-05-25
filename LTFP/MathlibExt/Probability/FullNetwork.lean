/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.NTKConcentration
import LTFP.MathlibExt.Probability.GradNeuronNTK
import LTFP.MathlibExt.Probability.FullNTKConcentration
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Single-hidden-layer network parameterization and init-kernel identity

**R4 NTK Part E3a — full network + training kernel definitions.**

Parts D, E1c, and E2 of the NTK programme work with the *init-time*
kernel `empiricalFullNTK`, whose σ- and σ'-blocks are evaluated at a
frozen iid sample `ω : Fin m → (EuclideanSpace ℝ (Fin d) × ℝ)`.
At training time the parameters of a single-hidden-layer network
evolve and the kernel acquires an `a_j ^ 2` weighting on the σ'
block. This file fixes the contract by defining:

* the parameter type `Param d m` (output weights `a` together with
  input weights `w`),
* the full network predictor `fullNet`,
* the dynamic training kernel `fullTrainingKernel`, which carries the
  `a_j ^ 2` weighting on the σ' block,
* an `InitParam` predicate capturing the canonical initialization
  `a_j ^ 2 = 1`, and
* the identity `fullTrainingKernel_init_eq_empiricalFullNTK` showing
  that at initialization the training kernel coincides with
  `empiricalFullNTK`.

The identity is the bridge between the random-feature (init-time)
matrix-Bernstein concentration in Parts D–E2 and a future
training-dynamics analysis.

## Main definitions

* `Param d m` — single-hidden-layer parameters (output weights and
  input weights).
* `fullNet σ b θ x` — the network predictor
  `f(θ, x) = (1/√m) Σ_j a_j σ(⟨w_j, x⟩ + b_j)`.
* `fullTrainingKernel σ σ' b θ xs` — the dynamic training kernel
  `(1/m) Σ_j σ-block + (1/m) Σ_j a_j ^ 2 · σ'-block`.
* `InitParam a₀ w₀` — the predicate `∀ j, a_j ^ 2 = 1`.

## Main results

* `fullTrainingKernel_init_eq_empiricalFullNTK` — the training kernel
  evaluated at any init parameter `(a₀, w₀)` with `a_j ^ 2 = 1`
  agrees, as a matrix, with
  `empiricalFullNTK σ σ' xs (fun j => (w₀ j, b j))`.
-/

namespace ProbabilityTheory

open MeasureTheory BigOperators Matrix

variable {d : ℕ}

/-! ### Parameter type and network predictor -/

/-- **Single-hidden-layer parameters.**

A point in parameter space consists of:
* output weights `a : Fin m → ℝ`, and
* input weights `w : Fin m → EuclideanSpace ℝ (Fin d)`.

Biases are treated as *frozen* hyperparameters (passed alongside the
network predictor) and are not part of the trained parameter vector,
matching Bach's Eq. 12.29 convention. -/
abbrev Param (d m : ℕ) :=
  (Fin m → ℝ) × (Fin m → EuclideanSpace ℝ (Fin d))

/-- **Single-hidden-layer network predictor.**

With output weights `a`, input weights `w`, frozen biases `b`, and
activation `σ`, the predictor is

  `f(θ, x) = (1 / √m) · Σ_j a_j · σ(⟨w_j, x⟩ + b_j)`.

The `1 / √m` factor is the canonical NTK normalization. -/
noncomputable def fullNet
    {m : ℕ}
    (σ : ℝ → ℝ)
    (b : Fin m → ℝ)
    (θ : Param d m)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (1 / Real.sqrt (m : ℝ)) *
    ∑ j, θ.1 j * σ (inner ℝ (θ.2 j) x + b j)

/-! ### Dynamic training kernel -/

/-- **Dynamic training kernel for a single-hidden-layer network.**

The training kernel at a parameter `θ = (a, w)` is
`K(θ; x, x') = ⟨∇_θ f(θ, x), ∇_θ f(θ, x')⟩`, decomposing along the
two parameter blocks.

* The `a`-derivatives contribute the σ block
  `(1 / m) Σ_j σ(⟨w_j, x⟩ + b_j) · σ(⟨w_j, x'⟩ + b_j)`.
* The `w`-derivatives contribute the σ' block
  `(1 / m) Σ_j a_j ^ 2 · σ'(⟨w_j, x⟩ + b_j) · σ'(⟨w_j, x'⟩ + b_j)
                    · ⟨x, x'⟩`.

This is the training-time (parameter-dependent) analogue of
`empiricalFullNTK`. The `a_j ^ 2` factor on the σ' block is the key
training-time refinement — it collapses to `1` at initialization
when `a_j ∈ {±1}`, recovering `empiricalFullNTK`. -/
noncomputable def fullTrainingKernel
    {n m : ℕ}
    (σ σ' : ℝ → ℝ)
    (b : Fin m → ℝ)
    (θ : Param d m)
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun r s =>
    (1 / (m : ℝ)) *
      ∑ j, σ (inner ℝ (θ.2 j) (xs r) + b j) *
             σ (inner ℝ (θ.2 j) (xs s) + b j)
     + (1 / (m : ℝ)) *
         ∑ j, θ.1 j ^ 2 *
                σ' (inner ℝ (θ.2 j) (xs r) + b j) *
                σ' (inner ℝ (θ.2 j) (xs s) + b j) *
                inner ℝ (xs r) (xs s)

/-- **Initialization parameter predicate.**

The canonical NTK initialization draws output weights `a_j` from a
distribution with `a_j ^ 2 = 1` almost surely — e.g. `a_j ∈ {±1}`
uniformly, or the symmetric Rademacher init. We capture this property
as a predicate on the joint parameter `(a₀, w₀)`. The input weights
`w₀` are unconstrained; only the squared-magnitude condition on `a₀`
is needed for the init-kernel identity below. -/
def InitParam {m : ℕ}
    (a₀ : Fin m → ℝ) (_w₀ : Fin m → EuclideanSpace ℝ (Fin d)) : Prop :=
  ∀ j, a₀ j ^ 2 = 1

/-! ### Init-kernel identity -/

/-- **Init-kernel identity.**

At an initialization parameter `(a₀, w₀)` with `a_j ^ 2 = 1`, the
dynamic training kernel coincides with the init-time random-feature
kernel `empiricalFullNTK`:

  `fullTrainingKernel σ σ' b (a₀, w₀) xs`
    `= empiricalFullNTK σ σ' xs (fun j => (w₀ j, b j))`.

The proof is entry-wise: the σ block of `fullTrainingKernel` matches
`empiricalNTK σ` by definition of `neuronNTK`, and the σ' block, with
`a_j ^ 2 = 1` substituted in, matches `empiricalGradNTK σ'` by
definition of `gradNeuronNTK`. Summing the two blocks recovers
`empiricalFullNTK = empiricalNTK + empiricalGradNTK`. -/
theorem fullTrainingKernel_init_eq_empiricalFullNTK
    {n m : ℕ}
    (σ σ' : ℝ → ℝ)
    (b : Fin m → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (a₀ : Fin m → ℝ) (w₀ : Fin m → EuclideanSpace ℝ (Fin d))
    (ha₀ : InitParam a₀ w₀) :
    fullTrainingKernel σ σ' b (a₀, w₀) xs =
      ProbabilityTheory.empiricalFullNTK σ σ' xs
        (fun j => (w₀ j, b j)) := by
  classical
  -- Reduce to entry-wise equality.
  ext r s
  -- Unfold the right-hand side: empiricalFullNTK = empiricalNTK + empiricalGradNTK.
  show fullTrainingKernel σ σ' b (a₀, w₀) xs r s
    = (empiricalNTK σ xs (fun j => (w₀ j, b j))
        + empiricalGradNTK σ' xs (fun j => (w₀ j, b j))) r s
  rw [Matrix.add_apply]
  -- Unfold the empirical-side definitions.
  unfold empiricalNTK empiricalGradNTK neuronNTK gradNeuronNTK
  -- Unfold the LHS training kernel.
  unfold fullTrainingKernel
  -- After unfolding, both sides are
  -- `(1/m) Σ_j σ(...) σ(...) + (1/m) Σ_j a_j^2 σ'(...) σ'(...) · ⟨xs r, xs s⟩`
  -- and `(1/m) Σ_j σ(...) σ(...) + (1/m) Σ_j σ'(...) σ'(...) · ⟨xs r, xs s⟩`
  -- respectively. The σ-blocks match. For the σ'-block, substitute
  -- `a_j ^ 2 = 1` pointwise and the remaining factors line up.
  -- We rewrite the σ'-block on the LHS by erasing the `a_j ^ 2` factor.
  have h_grad_eq :
      ∀ j : Fin m,
        a₀ j ^ 2 *
            σ' (inner ℝ ((a₀, w₀).2 j) (xs r) + b j) *
            σ' (inner ℝ ((a₀, w₀).2 j) (xs s) + b j) *
            inner ℝ (xs r) (xs s)
          = σ' (inner ℝ (w₀ j) (xs r) + b j) *
              σ' (inner ℝ (w₀ j) (xs s) + b j) *
              inner ℝ (xs r) (xs s) := by
    intro j
    have hj : a₀ j ^ 2 = 1 := ha₀ j
    -- `(a₀, w₀).2 = w₀`.
    simp [hj]
  -- The σ-block sums are identical after unfolding `(a₀, w₀).2 = w₀`.
  have h_sigma_sum :
      ∑ j, σ (inner ℝ ((a₀, w₀).2 j) (xs r) + b j) *
            σ (inner ℝ ((a₀, w₀).2 j) (xs s) + b j)
        = ∑ j, σ (inner ℝ (w₀ j) (xs r) + b j) *
            σ (inner ℝ (w₀ j) (xs s) + b j) := by
    apply Finset.sum_congr rfl
    intro j _
    rfl
  -- The σ'-block sums match after substituting `a₀ j ^ 2 = 1`.
  have h_grad_sum :
      ∑ j, a₀ j ^ 2 *
              σ' (inner ℝ ((a₀, w₀).2 j) (xs r) + b j) *
              σ' (inner ℝ ((a₀, w₀).2 j) (xs s) + b j) *
              inner ℝ (xs r) (xs s)
        = ∑ j, σ' (inner ℝ (w₀ j) (xs r) + b j) *
              σ' (inner ℝ (w₀ j) (xs s) + b j) *
              inner ℝ (xs r) (xs s) := by
    apply Finset.sum_congr rfl
    intro j _
    exact h_grad_eq j
  -- Assemble.
  show (1 / (m : ℝ)) *
        ∑ j, σ (inner ℝ ((a₀, w₀).2 j) (xs r) + b j) *
              σ (inner ℝ ((a₀, w₀).2 j) (xs s) + b j)
      + (1 / (m : ℝ)) *
          ∑ j, a₀ j ^ 2 *
                σ' (inner ℝ ((a₀, w₀).2 j) (xs r) + b j) *
                σ' (inner ℝ ((a₀, w₀).2 j) (xs s) + b j) *
                inner ℝ (xs r) (xs s)
      = (1 / (m : ℝ)) *
          ∑ j, σ (inner ℝ (w₀ j) (xs r) + b j) *
                σ (inner ℝ (w₀ j) (xs s) + b j)
        + (1 / (m : ℝ)) *
            ∑ j, σ' (inner ℝ (w₀ j) (xs r) + b j) *
                  σ' (inner ℝ (w₀ j) (xs s) + b j) *
                  inner ℝ (xs r) (xs s)
  rw [h_sigma_sum, h_grad_sum]

end ProbabilityTheory
