/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.FullKernelPerturbation
import LTFP.MathlibExt.Probability.NTKLazyTrainingEndToEnd

/-!
# Coercivity preservation under bounded parameter drift

**R4 NTK Part E3e.5 — coercivity preservation along the trajectory.**

Composes the Lipschitz operator-norm drift bound
`fullTrainingKernel_opNorm_drift_le` (Part E3c.2 / E3d) with the
Loewner-perturbation coercivity-transfer lemma `real_le_smul_one_perturb`
to give: if the initial dynamic NTK is coercive `ρ • 1 ≤ K(θ₀)` and the
parameter has moved by at most `Δ` from `θ₀` (entrywise distance per
neuron block), then the perturbed kernel inherits a coercivity floor
`(ρ/2) • 1 ≤ K(θ)`, provided the parameter drift is small enough that
`n · C · Δ ≤ ρ/2` where `C` is the operator-norm drift Lipschitz
constant.

This is the deterministic glue lemma that closes the "self-consistency"
loop for NTK lazy-training: bounded parameter motion preserves the NTK
spectral floor, which in turn (via Grönwall, Strategy 1) preserves the
exponential residual decay.

## Main result

* `coercivity_preserved_under_param_drift` — see the statement below.

## Strategy

1. Apply `fullTrainingKernel_opNorm_drift_le` to bound
   `‖K(θ) - K(θ₀)‖_op ≤ n · C · Δ`.
2. Combine with the small-drift hypothesis `n · C · Δ ≤ ρ/2` to get
   `‖K(θ) - K(θ₀)‖_op ≤ ρ/2`.
3. Apply `real_le_smul_one_perturb` to lift the operator-norm bound
   into a Loewner shift, yielding `(ρ - ρ/2) • 1 ≤ K(θ)`.
4. Algebra: `ρ - ρ/2 = ρ/2`.

## References

* Bach (2024) *Learning Theory from First Principles*, §12 (NTK lazy
  training).
* `LTFP.MathlibExt.Probability.FullKernelPerturbation` — E3c / E3d
  operator-norm drift.
* `LTFP.MathlibExt.Probability.NTKLazyTrainingEndToEnd` — E3e.1
  Loewner perturbation transfer.
-/

open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix

namespace LTFP

variable {d n m : ℕ}

/-- **Coercivity preservation under bounded parameter drift.**

Suppose:

* `σ, σ' : ℝ → ℝ` are bounded by `M, M'` and Lipschitz with constants
  `Lσ, Lσ'`;
* `xs : Fin n → EuclideanSpace ℝ (Fin d)` is data with bounded inner
  product `|⟨xs i, xs j⟩| ≤ G` and norm `‖xs i‖ ≤ X`;
* `θ, θ₀ : Param d m` are parameters with bounded output weights
  `|θ.1 j|, |θ₀.1 j| ≤ Aa` and parameter distance per neuron
  `dist (θ.1 j, θ.2 j) (θ₀.1 j, θ₀.2 j) ≤ Δ`;
* `K(θ₀) = fullTrainingKernel σ σ' b θ₀ xs` is coercive: `ρ • 1 ≤ K(θ₀)`;
* `K(θ)` and `K(θ₀)` are Hermitian.

If the parameter drift is small enough that `n · C · Δ ≤ ρ/2` where
`C := 2·M·Lσ·X + 2·Aa·M'²·G + 2·Aa²·M'·Lσ'·X·G` is the operator-norm
Lipschitz constant of `K`, then the perturbed kernel inherits a
coercivity floor:

  `(ρ/2) • 1 ≤ fullTrainingKernel σ σ' b θ xs`.

This is the deterministic core of NTK lazy-training: bounded parameter
motion preserves the NTK spectral floor. -/
theorem coercivity_preserved_under_param_drift
    [Nonempty (Fin n)]
    (σ σ' : ℝ → ℝ)
    {Lσ Lσ' : NNReal}
    (hσ_lip : LipschitzWith Lσ σ)
    (hσ'_lip : LipschitzWith Lσ' σ')
    {M M' : ℝ} (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (hσ_bdd : ∀ z, |σ z| ≤ M)
    (hσ'_bdd : ∀ z, |σ' z| ≤ M')
    (b : Fin m → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    {G X : ℝ} (hG_nn : 0 ≤ G) (hX_nn : 0 ≤ X)
    (hG : ∀ a b, |inner ℝ (xs a) (xs b)| ≤ G)
    (hX : ∀ a, ‖xs a‖ ≤ X)
    {Aa : ℝ} (hAa : 0 ≤ Aa)
    {θ θ₀ : ProbabilityTheory.Param d m}
    (ha_bound : ∀ j, |θ.1 j| ≤ Aa) (ha₀_bound : ∀ j, |θ₀.1 j| ≤ Aa)
    (Δ : ℝ) (hΔ_nn : 0 ≤ Δ)
    (hΔ : ∀ j, dist (θ.1 j, θ.2 j) (θ₀.1 j, θ₀.2 j) ≤ Δ)
    {ρ : ℝ} (_hρ_pos : 0 < ρ)
    (hK_herm₀ : (ProbabilityTheory.fullTrainingKernel σ σ' b θ₀ xs).IsHermitian)
    (hK_herm : (ProbabilityTheory.fullTrainingKernel σ σ' b θ xs).IsHermitian)
    (hK_init_coercive :
      (ρ : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤
        ProbabilityTheory.fullTrainingKernel σ σ' b θ₀ xs)
    (h_small :
      (n : ℝ) *
        (2 * M * (Lσ : ℝ) * X + 2 * Aa * M' ^ 2 * G
          + 2 * Aa ^ 2 * M' * (Lσ' : ℝ) * X * G) * Δ ≤ ρ / 2) :
    (ρ / 2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤
      ProbabilityTheory.fullTrainingKernel σ σ' b θ xs := by
  -- Step 1: operator-norm drift bound from E3c.2 / E3d.
  have h_drift :
      ‖ProbabilityTheory.fullTrainingKernel σ σ' b θ xs -
        ProbabilityTheory.fullTrainingKernel σ σ' b θ₀ xs‖ ≤
      (n : ℝ) *
        (2 * M * (Lσ : ℝ) * X + 2 * Aa * M' ^ 2 * G
          + 2 * Aa ^ 2 * M' * (Lσ' : ℝ) * X * G) * Δ :=
    ProbabilityTheory.fullTrainingKernel_opNorm_drift_le σ σ' hσ_lip hσ'_lip
      hM hM' hσ_bdd hσ'_bdd b xs hG_nn hX_nn hG hX hAa
      ha_bound ha₀_bound Δ hΔ_nn hΔ
  -- Step 2: chain with the small-drift hypothesis.
  have h_drift_half :
      ‖ProbabilityTheory.fullTrainingKernel σ σ' b θ xs -
        ProbabilityTheory.fullTrainingKernel σ σ' b θ₀ xs‖ ≤ ρ / 2 :=
    le_trans h_drift h_small
  -- Step 3: switch sign for the perturbation lemma input.
  have h_drift_sym :
      ‖ProbabilityTheory.fullTrainingKernel σ σ' b θ₀ xs -
        ProbabilityTheory.fullTrainingKernel σ σ' b θ xs‖ ≤ ρ / 2 := by
    rw [norm_sub_rev]; exact h_drift_half
  -- Step 4: Loewner perturbation (E3e.1) gives `(ρ - ρ/2) • 1 ≤ K(θ)`.
  have h_perturb :
      ((ρ - ρ / 2) : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤
        ProbabilityTheory.fullTrainingKernel σ σ' b θ xs :=
    real_le_smul_one_perturb hK_herm₀ hK_herm hK_init_coercive h_drift_sym
  -- Step 5: algebra `ρ - ρ/2 = ρ/2`.
  have h_eq : (ρ - ρ / 2 : ℝ) = ρ / 2 := by ring
  rw [h_eq] at h_perturb
  exact h_perturb

end LTFP
