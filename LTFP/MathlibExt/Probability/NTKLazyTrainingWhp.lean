/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.NTKInitCoercivityWhp
import LTFP.MathlibExt.Probability.NTKGradientFlowBootstrap

/-!
# End-to-end lazy-training guarantee for gradient flow

This file combines

* the antisymmetric initialisation (`NTKAntisymmetricInit`), whose initial
  residual is `-y` and whose output weights have absolute value `1`,
* the high-probability initial coercivity of the training kernel
  (`NTKInitCoercivityWhp`), obtained from matrix Bernstein with all
  regularity side conditions discharged, and
* the deterministic gradient-flow bootstrap
  (`fullNet_gradient_flow_lazy_training`),

into a single statement: with probability at least `1 - δ` over the `k`
sampled neurons, *every* gradient-flow trajectory of the width-`k + k`
network started at the antisymmetric initialisation has exponentially
decaying training residual on `[0, T]`,

  `‖r(θ t)‖² ≤ ‖y‖² · exp (-(λ₀/2) t)`.

## Assumptions

* model: `σ` differentiable, `|σ| ≤ M`, `|σ'| ≤ M'`, `σ'` Lipschitz;
* data: `‖xᵢ‖ ≤ X`, and the population full NTK is coercive,
  `λ₀ • 1 ≤ K_pop` (a property of the data and the sampling law `ν`);
* width: `k ≥ ntkBernsteinWidth` for both kernel blocks at deviation `λ₀/4`,
  plus the bootstrap width conditions of `fullNet_gradient_flow_lazy_training`
  with `ρ := λ₀ / 2` and `R₀ := ‖y‖`.

## Main result

* `fullNet_gradient_flow_lazy_training_whp`.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator

open MeasureTheory Matrix BigOperators Set

namespace ProbabilityTheory

variable {d : ℕ}

/-- **End-to-end lazy-training guarantee under gradient flow (high
probability).**

Sample `k` neurons iid from `ν` and initialise the width-`k + k` network
antisymmetrically. Under the regularity assumptions on `σ`, the input bound
`‖xᵢ‖ ≤ X`, population coercivity `λ₀ • 1 ≤ K_pop` and the explicit width
conditions, with probability at least `1 - δ` the following holds: every
gradient-flow trajectory `θ` on `[0, T]` started at the initialisation
satisfies `‖r(θ t)‖² ≤ ‖y‖² exp (-(λ₀/2) t)` for all `t ∈ [0, T]`. -/
theorem fullNet_gradient_flow_lazy_training_whp
    {n k : ℕ} [Nonempty (Fin n)] (hk : 0 < k)
    (σ : ℝ → ℝ) (hσ : Differentiable ℝ σ)
    {M M' : ℝ} (hM : 0 < M) (hM' : 0 < M')
    (hσ_bdd : ∀ z, |σ z| ≤ M) (hσ'_bdd : ∀ z, |deriv σ z| ≤ M')
    {Lσ' : NNReal} (hσ'_lip : LipschitzWith Lσ' (deriv σ))
    (y : Fin n → ℝ) (xs : Fin n → EuclideanSpace ℝ (Fin d))
    {X : ℝ} (hX_pos : 0 < X) (hX : ∀ i, ‖xs i‖ ≤ X)
    {ν : Measure (EuclideanSpace ℝ (Fin d) × ℝ)} [IsProbabilityMeasure ν]
    {lam₀ : ℝ} (hlam : 0 < lam₀)
    (hpop : lam₀ • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ populationFullNTK σ (deriv σ) xs ν)
    {δ : ℝ} (hδ : 0 < δ)
    (hWσ : ntkBernsteinWidth n (M ^ 2) (lam₀ / 4) δ ≤ k)
    (hWσ' : ntkBernsteinWidth n (M' ^ 2 * X ^ 2) (lam₀ / 4) δ ≤ k)
    (hW₁ : gfMovementBound n (k + k) (lam₀ / 2) M M' X
      ‖(EuclideanSpace.equiv (Fin n) ℝ).symm y‖ < 1)
    (hW₂ : (n : ℝ) * gfDriftConst M M' Lσ' X *
      gfMovementBound n (k + k) (lam₀ / 2) M M' X
        ‖(EuclideanSpace.equiv (Fin n) ℝ).symm y‖ < lam₀ / 4)
    (T : ℝ) :
    1 - δ ≤ (Measure.pi (fun _ : Fin k => ν)).real
      {ω | ∀ θ : ℝ → Param d (k + k), θ 0 = antisymInitParam ω →
        ContinuousOn θ (Icc 0 T) →
        (∀ t ∈ Ico 0 T, HasDerivWithinAt θ
          (gfFieldFullNet σ (antisymInitBias ω) y xs (θ t)) (Ici t) t) →
        ∀ t ∈ Icc 0 T,
          ‖residualFullNet σ (antisymInitBias ω) y xs (θ t)‖ ^ 2 ≤
            ‖(EuclideanSpace.equiv (Fin n) ℝ).symm y‖ ^ 2 *
              Real.exp (-(lam₀ / 2 * t))} := by
  set μ := Measure.pi (fun _ : Fin k => ν)
  set yE := (EuclideanSpace.equiv (Fin n) ℝ).symm y with hyE
  have hkk : 0 < k + k := by omega
  -- High-probability initial coercivity of the training kernel.
  have hgood := fullTrainingKernel_antisymInit_coercive_whp hk hσ.continuous hM hσ_bdd
    hσ'_lip.continuous hM' hσ'_bdd xs hX_pos hX hlam hpop hδ hWσ hWσ'
  refine hgood.trans (measureReal_mono ?_)
  -- On the good event, the deterministic bootstrap applies.
  intro ω hω θ hθ0 hθ_cont hθ_der t ht
  simp only [Set.mem_setOf_eq] at hω
  have ha₀ : ∀ j, |(θ 0).1 j| ≤ 1 := fun j => by
    rw [hθ0, abs_antisymInitParam_fst]
  have hK₀ : (lam₀ / 2) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤
      fullTrainingKernel σ (deriv σ) (antisymInitBias ω) (θ 0) xs := by
    rw [hθ0]; exact hω
  have hR₀ : ‖residualFullNet σ (antisymInitBias ω) y xs (θ 0)‖ ≤ ‖yE‖ := by
    rw [hθ0, norm_residualFullNet_antisymInit]
  have hW₂' : (n : ℝ) * gfDriftConst M M' Lσ' X *
      gfMovementBound n (k + k) (lam₀ / 2) M M' X ‖yE‖ < lam₀ / 2 / 2 := by
    rw [show lam₀ / 2 / 2 = lam₀ / 4 by ring]; exact hW₂
  have hmain := fullNet_gradient_flow_lazy_training hkk σ hσ hσ_bdd hσ'_bdd hσ'_lip
    (antisymInitBias ω) y xs hX θ hθ_cont hθ_der ha₀ (half_pos hlam) hK₀ hR₀ hW₁ hW₂' t ht
  have hr0 : ‖residualFullNet σ (antisymInitBias ω) y xs (θ 0)‖ = ‖yE‖ := by
    rw [hθ0, norm_residualFullNet_antisymInit]
  rw [hr0] at hmain
  exact hmain.1

end ProbabilityTheory
