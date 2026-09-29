/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.NTKLazyTrainingWhp
import LTFP.MathlibExt.Probability.NTKGradientFlowExistence

/-!
# High-probability lazy training with existence of the gradient flow

`fullNet_gradient_flow_lazy_training_whp` controls every gradient-flow
trajectory from the antisymmetric initialisation, but does not assert that such
a trajectory exists. Here we combine it with `exists_fullNet_gradient_flow`:
with probability at least `1 - δ`, a gradient-flow trajectory on `[0, T]`
exists, it is unique, and every such trajectory has exponentially decaying
residual.

We also show that the good event, on which the initial training kernel has
Loewner floor `λ₀ / 2`, is closed (hence measurable), and state the result on
that event.

## Main results

* `isClosed_setOf_antisymInit_coercive` — the good event is closed.
* `measurableSet_setOf_antisymInit_coercive` — the good event is measurable.
* `fullNet_gradient_flow_on_antisymInit_coercive` — deterministic statement on
  the good event: existence, uniqueness and decay.
* `fullNet_gradient_flow_lazy_training_whp_exists` — the high-probability
  guarantee including existence of the flow.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator

open MeasureTheory Matrix BigOperators Set

namespace ProbabilityTheory

variable {d : ℕ}

/-- The empirical full NTK is continuous in the sampled neurons. -/
theorem continuous_empiricalFullNTK {n k : ℕ} {σ σ' : ℝ → ℝ} (hσ : Continuous σ)
    (hσ' : Continuous σ') (xs : Fin n → EuclideanSpace ℝ (Fin d)) :
    Continuous fun ω : Fin k → EuclideanSpace ℝ (Fin d) × ℝ => empiricalFullNTK σ σ' xs ω := by
  refine continuous_pi fun a => continuous_pi fun c => ?_
  simp only [empiricalFullNTK, empiricalNTK, empiricalGradNTK, Matrix.add_apply, neuronNTK,
    gradNeuronNTK]
  fun_prop

/-- **The good event is closed.** The set of samples for which the initial
training kernel of the antisymmetric initialisation dominates `c • 1` is
closed. -/
theorem isClosed_setOf_antisymInit_coercive {n k : ℕ} {σ σ' : ℝ → ℝ} (hσ : Continuous σ)
    (hσ' : Continuous σ') (xs : Fin n → EuclideanSpace ℝ (Fin d)) (c : ℝ) :
    IsClosed {ω : Fin k → EuclideanSpace ℝ (Fin d) × ℝ |
      c • (1 : Matrix (Fin n) (Fin n) ℝ) ≤
        fullTrainingKernel σ σ' (antisymInitBias ω) (antisymInitParam ω) xs} := by
  simp_rw [fullTrainingKernel_antisymInit]
  have hset : {ω : Fin k → EuclideanSpace ℝ (Fin d) × ℝ |
      c • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ empiricalFullNTK σ σ' xs ω} =
      ⋂ x : Fin n → ℝ, {ω | 0 ≤ star x ⬝ᵥ ((empiricalFullNTK σ σ' xs ω -
        c • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ x)} := by
    ext ω
    simp only [mem_setOf_eq, mem_iInter, Matrix.le_iff, posSemidef_iff_dotProduct_mulVec]
    refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    refine Matrix.IsHermitian.sub ?_ ?_
    · rw [← fullTrainingKernel_antisymInit σ σ' ω xs]
      exact fullTrainingKernel_isHermitian _ _ _ _ _
    · refine Matrix.IsHermitian.ext fun i j => ?_
      by_cases h : i = j
      · subst h; simp
      · simp [h, Ne.symm h]
  rw [hset]
  refine isClosed_iInter fun x => isClosed_le continuous_const ?_
  have hK := continuous_empiricalFullNTK (k := k) hσ hσ' xs
  have hK' : Continuous fun ω : Fin k → EuclideanSpace ℝ (Fin d) × ℝ =>
      empiricalFullNTK σ σ' xs ω - c • (1 : Matrix (Fin n) (Fin n) ℝ) :=
    hK.sub continuous_const
  have hmv : Continuous fun A : Matrix (Fin n) (Fin n) ℝ => star x ⬝ᵥ (A *ᵥ x) := by
    simp only [dotProduct, mulVec]
    fun_prop
  exact hmv.comp hK'

/-- **The good event is measurable.** -/
theorem measurableSet_setOf_antisymInit_coercive {n k : ℕ} {σ σ' : ℝ → ℝ}
    (hσ : Continuous σ) (hσ' : Continuous σ') (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (c : ℝ) :
    MeasurableSet {ω : Fin k → EuclideanSpace ℝ (Fin d) × ℝ |
      c • (1 : Matrix (Fin n) (Fin n) ℝ) ≤
        fullTrainingKernel σ σ' (antisymInitBias ω) (antisymInitParam ω) xs} :=
  (isClosed_setOf_antisymInit_coercive hσ hσ' xs c).measurableSet

/-- **Deterministic statement on the good event.** If the initial training kernel
of the antisymmetric initialisation has Loewner floor `λ₀ / 2` and the width
conditions hold, then a gradient-flow trajectory on `[0, T]` exists, any two
such trajectories agree on `[0, T]`, and every such trajectory satisfies
`‖r(θ t)‖² ≤ ‖y‖² exp (-(λ₀/2) t)`. -/
theorem fullNet_gradient_flow_on_antisymInit_coercive
    {n k : ℕ} [Nonempty (Fin n)] (hk : 0 < k)
    (σ : ℝ → ℝ) (hσ : Differentiable ℝ σ)
    {M M' : ℝ} (hσ_bdd : ∀ z, |σ z| ≤ M) (hσ'_bdd : ∀ z, |deriv σ z| ≤ M')
    {Lσ' : NNReal} (hσ'_lip : LipschitzWith Lσ' (deriv σ))
    (y : Fin n → ℝ) (xs : Fin n → EuclideanSpace ℝ (Fin d))
    {X : ℝ} (hX : ∀ i, ‖xs i‖ ≤ X) {lam₀ : ℝ} (hlam : 0 < lam₀)
    (hW₁ : gfMovementBound n (k + k) (lam₀ / 2) M M' X
      ‖(EuclideanSpace.equiv (Fin n) ℝ).symm y‖ < 1)
    (hW₂ : (n : ℝ) * gfDriftConst M M' Lσ' X *
      gfMovementBound n (k + k) (lam₀ / 2) M M' X
        ‖(EuclideanSpace.equiv (Fin n) ℝ).symm y‖ < lam₀ / 4)
    (T : ℝ) (ω : Fin k → EuclideanSpace ℝ (Fin d) × ℝ)
    (hω : (lam₀ / 2) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤
      fullTrainingKernel σ (deriv σ) (antisymInitBias ω) (antisymInitParam ω) xs) :
    (∃ θ : ℝ → Param d (k + k), θ 0 = antisymInitParam ω ∧ ContinuousOn θ (Icc 0 T) ∧
      ∀ t ∈ Ico 0 T, HasDerivWithinAt θ
        (gfFieldFullNet σ (antisymInitBias ω) y xs (θ t)) (Ici t) t) ∧
    (∀ θ θ' : ℝ → Param d (k + k), θ 0 = antisymInitParam ω →
      θ' 0 = antisymInitParam ω → ContinuousOn θ (Icc 0 T) → ContinuousOn θ' (Icc 0 T) →
      (∀ t ∈ Ico 0 T, HasDerivWithinAt θ
        (gfFieldFullNet σ (antisymInitBias ω) y xs (θ t)) (Ici t) t) →
      (∀ t ∈ Ico 0 T, HasDerivWithinAt θ'
        (gfFieldFullNet σ (antisymInitBias ω) y xs (θ' t)) (Ici t) t) →
      EqOn θ θ' (Icc 0 T)) ∧
    (∀ θ : ℝ → Param d (k + k), θ 0 = antisymInitParam ω → ContinuousOn θ (Icc 0 T) →
      (∀ t ∈ Ico 0 T, HasDerivWithinAt θ
        (gfFieldFullNet σ (antisymInitBias ω) y xs (θ t)) (Ici t) t) →
      ∀ t ∈ Icc 0 T,
        ‖residualFullNet σ (antisymInitBias ω) y xs (θ t)‖ ^ 2 ≤
          ‖(EuclideanSpace.equiv (Fin n) ℝ).symm y‖ ^ 2 * Real.exp (-(lam₀ / 2 * t))) := by
  set yE := (EuclideanSpace.equiv (Fin n) ℝ).symm y with hyE
  have hkk : 0 < k + k := by omega
  have ha₀ : ∀ j, |(antisymInitParam ω).1 j| ≤ 1 := fun j => by
    rw [abs_antisymInitParam_fst]
  have hR₀ : ‖residualFullNet σ (antisymInitBias ω) y xs (antisymInitParam ω)‖ ≤ ‖yE‖ := by
    rw [norm_residualFullNet_antisymInit]
  have hW₂' : (n : ℝ) * gfDriftConst M M' Lσ' X *
      gfMovementBound n (k + k) (lam₀ / 2) M M' X ‖yE‖ < lam₀ / 2 / 2 := by
    rw [show lam₀ / 2 / 2 = lam₀ / 4 by ring]; exact hW₂
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨θ, h0, hc, -, hd, -⟩ := exists_fullNet_gradient_flow hkk σ hσ hσ_bdd hσ'_bdd
      hσ'_lip (antisymInitBias ω) y xs hX (antisymInitParam ω) ha₀ (half_pos hlam) hω hR₀
      hW₁ hW₂' T
    exact ⟨θ, h0, hc, hd⟩
  · intro θ θ' h0 h0' hc hc' hd hd'
    exact fullNet_gradient_flow_unique hkk σ hσ hσ_bdd hσ'_bdd hσ'_lip (antisymInitBias ω) y
      xs hX (antisymInitParam ω) ha₀ (half_pos hlam) hω hR₀ hW₁ hW₂' θ θ' h0 h0' hc hc' hd hd'
  · intro θ hθ0 hθ_cont hθ_der t ht
    have hmain := fullNet_gradient_flow_lazy_training hkk σ hσ hσ_bdd hσ'_bdd hσ'_lip
      (antisymInitBias ω) y xs hX θ hθ_cont hθ_der (by rw [hθ0]; exact ha₀) (half_pos hlam)
      (by rw [hθ0]; exact hω) (by rw [hθ0]; exact hR₀) hW₁ hW₂' t ht
    have hr0 : ‖residualFullNet σ (antisymInitBias ω) y xs (θ 0)‖ = ‖yE‖ := by
      rw [hθ0, norm_residualFullNet_antisymInit]
    rw [hr0] at hmain
    exact hmain.1

/-- **End-to-end lazy-training guarantee with existence of the flow.**

Under the assumptions of `fullNet_gradient_flow_lazy_training_whp`, the good
event `G = {ω | (λ₀/2) • 1 ≤ K(antisymInitParam ω)}` is measurable, has
probability at least `1 - δ`, and for every `ω ∈ G` a gradient-flow trajectory
on `[0, T]` from the antisymmetric initialisation exists, is unique, and every
such trajectory satisfies `‖r(θ t)‖² ≤ ‖y‖² exp (-(λ₀/2) t)`. -/
theorem fullNet_gradient_flow_lazy_training_whp_exists
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
    ∃ G : Set (Fin k → EuclideanSpace ℝ (Fin d) × ℝ), MeasurableSet G ∧
      1 - δ ≤ (Measure.pi (fun _ : Fin k => ν)).real G ∧
      ∀ ω ∈ G,
        (∃ θ : ℝ → Param d (k + k), θ 0 = antisymInitParam ω ∧ ContinuousOn θ (Icc 0 T) ∧
          ∀ t ∈ Ico 0 T, HasDerivWithinAt θ
            (gfFieldFullNet σ (antisymInitBias ω) y xs (θ t)) (Ici t) t) ∧
        (∀ θ θ' : ℝ → Param d (k + k), θ 0 = antisymInitParam ω →
          θ' 0 = antisymInitParam ω → ContinuousOn θ (Icc 0 T) →
          ContinuousOn θ' (Icc 0 T) →
          (∀ t ∈ Ico 0 T, HasDerivWithinAt θ
            (gfFieldFullNet σ (antisymInitBias ω) y xs (θ t)) (Ici t) t) →
          (∀ t ∈ Ico 0 T, HasDerivWithinAt θ'
            (gfFieldFullNet σ (antisymInitBias ω) y xs (θ' t)) (Ici t) t) →
          EqOn θ θ' (Icc 0 T)) ∧
        (∀ θ : ℝ → Param d (k + k), θ 0 = antisymInitParam ω → ContinuousOn θ (Icc 0 T) →
          (∀ t ∈ Ico 0 T, HasDerivWithinAt θ
            (gfFieldFullNet σ (antisymInitBias ω) y xs (θ t)) (Ici t) t) →
          ∀ t ∈ Icc 0 T,
            ‖residualFullNet σ (antisymInitBias ω) y xs (θ t)‖ ^ 2 ≤
              ‖(EuclideanSpace.equiv (Fin n) ℝ).symm y‖ ^ 2 *
                Real.exp (-(lam₀ / 2 * t))) := by
  refine ⟨_, measurableSet_setOf_antisymInit_coercive hσ.continuous
    hσ'_lip.continuous xs (lam₀ / 2), ?_, fun ω hω => ?_⟩
  · exact fullTrainingKernel_antisymInit_coercive_whp hk hσ.continuous hM hσ_bdd
      hσ'_lip.continuous hM' hσ'_bdd xs hX_pos hX hlam hpop hδ hWσ hWσ'
  · exact fullNet_gradient_flow_on_antisymInit_coercive hk σ hσ hσ_bdd hσ'_bdd hσ'_lip y xs
      hX hlam hW₁ hW₂ T ω hω

end ProbabilityTheory
