/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.NTKGradientFlowResidual
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Topology.Algebra.MetricSpace.Lipschitz

/-!
# Local Lipschitz bound for the gradient field of the two-layer network

If `σ` and `σ'` are Lipschitz, the explicit gradient-flow field
`gfFieldFullNet σ b y xs` is locally Lipschitz on the parameter space. Since
`Param d m` is finite dimensional, it is therefore Lipschitz and bounded on
every closed ball.

## Main results

* `locallyLipschitz_smul_of_real` — the pointwise scalar product of two
  locally Lipschitz maps is locally Lipschitz.
* `locallyLipschitz_pi_of_forall` — a finite product of locally Lipschitz
  maps is locally Lipschitz.
* `locallyLipschitz_gfFieldFullNet` — the gradient field is locally Lipschitz.
* `exists_lipschitzOnWith_gfFieldFullNet_closedBall` — it is Lipschitz on
  every closed ball.
* `exists_norm_le_gfFieldFullNet_closedBall` — it is bounded on every closed
  ball.
-/

namespace ProbabilityTheory

open BigOperators Metric Set Filter Topology LTFP

section Aux

variable {α E : Type*} [PseudoMetricSpace α] [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- The pointwise scalar product of two locally Lipschitz maps is locally
Lipschitz. -/
theorem locallyLipschitz_smul_of_real {f : α → ℝ} {g : α → E}
    (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz fun x => f x • g x := by
  intro x
  obtain ⟨Kf, t, ht, hKf⟩ := hf x
  obtain ⟨Kg, u, hu, hKg⟩ := hg x
  set Cf : ℝ := ‖f x‖ + 1
  set Cg : ℝ := ‖g x‖ + 1
  have hCf : 0 ≤ Cf := by positivity
  have hCg : 0 ≤ Cg := by positivity
  have hv₁ : {z | ‖f z‖ < Cf} ∈ 𝓝 x :=
    hf.continuous.norm.continuousAt.preimage_mem_nhds (Iio_mem_nhds (lt_add_one _))
  have hv₂ : {z | ‖g z‖ < Cg} ∈ 𝓝 x :=
    hg.continuous.norm.continuousAt.preimage_mem_nhds (Iio_mem_nhds (lt_add_one _))
  refine ⟨Cf.toNNReal * Kg + Kf * Cg.toNNReal,
    t ∩ u ∩ ({z | ‖f z‖ < Cf} ∩ {z | ‖g z‖ < Cg}),
    inter_mem (inter_mem ht hu) (inter_mem hv₁ hv₂), ?_⟩
  refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
  have h1 := hKf.dist_le_mul p hp.1.1 q hq.1.1
  have h2 := hKg.dist_le_mul p hp.1.2 q hq.1.2
  have hfp : ‖f p‖ ≤ Cf := hp.2.1.le
  have hgq : ‖g q‖ ≤ Cg := hq.2.2.le
  rw [dist_eq_norm] at h1 h2 ⊢
  have hdecomp : f p • g p - f q • g q = f p • (g p - g q) + (f p - f q) • g q := by
    rw [smul_sub, sub_smul]; abel
  rw [hdecomp]
  push_cast
  rw [Real.coe_toNNReal _ hCf, Real.coe_toNNReal _ hCg]
  have hd := dist_nonneg (x := p) (y := q)
  calc ‖f p • (g p - g q) + (f p - f q) • g q‖
      ≤ ‖f p‖ * ‖g p - g q‖ + ‖f p - f q‖ * ‖g q‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul]
    _ ≤ Cf * (Kg * dist p q) + Kf * dist p q * Cg := by
        gcongr
    _ = (Cf * Kg + Kf * Cg) * dist p q := by ring

/-- The pointwise product of two locally Lipschitz real functions is locally
Lipschitz. -/
theorem locallyLipschitz_mul_of_real {f g : α → ℝ}
    (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) :
    LocallyLipschitz fun x => f x * g x := by
  simpa only [smul_eq_mul] using locallyLipschitz_smul_of_real hf hg

omit [NormedSpace ℝ E] in
/-- A finite sum of locally Lipschitz maps is locally Lipschitz. -/
theorem locallyLipschitz_finset_sum {ι : Type*} (s : Finset ι) {f : ι → α → E}
    (hf : ∀ i ∈ s, LocallyLipschitz (f i)) :
    LocallyLipschitz fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LocallyLipschitz.const (0 : E)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).add
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- A finite product of locally Lipschitz maps is locally Lipschitz. -/
theorem locallyLipschitz_pi_of_forall {ι : Type*} [Fintype ι] {F : ι → Type*}
    [∀ i, PseudoMetricSpace (F i)] {f : α → ∀ i, F i}
    (hf : ∀ i, LocallyLipschitz fun x => f x i) : LocallyLipschitz f := by
  intro x
  choose K t ht hL using fun i => hf i x
  refine ⟨∑ i, K i, ⋂ i, t i, iInter_mem.2 ht, ?_⟩
  refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
  rw [mem_iInter] at hp hq
  refine (dist_pi_le_iff (by positivity)).2 fun i => ?_
  refine ((hL i).dist_le_mul p (hp i) q (hq i)).trans ?_
  gcongr
  exact_mod_cast Finset.single_le_sum (fun j _ => (K j).coe_nonneg) (Finset.mem_univ i)

end Aux

variable {d n m : ℕ}

/-- The pre-activation `θ ↦ ⟪w_j, x⟫ + b_j` is locally Lipschitz. -/
theorem locallyLipschitz_preact (b : Fin m → ℝ) (x : EuclideanSpace ℝ (Fin d)) (j : Fin m) :
    LocallyLipschitz fun θ : Param d m => inner ℝ (θ.2 j) x + b j := by
  have : ContDiff ℝ 1 fun θ : Param d m => inner ℝ (θ.2 j) x + b j :=
    (ContDiff.inner ℝ (by fun_prop) contDiff_const).add contDiff_const
  exact this.locallyLipschitz

/-- The output-weight coordinate `θ ↦ a_j` is locally Lipschitz. -/
theorem locallyLipschitz_outWeight (j : Fin m) :
    LocallyLipschitz fun θ : Param d m => θ.1 j := by
  have : ContDiff ℝ 1 fun θ : Param d m => θ.1 j := by fun_prop
  exact this.locallyLipschitz

/-- The network output is locally Lipschitz in the parameters when `σ` is
Lipschitz. -/
theorem locallyLipschitz_fullNet {σ : ℝ → ℝ} {Kσ : NNReal} (hσ : LipschitzWith Kσ σ)
    (b : Fin m → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    LocallyLipschitz fun θ : Param d m => fullNet σ b θ x := by
  unfold fullNet
  refine locallyLipschitz_mul_of_real (LocallyLipschitz.const _) ?_
  refine locallyLipschitz_finset_sum _ fun j _ => ?_
  exact locallyLipschitz_mul_of_real (locallyLipschitz_outWeight j)
    (hσ.locallyLipschitz.comp (locallyLipschitz_preact b x j))

/-- The explicit gradient of the network output is locally Lipschitz in the
parameters when `σ` and `σ'` are Lipschitz. -/
theorem locallyLipschitz_gradFullNet {σ σ' : ℝ → ℝ} {Kσ Kσ' : NNReal}
    (hσ : LipschitzWith Kσ σ) (hσ' : LipschitzWith Kσ' σ')
    (b : Fin m → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    LocallyLipschitz fun θ : Param d m => gradFullNet σ σ' b θ x := by
  unfold gradFullNet
  refine LocallyLipschitz.prodMk ?_ ?_
  · refine locallyLipschitz_pi_of_forall fun j => ?_
    exact locallyLipschitz_mul_of_real (LocallyLipschitz.const _)
      (hσ.locallyLipschitz.comp (locallyLipschitz_preact b x j))
  · refine locallyLipschitz_pi_of_forall fun j => ?_
    refine locallyLipschitz_smul_of_real ?_ (LocallyLipschitz.const x)
    exact locallyLipschitz_mul_of_real
      (locallyLipschitz_mul_of_real (LocallyLipschitz.const _) (locallyLipschitz_outWeight j))
      (hσ'.locallyLipschitz.comp (locallyLipschitz_preact b x j))

/-- **The gradient field is locally Lipschitz.** -/
theorem locallyLipschitz_gfFieldFullNet {σ : ℝ → ℝ} {Kσ Kσ' : NNReal}
    (hσ : LipschitzWith Kσ σ) (hσ' : LipschitzWith Kσ' (deriv σ))
    (b : Fin m → ℝ) (y : Fin n → ℝ) (xs : Fin n → EuclideanSpace ℝ (Fin d)) :
    LocallyLipschitz (gfFieldFullNet σ b y xs) := by
  unfold gfFieldFullNet
  refine locallyLipschitz_finset_sum _ fun i _ => ?_
  exact locallyLipschitz_smul_of_real
    ((LocallyLipschitz.const (y i)).sub (locallyLipschitz_fullNet hσ b (xs i)))
    (locallyLipschitz_gradFullNet hσ hσ' b (xs i))

/-- **The gradient field is Lipschitz on every closed ball.** -/
theorem exists_lipschitzOnWith_gfFieldFullNet_closedBall {σ : ℝ → ℝ} {Kσ Kσ' : NNReal}
    (hσ : LipschitzWith Kσ σ) (hσ' : LipschitzWith Kσ' (deriv σ))
    (b : Fin m → ℝ) (y : Fin n → ℝ) (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (θ₀ : Param d m) (R : ℝ) :
    ∃ K, LipschitzOnWith K (gfFieldFullNet σ b y xs) (closedBall θ₀ R) :=
  LocallyLipschitzOn.exists_lipschitzOnWith_of_compact (isCompact_closedBall θ₀ R)
    (locallyLipschitz_gfFieldFullNet hσ hσ' b y xs).locallyLipschitzOn

/-- **The gradient field is bounded on every closed ball.** -/
theorem exists_norm_le_gfFieldFullNet_closedBall {σ : ℝ → ℝ} {Kσ Kσ' : NNReal}
    (hσ : LipschitzWith Kσ σ) (hσ' : LipschitzWith Kσ' (deriv σ))
    (b : Fin m → ℝ) (y : Fin n → ℝ) (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (θ₀ : Param d m) (R : ℝ) :
    ∃ B, ∀ θ ∈ closedBall θ₀ R, ‖gfFieldFullNet σ b y xs θ‖ ≤ B :=
  (isCompact_closedBall θ₀ R).exists_bound_of_continuousOn
    (locallyLipschitz_gfFieldFullNet hσ hσ' b y xs).continuous.continuousOn

end ProbabilityTheory
