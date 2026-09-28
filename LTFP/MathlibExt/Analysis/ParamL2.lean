/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.FullNetwork
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# L² parameter wrapper for single-hidden-layer networks

**R4 NTK L1 — L² parameter norm foundation.**

The existing `Param d m := (Fin m → ℝ) × (Fin m → EuclideanSpace ℝ (Fin d))`
inherits Mathlib's default **sup-norm** (max over the product and Pi
projections).  The Chizat–Bach Hessian bound

  `‖iteratedFDeriv 2 f θ‖ ≤ L₀ / √m`

for softplus is **false** under this sup-norm — the scalar bilinear
Hessian sums across all `m` neuron blocks and the sup-norm on `Param`
gives a `√m · L₀` bound instead.  The correct `L₀ / √m` rate arises
only under an **L² parameter norm** and Cauchy–Schwarz.

This file introduces a companion type `ParamL2 d m` — the same
underlying data flattened to `EuclideanSpace ℝ (Fin (m + m * d))` — and
supplies the linear-equivalence bridge to `Param d m`, plus the
two-sided sup/L² norm comparison.

## Layout convention

The `m + m * d` flat coordinates are split into two blocks:

* Indices `⟨k, _⟩` with `k < m`  → output weight `a_k`.
* Indices `⟨m + k * d + i, _⟩`   → input weight coordinate `w_k i`.

## Main definitions

* `ParamL2 d m` — flat L² parameter space.
* `ParamL2.toParam` / `ParamL2.ofParam` — the two directions of the bridge.
* `paramL2Equiv d m` — linear equivalence `ParamL2 d m ≃ₗ[ℝ] Param d m`.
* `ParamL2.unwrap` / `ParamL2.wrap` — user-facing aliases.

## Main results

* `param_sup_le_paramL2` — `‖ParamL2.toParam θ‖ ≤ ‖θ‖`.
* `paramL2_le_scale_param_sup` —
  `‖θ‖ ≤ √(m + m · d) · ‖ParamL2.toParam θ‖`.
-/

namespace ProbabilityTheory

open BigOperators Real

variable {d m : ℕ}

/-! ### The L² parameter space -/

/-- **Flat L² parameter space** for a single-hidden-layer network with
`m` neurons and input dimension `d`.

Definitionally `EuclideanSpace ℝ (Fin (m + m * d))`, which is
`PiLp 2 (fun _ : Fin (m + m * d) => ℝ)`.  All L²-norm, inner-product,
and normed-space instances are inherited from Mathlib. -/
abbrev ParamL2 (d m : ℕ) : Type :=
  EuclideanSpace ℝ (Fin (m + m * d))

/-! ### Layout helpers -/

/-- Flat index for the output weight `a_k`. -/
def ParamL2.aIdx (m d : ℕ) (k : Fin m) : Fin (m + m * d) :=
  ⟨k.val, lt_of_lt_of_le k.isLt (Nat.le_add_right _ _)⟩

@[simp]
lemma ParamL2.aIdx_val (m d : ℕ) (k : Fin m) :
    (ParamL2.aIdx m d k).val = k.val := rfl

/-- Flat index for the `i`-th coordinate of the input weight `w_k`. -/
def ParamL2.wIdx (m d : ℕ) (k : Fin m) (i : Fin d) : Fin (m + m * d) :=
  ⟨m + k.val * d + i.val, by
    have hkd : k.val * d + i.val < m * d := by
      have h1 : k.val * d + i.val < k.val * d + d :=
        Nat.add_lt_add_left i.isLt _
      have h2 : k.val * d + d = (k.val + 1) * d := by ring
      have h3 : (k.val + 1) * d ≤ m * d :=
        Nat.mul_le_mul_right d (Nat.succ_le_of_lt k.isLt)
      omega
    omega⟩

@[simp]
lemma ParamL2.wIdx_val (m d : ℕ) (k : Fin m) (i : Fin d) :
    (ParamL2.wIdx m d k i).val = m + k.val * d + i.val := rfl

/-! ### Bridge to `Param d m` -/

/-- Unpack a flat L² parameter vector into the `(a, w)` sup-norm form. -/
noncomputable def ParamL2.toParam (θ : ParamL2 d m) : Param d m :=
  ( fun k : Fin m => θ (ParamL2.aIdx m d k)
  , fun k : Fin m => (WithLp.equiv 2 (Fin d → ℝ)).symm
                       (fun i : Fin d => θ (ParamL2.wIdx m d k i)) )

/-- Package an `(a, w)` parameter into flat L² form. -/
noncomputable def ParamL2.ofParam (θ : Param d m) : ParamL2 d m :=
  (WithLp.equiv 2 (Fin (m + m * d) → ℝ)).symm
    (fun j : Fin (m + m * d) =>
      if h : j.val < m then
        θ.1 ⟨j.val, h⟩
      else
        let r := j.val - m
        let k := r / d
        let i := r % d
        if hk : k < m then
          if hi : i < d then
            (WithLp.equiv 2 (Fin d → ℝ)) (θ.2 ⟨k, hk⟩) ⟨i, hi⟩
          else (0 : ℝ)
        else (0 : ℝ))

/-! ### Linearity of `toParam` -/

lemma ParamL2.toParam_add (θ η : ParamL2 d m) :
    ParamL2.toParam (θ + η) = ParamL2.toParam θ + ParamL2.toParam η := by
  refine Prod.ext ?_ ?_
  · funext k
    change (θ + η) (ParamL2.aIdx m d k) = θ (ParamL2.aIdx m d k) + η (ParamL2.aIdx m d k)
    rfl
  · funext k
    apply PiLp.ext
    intro i
    -- After PiLp.ext, the goal is on the underlying pi types via coercion.
    -- Both sides applied at (wIdx m d k i) come from the same flat add.
    show (WithLp.equiv 2 (Fin d → ℝ)).symm
            (fun i' : Fin d => (θ + η) (ParamL2.wIdx m d k i')) i =
          ((WithLp.equiv 2 (Fin d → ℝ)).symm
              (fun i' : Fin d => θ (ParamL2.wIdx m d k i')) +
            (WithLp.equiv 2 (Fin d → ℝ)).symm
              (fun i' : Fin d => η (ParamL2.wIdx m d k i'))) i
    rfl

lemma ParamL2.toParam_smul (c : ℝ) (θ : ParamL2 d m) :
    ParamL2.toParam (c • θ) = c • ParamL2.toParam θ := by
  refine Prod.ext ?_ ?_
  · funext k
    change (c • θ) (ParamL2.aIdx m d k) = c • (θ (ParamL2.aIdx m d k))
    rfl
  · funext k
    apply PiLp.ext
    intro i
    show (WithLp.equiv 2 (Fin d → ℝ)).symm
            (fun i' : Fin d => (c • θ) (ParamL2.wIdx m d k i')) i =
          (c • (WithLp.equiv 2 (Fin d → ℝ)).symm
              (fun i' : Fin d => θ (ParamL2.wIdx m d k i'))) i
    rfl

/-! ### Round trips -/

/-- Round-trip on flat vectors: `ofParam ∘ toParam = id`. -/
lemma ParamL2.ofParam_toParam (θ : ParamL2 d m) :
    ParamL2.ofParam (ParamL2.toParam θ) = θ := by
  classical
  apply PiLp.ext
  intro j
  -- Both sides evaluated at j — reduce to the underlying pi function.
  -- The LHS is `((WithLp.equiv 2 _).symm (fun j' => …)) j = (fun j' => …) j`.
  have hLHS : (ParamL2.ofParam (ParamL2.toParam θ)) j =
      (if h : j.val < m then
        (ParamL2.toParam θ).1 ⟨j.val, h⟩
      else
        let r := j.val - m
        let k := r / d
        let i := r % d
        if hk : k < m then
          if hi : i < d then
            (WithLp.equiv 2 (Fin d → ℝ)) ((ParamL2.toParam θ).2 ⟨k, hk⟩) ⟨i, hi⟩
          else (0 : ℝ)
        else (0 : ℝ)) := rfl
  rw [hLHS]
  by_cases hj : j.val < m
  · -- a-block
    rw [dif_pos hj]
    -- (toParam θ).1 ⟨j.val, hj⟩ = θ (aIdx m d ⟨j.val, hj⟩) = θ j
    have hAidx : (ParamL2.aIdx m d ⟨j.val, hj⟩) = j := Fin.ext rfl
    show θ (ParamL2.aIdx m d ⟨j.val, hj⟩) = θ j
    rw [hAidx]
  · -- w-block
    push_neg at hj
    rw [dif_neg (not_lt.mpr hj)]
    have hd_pos : 0 < d := by
      rcases Nat.eq_zero_or_pos d with hd0 | hdp
      · exfalso
        have hj_lt := j.isLt
        subst hd0
        simp at hj_lt
        omega
      · exact hdp
    set r : ℕ := j.val - m with hr_def
    have hjm : j.val = m + r := by omega
    set k : ℕ := r / d with hk_def
    set i : ℕ := r % d with hi_def
    have hr_lt : r < m * d := by
      have := j.isLt; omega
    have hk_lt : k < m := by
      rw [hk_def]
      exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hr_lt)
    have hi_lt : i < d := by rw [hi_def]; exact Nat.mod_lt r hd_pos
    have hkd : k * d + i = r := by
      rw [hk_def, hi_def]
      have := Nat.div_add_mod r d; linarith
    -- Now the goal is the `let`-form; peel it
    show (if hk : (j.val - m) / d < m then
            if hi : (j.val - m) % d < d then
              (WithLp.equiv 2 (Fin d → ℝ)) ((ParamL2.toParam θ).2 ⟨(j.val - m) / d, hk⟩)
                ⟨(j.val - m) % d, hi⟩
            else (0 : ℝ)
          else (0 : ℝ)) = θ j
    have hk_lt' : (j.val - m) / d < m := by rw [← hr_def, ← hk_def]; exact hk_lt
    have hi_lt' : (j.val - m) % d < d := by rw [← hr_def, ← hi_def]; exact hi_lt
    rw [dif_pos hk_lt', dif_pos hi_lt']
    -- Unfold toParam.2
    show (WithLp.equiv 2 (Fin d → ℝ))
            ((WithLp.equiv 2 (Fin d → ℝ)).symm
              (fun i' : Fin d =>
                θ (ParamL2.wIdx m d ⟨(j.val - m) / d, hk_lt'⟩ i')))
            ⟨(j.val - m) % d, hi_lt'⟩ = θ j
    rw [Equiv.apply_symm_apply]
    have hwidx : (ParamL2.wIdx m d ⟨(j.val - m) / d, hk_lt'⟩
                    ⟨(j.val - m) % d, hi_lt'⟩) = j := by
      apply Fin.ext
      show m + ((j.val - m) / d) * d + (j.val - m) % d = j.val
      have hr : (j.val - m) / d * d + (j.val - m) % d = j.val - m := by
        rw [← hr_def, ← hk_def, ← hi_def]; exact hkd
      omega
    rw [hwidx]

/-- Round-trip on `(a, w)`: `toParam ∘ ofParam = id`. -/
lemma ParamL2.toParam_ofParam (θ : Param d m) :
    ParamL2.toParam (ParamL2.ofParam θ) = θ := by
  classical
  refine Prod.ext ?_ ?_
  · -- a-block
    funext k
    -- (toParam (ofParam θ)).1 k = ofParam θ (aIdx m d k) = branch based on aIdx.val < m
    have hLHS : (ParamL2.toParam (ParamL2.ofParam θ)).1 k =
        (if h : (ParamL2.aIdx m d k).val < m then θ.1 ⟨(ParamL2.aIdx m d k).val, h⟩
         else
          let r := (ParamL2.aIdx m d k).val - m
          let k' := r / d
          let i' := r % d
          if hk : k' < m then
            if hi : i' < d then
              (WithLp.equiv 2 (Fin d → ℝ)) (θ.2 ⟨k', hk⟩) ⟨i', hi⟩
            else (0 : ℝ)
          else (0 : ℝ)) := rfl
    rw [hLHS]
    have hk : (ParamL2.aIdx m d k).val < m := k.isLt
    rw [dif_pos hk]
    -- goal: θ.1 ⟨(aIdx m d k).val, hk⟩ = θ.1 k
    congr 1
  · -- w-block
    funext k
    apply PiLp.ext
    intro i
    -- Compute LHS: (toParam (ofParam θ)).2 k i
    -- toParam.2 k = (WithLp.equiv 2 _).symm (fun i' => ofParam θ (wIdx m d k i'))
    -- So (toParam.2 k) i = (WithLp.equiv 2 _) applied to something evaluated at i
    -- The way we can reduce this: use LinearIsometryEquiv.apply_symm_apply
    have hLHS : (ParamL2.toParam (ParamL2.ofParam θ)).2 k =
        (WithLp.equiv 2 (Fin d → ℝ)).symm
          (fun i' : Fin d => (ParamL2.ofParam θ) (ParamL2.wIdx m d k i')) := rfl
    rw [hLHS]
    -- After PiLp.ext, goal at index i:
    -- ((WithLp.equiv 2 (Fin d → ℝ)).symm (fun i' => …)) i = θ.2 k i
    -- These are equal via `LinearIsometryEquiv.symm_apply` composed with coe
    show ((WithLp.equiv 2 (Fin d → ℝ)).symm
              (fun i' : Fin d => (ParamL2.ofParam θ) (ParamL2.wIdx m d k i'))) i =
          θ.2 k i
    -- The LHS coercion `θ' i` for θ' : PiLp 2 (fun _ => ℝ) is ofLp θ' i.
    -- With `θ' := (WithLp.equiv 2 (Fin d → ℝ)).symm f`, we have `ofLp θ' = f` by defeq.
    show (ParamL2.ofParam θ) (ParamL2.wIdx m d k i) = θ.2 k i
    -- Unfold ofParam at index wIdx m d k i.
    have hRHS_ofParam : (ParamL2.ofParam θ) (ParamL2.wIdx m d k i) =
        (if h : (ParamL2.wIdx m d k i).val < m then
            θ.1 ⟨(ParamL2.wIdx m d k i).val, h⟩
         else
          let r := (ParamL2.wIdx m d k i).val - m
          let k' := r / d
          let i' := r % d
          if hk : k' < m then
            if hi : i' < d then
              (WithLp.equiv 2 (Fin d → ℝ)) (θ.2 ⟨k', hk⟩) ⟨i', hi⟩
            else (0 : ℝ)
          else (0 : ℝ)) := rfl
    rw [hRHS_ofParam]
    have hd_pos : 0 < d := lt_of_le_of_lt (Nat.zero_le _) i.isLt
    have hval : (ParamL2.wIdx m d k i).val = m + k.val * d + i.val := rfl
    have hne : ¬ ((ParamL2.wIdx m d k i).val < m) := by rw [hval]; omega
    rw [dif_neg hne]
    have hr_eq : (ParamL2.wIdx m d k i).val - m = k.val * d + i.val := by
      rw [hval]; omega
    have hdiv : (k.val * d + i.val) / d = k.val := by
      have h1 : k.val * d + i.val = i.val + d * k.val := by ring
      rw [h1, Nat.add_mul_div_left _ _ hd_pos]
      have : i.val / d = 0 := Nat.div_eq_of_lt i.isLt
      omega
    have hmod : (k.val * d + i.val) % d = i.val := by
      have h1 : k.val * d + i.val = i.val + d * k.val := by ring
      rw [h1, Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt i.isLt
    have hk_lt' : (k.val * d + i.val) / d < m := by rw [hdiv]; exact k.isLt
    have hi_lt' : (k.val * d + i.val) % d < d := by rw [hmod]; exact i.isLt
    -- After dif_neg, expression becomes let r := wIdx.val - m; …
    -- Rewrite r using hr_eq
    show (let r := (ParamL2.wIdx m d k i).val - m
          let k' := r / d
          let i' := r % d
          if hk : k' < m then
            if hi : i' < d then
              (WithLp.equiv 2 (Fin d → ℝ)) (θ.2 ⟨k', hk⟩) ⟨i', hi⟩
            else (0 : ℝ)
          else (0 : ℝ))
        = θ.2 k i
    simp only [hr_eq]
    -- Now: let k' := (k.val * d + i.val) / d = k.val; let i' := (k.val * d + i.val) % d = i.val
    rw [dif_pos hk_lt', dif_pos hi_lt']
    have hk_eq : (⟨(k.val * d + i.val) / d, hk_lt'⟩ : Fin m) = k := by
      apply Fin.ext; simpa using hdiv
    have hi_eq : (⟨(k.val * d + i.val) % d, hi_lt'⟩ : Fin d) = i := by
      apply Fin.ext; simpa using hmod
    rw [hk_eq, hi_eq]
    -- Now: (WithLp.equiv 2 (Fin d → ℝ)) (θ.2 k) i = θ.2 k i
    rfl

/-! ### The linear equivalence -/

/-- **Linear equivalence** between the flat L² parameter space and the
existing sup-normed `Param d m`.  This is NOT an isometry — the norms
differ by the sup/L² gap quantified in `param_sup_le_paramL2` and
`paramL2_le_scale_param_sup` below. -/
noncomputable def paramL2Equiv (d m : ℕ) : ParamL2 d m ≃ₗ[ℝ] Param d m where
  toFun := ParamL2.toParam
  map_add' := ParamL2.toParam_add
  map_smul' c θ := by simpa using ParamL2.toParam_smul c θ
  invFun := ParamL2.ofParam
  left_inv := ParamL2.ofParam_toParam
  right_inv := ParamL2.toParam_ofParam

/-- User-facing alias: unwrap an L² vector into `Param d m`. -/
noncomputable def ParamL2.unwrap (θ : ParamL2 d m) : Param d m := paramL2Equiv d m θ

/-- User-facing alias: wrap a `Param d m` back into L² form. -/
noncomputable def ParamL2.wrap (θ : Param d m) : ParamL2 d m := (paramL2Equiv d m).symm θ

/-! ### Norm comparison -/

/-- L² norm squared equals sum of squared flat coordinates. -/
private lemma paramL2_norm_sq (θ : ParamL2 d m) :
    ‖θ‖ ^ 2 = ∑ j : Fin (m + m * d), (θ j) ^ 2 := by
  have := (PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin (m + m * d) => ℝ) θ)
  simpa [Real.norm_eq_abs, sq_abs] using this

/-- **Sup-norm ≤ L² norm** on the parameter space.

The sup-norm of `θ.toParam` picks one coordinate; the L² norm sums
squares over all coordinates.  Since each `a_k` and each `w_k i` is a
single flat coordinate, the pointwise bound propagates to the sup. -/
theorem param_sup_le_paramL2 (θ : ParamL2 d m) :
    ‖ParamL2.toParam θ‖ ≤ ‖θ‖ := by
  classical
  set ϑ : Param d m := ParamL2.toParam θ with hϑ_def
  have hL2_sq := paramL2_norm_sq θ
  have hθ_nonneg : 0 ≤ ‖θ‖ := norm_nonneg _
  -- Each flat coordinate is ≤ ‖θ‖ (in absolute value)
  have h_coord : ∀ j : Fin (m + m * d), |θ j| ≤ ‖θ‖ := by
    intro j
    have hsq : (θ j) ^ 2 ≤ ‖θ‖ ^ 2 := by
      rw [hL2_sq]
      exact Finset.single_le_sum
        (f := fun j' : Fin (m + m * d) => (θ j') ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq_eq_abs, Real.sqrt_sq hθ_nonneg] at h
  -- a-block: ∀ k, ‖ϑ.1 k‖ ≤ ‖θ‖
  have h_a : ∀ k : Fin m, ‖ϑ.1 k‖ ≤ ‖θ‖ := by
    intro k
    have := h_coord (ParamL2.aIdx m d k)
    -- ϑ.1 k = θ (aIdx m d k)
    show ‖(ParamL2.toParam θ).1 k‖ ≤ ‖θ‖
    show ‖θ (ParamL2.aIdx m d k)‖ ≤ ‖θ‖
    simpa [Real.norm_eq_abs] using this
  -- w-block: ∀ k, ‖ϑ.2 k‖ ≤ ‖θ‖
  have h_w : ∀ k : Fin m, ‖ϑ.2 k‖ ≤ ‖θ‖ := by
    intro k
    have hwn : ‖ϑ.2 k‖ ^ 2 =
        ∑ i : Fin d, (θ (ParamL2.wIdx m d k i)) ^ 2 := by
      have hexp :
          (ϑ.2 k) = (WithLp.equiv 2 (Fin d → ℝ)).symm
              (fun i : Fin d => θ (ParamL2.wIdx m d k i)) := rfl
      have hEnorm : ‖ϑ.2 k‖ ^ 2 =
          ∑ i : Fin d, ((WithLp.equiv 2 (Fin d → ℝ)) (ϑ.2 k) i) ^ 2 := by
        have := (PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin d => ℝ) (ϑ.2 k))
        simpa [Real.norm_eq_abs, sq_abs] using this
      rw [hEnorm]
      apply Finset.sum_congr rfl
      intro i _
      rw [hexp]
      simp
    -- injectivity of wIdx m d k
    have hinj : Function.Injective (ParamL2.wIdx m d k) := by
      intro i₁ i₂ hEq
      have h1 : (m + k.val * d + i₁.val : ℕ) = m + k.val * d + i₂.val := by
        have := congrArg Fin.val hEq
        simpa using this
      exact Fin.ext (by omega)
    have hSubset :
        ((Finset.univ : Finset (Fin d)).image (ParamL2.wIdx m d k))
          ⊆ (Finset.univ : Finset (Fin (m + m * d))) :=
      fun j _ => Finset.mem_univ _
    have hbound :
        ∑ i : Fin d, (θ (ParamL2.wIdx m d k i)) ^ 2
          ≤ ∑ j : Fin (m + m * d), (θ j) ^ 2 := by
      have himg :
          ∑ j ∈ (Finset.univ : Finset (Fin d)).image (ParamL2.wIdx m d k),
              (θ j) ^ 2
          = ∑ i : Fin d, (θ (ParamL2.wIdx m d k i)) ^ 2 := by
        rw [Finset.sum_image]
        intro i _ i' _ h; exact hinj h
      calc ∑ i : Fin d, (θ (ParamL2.wIdx m d k i)) ^ 2
          = ∑ j ∈ (Finset.univ : Finset (Fin d)).image (ParamL2.wIdx m d k),
              (θ j) ^ 2 := himg.symm
        _ ≤ ∑ j : Fin (m + m * d), (θ j) ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg hSubset
                (fun j _ _ => sq_nonneg _)
    have hle_sq : ‖ϑ.2 k‖ ^ 2 ≤ ‖θ‖ ^ 2 := by rw [hwn, hL2_sq]; exact hbound
    have h1 : 0 ≤ ‖ϑ.2 k‖ := norm_nonneg _
    have := Real.sqrt_le_sqrt hle_sq
    rwa [Real.sqrt_sq h1, Real.sqrt_sq hθ_nonneg] at this
  -- Combine: ‖ϑ‖ = max ‖ϑ.1‖ ‖ϑ.2‖
  have h_a_all : ‖ϑ.1‖ ≤ ‖θ‖ := by
    rcases isEmpty_or_nonempty (Fin m) with hne | hne
    · have hzero : ϑ.1 = 0 := by funext k; exact (hne.false k).elim
      simp [hzero, hθ_nonneg]
    · exact (pi_norm_le_iff_of_nonempty (f := ϑ.1) (r := ‖θ‖)).2 h_a
  have h_w_all : ‖ϑ.2‖ ≤ ‖θ‖ := by
    rcases isEmpty_or_nonempty (Fin m) with hne | hne
    · have hzero : ϑ.2 = 0 := by funext k; exact (hne.false k).elim
      simp [hzero, hθ_nonneg]
    · exact (pi_norm_le_iff_of_nonempty (f := ϑ.2) (r := ‖θ‖)).2 h_w
  have hProd : ‖ϑ‖ = max ‖ϑ.1‖ ‖ϑ.2‖ := Prod.norm_def ϑ
  rw [hProd]
  exact max_le h_a_all h_w_all

/-- **L² norm ≤ √(m + m · d) · sup-norm** on the parameter space.

If `M = ‖ParamL2.toParam θ‖` is the sup-norm, then each flat coordinate
has absolute value at most `M`, so the sum of squares is at most
`(m + m · d) · M ^ 2`, and the L² norm at most `√(m + m · d) · M`. -/
theorem paramL2_le_scale_param_sup (θ : ParamL2 d m) :
    ‖θ‖ ≤ Real.sqrt ((m + m * d : ℕ) : ℝ) * ‖ParamL2.toParam θ‖ := by
  classical
  set ϑ : Param d m := ParamL2.toParam θ with hϑ_def
  set M : ℝ := ‖ϑ‖ with hM_def
  have hM_nonneg : 0 ≤ M := norm_nonneg _
  have hL2_sq := paramL2_norm_sq θ
  -- Show each flat coordinate (θ j)^2 ≤ M^2
  have h_coord : ∀ j : Fin (m + m * d), (θ j) ^ 2 ≤ M ^ 2 := by
    intro j
    by_cases hj : j.val < m
    · -- a-block: θ j = ϑ.1 ⟨j.val, hj⟩
      set k : Fin m := ⟨j.val, hj⟩ with hk_def
      have hAidx : (ParamL2.aIdx m d k) = j := Fin.ext rfl
      have hcoord : θ j = ϑ.1 k := by
        show θ j = θ (ParamL2.aIdx m d k)
        rw [hAidx]
      rw [hcoord]
      have h1 : ‖ϑ.1 k‖ ≤ ‖ϑ.1‖ := norm_le_pi_norm ϑ.1 k
      have h2 : ‖ϑ.1‖ ≤ M := by rw [hM_def, Prod.norm_def]; exact le_max_left _ _
      have h3 : |ϑ.1 k| ≤ M := by
        have := h1.trans h2
        simpa [Real.norm_eq_abs] using this
      have := pow_le_pow_left₀ (abs_nonneg _) h3 2
      simpa [sq_abs] using this
    · -- w-block
      push_neg at hj
      have hd_pos : 0 < d := by
        rcases Nat.eq_zero_or_pos d with hd0 | hdp
        · exfalso
          have hj_lt := j.isLt
          subst hd0
          simp at hj_lt
          omega
        · exact hdp
      set r : ℕ := j.val - m with hr_def
      set k : ℕ := r / d with hk_def
      set i : ℕ := r % d with hi_def
      have hr_lt : r < m * d := by
        have := j.isLt; omega
      have hk_lt : k < m := by
        rw [hk_def]
        exact Nat.div_lt_of_lt_mul (by simpa [Nat.mul_comm] using hr_lt)
      have hi_lt : i < d := by rw [hi_def]; exact Nat.mod_lt r hd_pos
      have hkd : k * d + i = r := by
        rw [hk_def, hi_def]
        have := Nat.div_add_mod r d; linarith
      have hAidx : (ParamL2.wIdx m d ⟨k, hk_lt⟩ ⟨i, hi_lt⟩) = j := by
        apply Fin.ext
        show m + k * d + i = j.val
        omega
      have hcoord : θ j =
          (WithLp.equiv 2 (Fin d → ℝ)) (ϑ.2 ⟨k, hk_lt⟩) ⟨i, hi_lt⟩ := by
        show θ j = (WithLp.equiv 2 (Fin d → ℝ))
                     ((WithLp.equiv 2 (Fin d → ℝ)).symm
                        (fun i' : Fin d =>
                          θ (ParamL2.wIdx m d ⟨k, hk_lt⟩ i'))) ⟨i, hi_lt⟩
        rw [Equiv.apply_symm_apply]
        rw [hAidx]
      rw [hcoord]
      -- Bound: |(equiv) (ϑ.2 ⟨k, hk_lt⟩) ⟨i, hi_lt⟩| ≤ M
      -- Step 1: coord ≤ ‖ϑ.2 ⟨k, hk_lt⟩‖
      have hL2 : ‖ϑ.2 ⟨k, hk_lt⟩‖ ^ 2 =
          ∑ i' : Fin d,
            ((WithLp.equiv 2 (Fin d → ℝ)) (ϑ.2 ⟨k, hk_lt⟩) i') ^ 2 := by
        have := (PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin d => ℝ) (ϑ.2 ⟨k, hk_lt⟩))
        simpa [Real.norm_eq_abs, sq_abs] using this
      have hs :
          ((WithLp.equiv 2 (Fin d → ℝ)) (ϑ.2 ⟨k, hk_lt⟩) ⟨i, hi_lt⟩) ^ 2
            ≤ ∑ i' : Fin d,
                ((WithLp.equiv 2 (Fin d → ℝ)) (ϑ.2 ⟨k, hk_lt⟩) i') ^ 2 :=
        Finset.single_le_sum
          (f := fun i' : Fin d =>
                  ((WithLp.equiv 2 (Fin d → ℝ)) (ϑ.2 ⟨k, hk_lt⟩) i') ^ 2)
          (fun _ _ => sq_nonneg _) (Finset.mem_univ _)
      have hsq_kn :
          ((WithLp.equiv 2 (Fin d → ℝ)) (ϑ.2 ⟨k, hk_lt⟩) ⟨i, hi_lt⟩) ^ 2
            ≤ ‖ϑ.2 ⟨k, hk_lt⟩‖ ^ 2 := by rw [hL2]; exact hs
      have h2n : ‖ϑ.2 ⟨k, hk_lt⟩‖ ≤ ‖ϑ.2‖ := norm_le_pi_norm ϑ.2 _
      have h3n : ‖ϑ.2‖ ≤ M := by rw [hM_def, Prod.norm_def]; exact le_max_right _ _
      have h_kn_sq_M : ‖ϑ.2 ⟨k, hk_lt⟩‖ ^ 2 ≤ M ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (h2n.trans h3n) 2
      exact hsq_kn.trans h_kn_sq_M
  -- Sum-of-squares bound
  have hSum : (∑ j : Fin (m + m * d), (θ j) ^ 2)
                ≤ (m + m * d : ℕ) * M ^ 2 := by
    have h1 : ∑ _j : Fin (m + m * d), M ^ 2 = (m + m * d : ℕ) * M ^ 2 := by
      simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc ∑ j : Fin (m + m * d), (θ j) ^ 2
        ≤ ∑ _j : Fin (m + m * d), M ^ 2 :=
          Finset.sum_le_sum (fun j _ => h_coord j)
      _ = (m + m * d : ℕ) * M ^ 2 := h1
  have hθ_sq : ‖θ‖ ^ 2 ≤ (m + m * d : ℕ) * M ^ 2 := by rw [hL2_sq]; exact hSum
  have hn_nonneg : (0 : ℝ) ≤ ((m + m * d : ℕ) : ℝ) := by exact_mod_cast Nat.zero_le _
  have hprod_nonneg : 0 ≤ Real.sqrt ((m + m * d : ℕ) : ℝ) * M :=
    mul_nonneg (Real.sqrt_nonneg _) hM_nonneg
  have hRHS_sq :
      (Real.sqrt ((m + m * d : ℕ) : ℝ) * M) ^ 2 = (m + m * d : ℕ) * M ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hn_nonneg]
  have h_sq : ‖θ‖ ^ 2 ≤ (Real.sqrt ((m + m * d : ℕ) : ℝ) * M) ^ 2 := by
    rw [hRHS_sq]; exact hθ_sq
  have hθ_nonneg : 0 ≤ ‖θ‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖θ‖ - Real.sqrt ((m + m * d : ℕ) : ℝ) * M),
             h_sq, hθ_nonneg, hprod_nonneg]

end ProbabilityTheory
