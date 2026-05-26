/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.FullNetwork
import LTFP.MathlibExt.Probability.GradNeuronNTK
import LTFP.MathlibExt.Probability.NTKConcentration

/-!
# Entrywise bound for the dynamic training kernel

**R4 NTK Part E3c.1 — bounded-entry estimate for `fullTrainingKernel`.**

Part E3a defined the parameter-dependent training kernel
`fullTrainingKernel σ σ' b θ xs`, which at initialization
(when `a_j ^ 2 = 1`) coincides with the random-feature kernel
`empiricalFullNTK σ σ' xs ω` (Part E2). This file delivers the
*entrywise* magnitude bound on the training kernel at an arbitrary
parameter `θ = (a, w)`:

  `|fullTrainingKernel σ σ' b θ xs r s|`
    `≤ M ^ 2 + ((∑ j, a_j ^ 2) / m) * M' ^ 2 * G`,

where `M`, `M'` are uniform bounds on `σ`, `σ'`, and `G` bounds the
data-Gram `|⟨xs r, xs s⟩| ≤ G`. The σ-block contributes the `M ^ 2`
term (free of `a`), and the σ'-block contributes the
`(avg a²) * M'^2 * G` term, with the `(1/m) Σ_j a_j ^ 2` factor
recording the dependence on the *output-weight energy*.

This is the per-entry analogue of the operator-norm bound that
downstream operator-norm lifts (E3d) will derive. The drift form
(comparing `K_θ` with `K_{θ_0}`) requires additional Lipschitz
hypotheses on `σ` and `σ'` and is deferred to Part E3c.2.

## Main result

* `fullTrainingKernel_apply_abs_le` — for any parameter `θ`,
  `|fullTrainingKernel σ σ' b θ xs r s|`
    `≤ M ^ 2 + ((∑ j, θ.1 j ^ 2) / m) * M' ^ 2 * G`.

The bound is sharp up to constants: at initialization
(`a_j ^ 2 = 1`, so `(∑ a_j ^ 2) / m = 1`), the σ'-block contribution
collapses to `M'^2 * G`, matching `gradNeuronNTK_abs_le`.
-/

namespace ProbabilityTheory

open MeasureTheory BigOperators Matrix

variable {d : ℕ}

/-! ### Entrywise bound -/

/-- **Entrywise magnitude bound for the dynamic training kernel.**

Let `σ, σ' : ℝ → ℝ` be bounded by `M, M'` respectively, let
`xs : Fin n → EuclideanSpace ℝ (Fin d)` be data with bounded Gram
`|⟨xs r, xs s⟩| ≤ G`, and let `θ = (a, w)` be any parameter. Then
each entry of the dynamic training kernel satisfies

  `|fullTrainingKernel σ σ' b θ xs r s|`
    `≤ M ^ 2 + ((∑ j, a_j ^ 2) / m) * M' ^ 2 * G`.

**Proof sketch.** The training kernel decomposes as a σ-block plus a
σ'-block (Part E3a). Apply the triangle inequality `|x + y| ≤ |x| + |y|`
to split:

* **σ-block.** Each summand factor `|σ(·)| ≤ M`, so
  `|σ(·) · σ(·)| ≤ M * M = M^2`, and the average
  `(1/m) Σ_j σ(·) σ(·)` has magnitude at most `M^2`.

* **σ'-block.** Each summand `a_j^2 · σ'(·) · σ'(·) · ⟨x_r, x_s⟩` has
  magnitude `a_j^2 · M'^2 · G` (the `a_j^2` factor is already
  nonnegative). Averaging over `j ∈ Fin m` gives
  `((∑ j, a_j ^ 2) / m) * M'^2 * G`.

Adding the two block bounds yields the claim.

This is the per-entry analogue of an operator-norm bound; downstream
the Frobenius lift gives `‖fullTrainingKernel‖_F ≤ n · (…)` and the
operator-norm lift gives `‖fullTrainingKernel‖_op ≤ n · (…)`. -/
theorem fullTrainingKernel_apply_abs_le
    {n m : ℕ}
    (σ σ' : ℝ → ℝ)
    {M M' G : ℝ}
    (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (hσ_bdd : ∀ z, |σ z| ≤ M)
    (hσ'_bdd : ∀ z, |σ' z| ≤ M')
    (b : Fin m → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (hG : ∀ a b, |inner ℝ (xs a) (xs b)| ≤ G)
    (θ : Param d m)
    (r s : Fin n) :
    |fullTrainingKernel σ σ' b θ xs r s|
      ≤ M ^ 2 + ((∑ j, θ.1 j ^ 2) / (m : ℝ)) * M' ^ 2 * G := by
  classical
  -- 0 ≤ G follows from |⟨x, x'⟩| ≤ G applied at r = s.
  have hG_nn : 0 ≤ G := le_trans (abs_nonneg _) (hG r s)
  -- Abbreviations for the two blocks.
  set Sσ : ℝ :=
      ∑ j, σ (inner ℝ (θ.2 j) (xs r) + b j) *
              σ (inner ℝ (θ.2 j) (xs s) + b j) with hSσ_def
  set Sσ' : ℝ :=
      ∑ j, θ.1 j ^ 2 *
              σ' (inner ℝ (θ.2 j) (xs r) + b j) *
              σ' (inner ℝ (θ.2 j) (xs s) + b j) *
              inner ℝ (xs r) (xs s) with hSσ'_def
  -- Rewrite the LHS as a single (a+b) and split via triangle.
  have hLHS : fullTrainingKernel σ σ' b θ xs r s
      = (1 / (m : ℝ)) * Sσ + (1 / (m : ℝ)) * Sσ' := by
    unfold fullTrainingKernel
    rfl
  rw [hLHS]
  -- Bound each block separately.
  -- σ-block: |Sσ| ≤ m * M^2, hence (1/m) * Sσ has |.| ≤ M^2.
  have h_sigma_summand :
      ∀ j : Fin m,
        |σ (inner ℝ (θ.2 j) (xs r) + b j) *
            σ (inner ℝ (θ.2 j) (xs s) + b j)|
          ≤ M * M := by
    intro j
    rw [abs_mul]
    exact mul_le_mul (hσ_bdd _) (hσ_bdd _) (abs_nonneg _) hM
  have h_Sσ_abs : |Sσ| ≤ (m : ℝ) * (M * M) := by
    have hsum_abs : |Sσ| ≤
        ∑ j : Fin m,
          |σ (inner ℝ (θ.2 j) (xs r) + b j) *
              σ (inner ℝ (θ.2 j) (xs s) + b j)| := by
      rw [hSσ_def]
      exact Finset.abs_sum_le_sum_abs
        (f := fun j => σ (inner ℝ (θ.2 j) (xs r) + b j) *
                        σ (inner ℝ (θ.2 j) (xs s) + b j))
        (s := (Finset.univ : Finset (Fin m)))
    have hsum_const :
        ∑ _j : Fin m, (M * M) = (m : ℝ) * (M * M) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc |Sσ|
        ≤ ∑ j : Fin m,
            |σ (inner ℝ (θ.2 j) (xs r) + b j) *
                σ (inner ℝ (θ.2 j) (xs s) + b j)| := hsum_abs
      _ ≤ ∑ _j : Fin m, M * M :=
          Finset.sum_le_sum (fun j _ => h_sigma_summand j)
      _ = (m : ℝ) * (M * M) := hsum_const
  -- σ'-block. Each summand absolute value: a_j^2 * M'^2 * G.
  -- Note a_j^2 ≥ 0 so |a_j^2 ...| = a_j^2 * |σ' σ' inner|.
  have h_grad_summand :
      ∀ j : Fin m,
        |θ.1 j ^ 2 *
            σ' (inner ℝ (θ.2 j) (xs r) + b j) *
            σ' (inner ℝ (θ.2 j) (xs s) + b j) *
            inner ℝ (xs r) (xs s)|
          ≤ θ.1 j ^ 2 * (M' * M' * G) := by
    intro j
    have ha_sq_nn : 0 ≤ θ.1 j ^ 2 := sq_nonneg _
    -- Take out the nonneg a_j^2.
    have h_eq :
        |θ.1 j ^ 2 *
            σ' (inner ℝ (θ.2 j) (xs r) + b j) *
            σ' (inner ℝ (θ.2 j) (xs s) + b j) *
            inner ℝ (xs r) (xs s)|
          = θ.1 j ^ 2 *
              (|σ' (inner ℝ (θ.2 j) (xs r) + b j)| *
                |σ' (inner ℝ (θ.2 j) (xs s) + b j)| *
                |inner ℝ (xs r) (xs s)|) := by
      rw [show θ.1 j ^ 2 *
              σ' (inner ℝ (θ.2 j) (xs r) + b j) *
              σ' (inner ℝ (θ.2 j) (xs s) + b j) *
              inner ℝ (xs r) (xs s)
            = θ.1 j ^ 2 *
                (σ' (inner ℝ (θ.2 j) (xs r) + b j) *
                  σ' (inner ℝ (θ.2 j) (xs s) + b j) *
                  inner ℝ (xs r) (xs s)) from by ring]
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg ha_sq_nn]
    rw [h_eq]
    -- Bound the |σ' σ' inner| part by M' * M' * G.
    have h_prefix : |σ' (inner ℝ (θ.2 j) (xs r) + b j)| *
        |σ' (inner ℝ (θ.2 j) (xs s) + b j)| ≤ M' * M' :=
      mul_le_mul (hσ'_bdd _) (hσ'_bdd _) (abs_nonneg _) hM'
    have h_triple :
        |σ' (inner ℝ (θ.2 j) (xs r) + b j)| *
            |σ' (inner ℝ (θ.2 j) (xs s) + b j)| *
            |inner ℝ (xs r) (xs s)|
          ≤ M' * M' * G :=
      mul_le_mul h_prefix (hG r s) (abs_nonneg _) (mul_nonneg hM' hM')
    exact mul_le_mul_of_nonneg_left h_triple ha_sq_nn
  have hM'2G_nn : 0 ≤ M' * M' * G := mul_nonneg (mul_nonneg hM' hM') hG_nn
  have h_Sσ'_abs :
      |Sσ'| ≤ (∑ j, θ.1 j ^ 2) * (M' * M' * G) := by
    have hsum_abs : |Sσ'| ≤
        ∑ j : Fin m,
          |θ.1 j ^ 2 *
              σ' (inner ℝ (θ.2 j) (xs r) + b j) *
              σ' (inner ℝ (θ.2 j) (xs s) + b j) *
              inner ℝ (xs r) (xs s)| := by
      rw [hSσ'_def]
      exact Finset.abs_sum_le_sum_abs
        (f := fun j => θ.1 j ^ 2 *
                σ' (inner ℝ (θ.2 j) (xs r) + b j) *
                σ' (inner ℝ (θ.2 j) (xs s) + b j) *
                inner ℝ (xs r) (xs s))
        (s := (Finset.univ : Finset (Fin m)))
    have hsum_bound :
        ∑ j : Fin m,
            |θ.1 j ^ 2 *
              σ' (inner ℝ (θ.2 j) (xs r) + b j) *
              σ' (inner ℝ (θ.2 j) (xs s) + b j) *
              inner ℝ (xs r) (xs s)|
          ≤ ∑ j : Fin m, θ.1 j ^ 2 * (M' * M' * G) :=
        Finset.sum_le_sum (fun j _ => h_grad_summand j)
    have hsum_factor :
        ∑ j : Fin m, θ.1 j ^ 2 * (M' * M' * G)
          = (∑ j, θ.1 j ^ 2) * (M' * M' * G) := by
      rw [← Finset.sum_mul]
    calc |Sσ'|
        ≤ ∑ j : Fin m,
            |θ.1 j ^ 2 *
              σ' (inner ℝ (θ.2 j) (xs r) + b j) *
              σ' (inner ℝ (θ.2 j) (xs s) + b j) *
              inner ℝ (xs r) (xs s)| := hsum_abs
      _ ≤ ∑ j : Fin m, θ.1 j ^ 2 * (M' * M' * G) := hsum_bound
      _ = (∑ j, θ.1 j ^ 2) * (M' * M' * G) := hsum_factor
  -- Combine the two block bounds.
  -- |a + b| ≤ |a| + |b|.
  have h_tri :
      |(1 / (m : ℝ)) * Sσ + (1 / (m : ℝ)) * Sσ'|
        ≤ |(1 / (m : ℝ)) * Sσ| + |(1 / (m : ℝ)) * Sσ'| :=
    abs_add_le _ _
  -- Two cases: m = 0 vs m > 0.
  rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
  · -- m = 0: empty sums, both blocks vanish, RHS = M^2 + 0 = M^2 ≥ 0.
    subst hm0
    have hSσ_zero : Sσ = 0 := by
      simp [hSσ_def]
    have hSσ'_zero : Sσ' = 0 := by
      simp [hSσ'_def]
    have hsum_a2_zero : (∑ j : Fin 0, θ.1 j ^ 2) = 0 := by
      simp
    -- LHS = 0; RHS ≥ 0.
    have hM2_nn : 0 ≤ M ^ 2 := sq_nonneg _
    have hM'2_nn : 0 ≤ M' ^ 2 := sq_nonneg _
    have h_rhs_nn :
        0 ≤ M ^ 2 + ((∑ j : Fin 0, θ.1 j ^ 2) / ((0 : ℕ) : ℝ)) * M' ^ 2 * G := by
      rw [hsum_a2_zero]
      simp
      exact hM2_nn
    have h_lhs_zero :
        (1 / ((0 : ℕ) : ℝ)) * Sσ + (1 / ((0 : ℕ) : ℝ)) * Sσ' = 0 := by
      rw [hSσ_zero, hSσ'_zero]; ring
    rw [h_lhs_zero, abs_zero]
    exact h_rhs_nn
  · -- m > 0: divide by m.
    have hm_pos_real : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
    have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos_real
    have hm_nn : 0 ≤ (m : ℝ) := le_of_lt hm_pos_real
    have h_inv_nn : 0 ≤ 1 / (m : ℝ) := by positivity
    -- Bound |(1/m) * Sσ| ≤ M^2.
    have h_block1 : |(1 / (m : ℝ)) * Sσ| ≤ M ^ 2 := by
      rw [abs_mul, abs_of_nonneg h_inv_nn]
      have h_bound : (1 / (m : ℝ)) * |Sσ| ≤ (1 / (m : ℝ)) * ((m : ℝ) * (M * M)) :=
        mul_le_mul_of_nonneg_left h_Sσ_abs h_inv_nn
      have h_simplify : (1 / (m : ℝ)) * ((m : ℝ) * (M * M)) = M ^ 2 := by
        have hmm : (1 / (m : ℝ)) * (m : ℝ) = 1 := by
          field_simp
        calc (1 / (m : ℝ)) * ((m : ℝ) * (M * M))
            = ((1 / (m : ℝ)) * (m : ℝ)) * (M * M) := by ring
          _ = 1 * (M * M) := by rw [hmm]
          _ = M ^ 2 := by ring
      linarith [h_bound, h_simplify]
    -- Bound |(1/m) * Sσ'| ≤ ((∑ a^2) / m) * M'^2 * G.
    have h_block2 :
        |(1 / (m : ℝ)) * Sσ'|
          ≤ ((∑ j, θ.1 j ^ 2) / (m : ℝ)) * M' ^ 2 * G := by
      rw [abs_mul, abs_of_nonneg h_inv_nn]
      have h_bound :
          (1 / (m : ℝ)) * |Sσ'|
            ≤ (1 / (m : ℝ)) * ((∑ j, θ.1 j ^ 2) * (M' * M' * G)) :=
        mul_le_mul_of_nonneg_left h_Sσ'_abs h_inv_nn
      have h_simplify :
          (1 / (m : ℝ)) * ((∑ j, θ.1 j ^ 2) * (M' * M' * G))
            = ((∑ j, θ.1 j ^ 2) / (m : ℝ)) * M' ^ 2 * G := by
        have : (∑ j, θ.1 j ^ 2) / (m : ℝ)
                = (1 / (m : ℝ)) * (∑ j, θ.1 j ^ 2) := by ring
        rw [this]; ring
      linarith [h_bound, h_simplify]
    -- Combine.
    calc |(1 / (m : ℝ)) * Sσ + (1 / (m : ℝ)) * Sσ'|
        ≤ |(1 / (m : ℝ)) * Sσ| + |(1 / (m : ℝ)) * Sσ'| := h_tri
      _ ≤ M ^ 2 + ((∑ j, θ.1 j ^ 2) / (m : ℝ)) * M' ^ 2 * G := by
          linarith [h_block1, h_block2]

/-- **Entrywise bound under bounded output weights.**

Specialization of `fullTrainingKernel_apply_abs_le` when each output
weight `|a_j| ≤ Aa`: then `(∑ a_j ^ 2) / m ≤ Aa^2`, giving the
uniform bound

  `|fullTrainingKernel σ σ' b θ xs r s|`
    `≤ M ^ 2 + Aa^2 * M' ^ 2 * G`,

which is *independent of `m`* and of the particular parameter `θ`.

This is the form that downstream operator-norm lifts will use: it
gives a parameter-independent ceiling on each entry of the training
kernel along the entire trajectory, provided the output weights
remain in a uniform `Aa`-ball. -/
theorem fullTrainingKernel_apply_abs_le_of_bounded
    {n m : ℕ}
    (σ σ' : ℝ → ℝ)
    {M M' G Aa : ℝ}
    (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (hσ_bdd : ∀ z, |σ z| ≤ M)
    (hσ'_bdd : ∀ z, |σ' z| ≤ M')
    (b : Fin m → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (hG : ∀ a b, |inner ℝ (xs a) (xs b)| ≤ G)
    (hAa : 0 ≤ Aa)
    (θ : Param d m)
    (ha_bound : ∀ j, |θ.1 j| ≤ Aa)
    (r s : Fin n) :
    |fullTrainingKernel σ σ' b θ xs r s|
      ≤ M ^ 2 + Aa ^ 2 * M' ^ 2 * G := by
  classical
  have hG_nn : 0 ≤ G := le_trans (abs_nonneg _) (hG r s)
  have hM'2_nn : 0 ≤ M' ^ 2 := sq_nonneg _
  have hM'2G_nn : 0 ≤ M' ^ 2 * G := mul_nonneg hM'2_nn hG_nn
  -- The basic bound.
  have h_base :=
    fullTrainingKernel_apply_abs_le σ σ' hM hM' hσ_bdd hσ'_bdd b xs hG θ r s
  -- Bound the (∑ a^2) / m factor by Aa^2.
  -- Each a_j^2 ≤ Aa^2 via |a_j| ≤ Aa and sq_le_sq'.
  have h_aj_sq : ∀ j : Fin m, θ.1 j ^ 2 ≤ Aa ^ 2 := by
    intro j
    have h := ha_bound j
    -- |a_j| ≤ Aa implies a_j^2 ≤ Aa^2.
    have habs_sq : |θ.1 j| ^ 2 ≤ Aa ^ 2 := by
      have h_nn : 0 ≤ |θ.1 j| := abs_nonneg _
      exact pow_le_pow_left₀ h_nn h 2
    have hsq_eq : θ.1 j ^ 2 = |θ.1 j| ^ 2 := by
      rw [sq_abs]
    rw [hsq_eq]
    exact habs_sq
  -- Hence (∑ a^2) ≤ m * Aa^2.
  have h_sum_le :
      (∑ j, θ.1 j ^ 2) ≤ (m : ℝ) * Aa ^ 2 := by
    calc (∑ j, θ.1 j ^ 2)
        ≤ ∑ _j : Fin m, Aa ^ 2 := Finset.sum_le_sum (fun j _ => h_aj_sq j)
      _ = (m : ℝ) * Aa ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- 0 ≤ (∑ a^2).
  have h_sum_nn : 0 ≤ (∑ j, θ.1 j ^ 2) :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  -- Two cases: m = 0 vs m > 0.
  rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
  · subst hm0
    -- Empty sum: (∑ a^2) = 0, and (0/0) = 0 in ℝ.
    have hsum_zero : (∑ j : Fin 0, θ.1 j ^ 2) = 0 := by simp
    have h_base' :
        |fullTrainingKernel σ σ' b θ xs r s|
          ≤ M ^ 2 + ((0 : ℝ) / ((0 : ℕ) : ℝ)) * M' ^ 2 * G := by
      have := h_base
      rw [hsum_zero] at this
      exact this
    have h_rhs_zero : ((0 : ℝ) / ((0 : ℕ) : ℝ)) * M' ^ 2 * G = 0 := by simp
    rw [h_rhs_zero] at h_base'
    have hAa2 : 0 ≤ Aa ^ 2 * M' ^ 2 * G :=
      mul_nonneg (mul_nonneg (sq_nonneg _) hM'2_nn) hG_nn
    linarith
  · have hm_pos_real : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
    have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos_real
    have h_avg_le : (∑ j, θ.1 j ^ 2) / (m : ℝ) ≤ Aa ^ 2 := by
      rw [div_le_iff₀ hm_pos_real]
      linarith [h_sum_le, mul_comm ((m : ℝ)) (Aa ^ 2)]
    have h_factor_le :
        ((∑ j, θ.1 j ^ 2) / (m : ℝ)) * M' ^ 2 * G ≤ Aa ^ 2 * M' ^ 2 * G := by
      have h1 : ((∑ j, θ.1 j ^ 2) / (m : ℝ)) * M' ^ 2
                  ≤ Aa ^ 2 * M' ^ 2 :=
        mul_le_mul_of_nonneg_right h_avg_le hM'2_nn
      exact mul_le_mul_of_nonneg_right h1 hG_nn
    linarith

/-! ### Operator-norm bound -/

open scoped Matrix.Norms.L2Operator in
/-- **Operator-norm bound for the dynamic training kernel under bounded output weights.**

Lifting the entrywise bound
`fullTrainingKernel_apply_abs_le_of_bounded` via the Cauchy–Schwarz
glue lemma `Matrix.l2_opNorm_le_card_mul_of_entry_le`, the `ℓ²`
operator norm of the dynamic training kernel is bounded by
`n · (M ^ 2 + Aa ^ 2 · M' ^ 2 · G)`:

  `‖fullTrainingKernel σ σ' b θ xs‖`
    `≤ n · (M ^ 2 + Aa ^ 2 · M' ^ 2 · G)`,

provided each output weight satisfies `|a_j| ≤ Aa`.

This is the operator-norm analogue of the per-entry bound
(Part E3c.1), and is the form downstream lazy-training arguments use
when controlling the training-kernel drift through `‖·‖`. The bound is
*parameter-free* on the right-hand side: it depends only on the data
envelopes `M, M', G, Aa`, not on the particular trajectory point `θ`. -/
theorem fullTrainingKernel_opNorm_le_of_bounded
    {n m : ℕ}
    (σ σ' : ℝ → ℝ)
    {M M' G Aa : ℝ}
    (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (hσ_bdd : ∀ z, |σ z| ≤ M)
    (hσ'_bdd : ∀ z, |σ' z| ≤ M')
    (b : Fin m → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (hG_nn : 0 ≤ G)
    (hG : ∀ a b : Fin n, |inner ℝ (xs a) (xs b)| ≤ G)
    (hAa : 0 ≤ Aa)
    (θ : Param d m)
    (ha_bound : ∀ j, |θ.1 j| ≤ Aa) :
    ‖fullTrainingKernel σ σ' b θ xs‖
      ≤ (n : ℝ) * (M ^ 2 + Aa ^ 2 * M' ^ 2 * G) := by
  classical
  -- The entrywise envelope `s := M^2 + Aa^2 * M'^2 * G ≥ 0`.
  set s : ℝ := M ^ 2 + Aa ^ 2 * M' ^ 2 * G with hs_def
  have hM2_nn : 0 ≤ M ^ 2 := sq_nonneg _
  have hAa2_nn : 0 ≤ Aa ^ 2 := sq_nonneg _
  have hM'2_nn : 0 ≤ M' ^ 2 := sq_nonneg _
  have hs_nn : 0 ≤ s := by
    have : 0 ≤ Aa ^ 2 * M' ^ 2 * G :=
      mul_nonneg (mul_nonneg hAa2_nn hM'2_nn) hG_nn
    linarith
  -- Entrywise: ‖K i j‖ ≤ s.
  have h_entry : ∀ i j : Fin n,
      ‖fullTrainingKernel σ σ' b θ xs i j‖ ≤ s := by
    intro i j
    have h := fullTrainingKernel_apply_abs_le_of_bounded
      σ σ' hM hM' hσ_bdd hσ'_bdd b xs hG hAa θ ha_bound i j
    simpa [Real.norm_eq_abs, hs_def] using h
  -- Apply the Cauchy–Schwarz glue lemma.
  have h_op :=
    Matrix.l2_opNorm_le_card_mul_of_entry_le
      (fullTrainingKernel σ σ' b θ xs) hs_nn h_entry
  rwa [Fintype.card_fin] at h_op

/-! ### Entrywise Lipschitz drift -/

/-- **Entrywise Lipschitz drift bound for the dynamic training kernel.**

Comparing the training kernel at two parameters `θ` and `θ₀` whose
output weights are uniformly bounded by `Aa` and whose per-neuron
joint deviation is at most `Δ` (i.e.
`dist (θ.1 j, θ.2 j) (θ₀.1 j, θ₀.2 j) ≤ Δ` for every `j`), each
entry of the training kernel drifts by at most a linear function of
`Δ`:

  `|fullTrainingKernel σ σ' b θ xs r s
      - fullTrainingKernel σ σ' b θ₀ xs r s|`
    `≤ C · Δ`,

where the Lipschitz constant
`C := 2·M·Lσ·X + 2·Aa·M'²·G + 2·Aa²·M'·Lσ'·X·G`
depends only on the data envelopes `(M, M', Lσ, Lσ', G, X, Aa)` and
*not* on the particular parameters `(θ, θ₀)`.

**Proof sketch.** Split the difference into σ- and σ'-blocks.

* **σ-block.** Each per-neuron summand factors via the identity
  `σ(u)σ(v) - σ(u₀)σ(v₀) = (σ(u) - σ(u₀))·σ(v) + σ(u₀)·(σ(v) - σ(v₀))`.
  Using `LipschitzWith Lσ σ` and `|σ| ≤ M`, the magnitude is bounded
  by `Lσ·|⟨w-w₀, x_r⟩|·M + M·Lσ·|⟨w-w₀, x_s⟩|`. Cauchy–Schwarz
  (`|⟨w-w₀, x⟩| ≤ ‖w-w₀‖·X ≤ X·Δ`) then yields the bound
  `2·M·Lσ·X·Δ` per summand; averaging over `m` neurons preserves it.

* **σ'-block.** Each per-neuron summand factors as
  `a²·σ'·σ'·⟨x,x⟩ - a₀²·σ'·σ'·⟨x,x⟩
     = (a² - a₀²)·σ'·σ'·⟨x,x⟩
       + a₀²·(σ' - σ'₀)·σ'·⟨x,x⟩
       + a₀²·σ'₀·(σ' - σ'₀)·⟨x,x⟩`.
  Using `|a² - a₀²| = |a - a₀|·|a + a₀| ≤ 2·Aa·|a - a₀| ≤ 2·Aa·Δ`
  (since `|a|, |a₀| ≤ Aa`), and the σ' Lipschitz/Cauchy–Schwarz combo
  on the σ' differences, the magnitude is bounded by
  `2·Aa·Δ·M'²·G + Aa²·Lσ'·X·Δ·M'·G + Aa²·M'·Lσ'·X·Δ·G
     = (2·Aa·M'²·G + 2·Aa²·M'·Lσ'·X·G)·Δ`.

Adding the two block bounds and noting that the `(1/m)` factor cancels
the `m` summands gives the claim. -/
theorem fullTrainingKernel_apply_lipschitz
    {n m : ℕ}
    (σ σ' : ℝ → ℝ)
    {Lσ Lσ' : NNReal}
    (hσ_lip : LipschitzWith Lσ σ)
    (hσ'_lip : LipschitzWith Lσ' σ')
    {M M' G X Aa : ℝ}
    (hM : 0 ≤ M) (hM' : 0 ≤ M')
    (hG_nn : 0 ≤ G) (hX_nn : 0 ≤ X) (hAa : 0 ≤ Aa)
    (hσ_bdd : ∀ z, |σ z| ≤ M)
    (hσ'_bdd : ∀ z, |σ' z| ≤ M')
    (b : Fin m → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (hG : ∀ a b, |inner ℝ (xs a) (xs b)| ≤ G)
    (hX : ∀ a, ‖xs a‖ ≤ X)
    {θ θ₀ : Param d m}
    (ha_bound : ∀ j, |θ.1 j| ≤ Aa) (ha₀_bound : ∀ j, |θ₀.1 j| ≤ Aa)
    (Δ : ℝ) (hΔ_nn : 0 ≤ Δ)
    (hΔ : ∀ j, dist (θ.1 j, θ.2 j) (θ₀.1 j, θ₀.2 j) ≤ Δ)
    (r s : Fin n) :
    |fullTrainingKernel σ σ' b θ xs r s -
     fullTrainingKernel σ σ' b θ₀ xs r s| ≤
      (2 * M * (Lσ : ℝ) * X + 2 * Aa * M' ^ 2 * G
        + 2 * Aa ^ 2 * M' * (Lσ' : ℝ) * X * G) * Δ := by
  classical
  -- 0 ≤ Δ (from the hypothesis applied to any j; m may be 0 though).
  -- We don't actually need 0 ≤ Δ to prove the bound; both sides are
  -- consistent.  Just bookkeeping.
  set Lσℝ : ℝ := (Lσ : ℝ) with hLσℝ_def
  set Lσ'ℝ : ℝ := (Lσ' : ℝ) with hLσ'ℝ_def
  have hLσ_nn : 0 ≤ Lσℝ := NNReal.coe_nonneg Lσ
  have hLσ'_nn : 0 ≤ Lσ'ℝ := NNReal.coe_nonneg Lσ'
  -- Per-neuron deviations: extract `|Δa| ≤ Δ` and `‖Δw‖ ≤ Δ` from the
  -- product-metric hypothesis.
  have h_da : ∀ j, |θ.1 j - θ₀.1 j| ≤ Δ := by
    intro j
    have hj := hΔ j
    have hmax : max (dist (θ.1 j) (θ₀.1 j)) (dist (θ.2 j) (θ₀.2 j)) ≤ Δ := by
      simpa [Prod.dist_eq] using hj
    have := le_trans (le_max_left _ _) hmax
    simpa [Real.dist_eq] using this
  have h_dw : ∀ j, ‖θ.2 j - θ₀.2 j‖ ≤ Δ := by
    intro j
    have hj := hΔ j
    have hmax : max (dist (θ.1 j) (θ₀.1 j)) (dist (θ.2 j) (θ₀.2 j)) ≤ Δ := by
      simpa [Prod.dist_eq] using hj
    have := le_trans (le_max_right _ _) hmax
    simpa [dist_eq_norm] using this
  -- Δ ≥ 0 when m ≥ 1; need separate handling otherwise.
  -- For the σ-block, define per-neuron expressions.
  -- LHS = (1/m)·(Aσ - Aσ₀) + (1/m)·(Aσ' - Aσ'₀) where
  --   Aσ_θ := Σ_j σ(⟨w_j,x_r⟩+b) σ(⟨w_j,x_s⟩+b)
  --   Aσ'_θ := Σ_j a_j² σ'(⟨w_j,x_r⟩+b) σ'(⟨w_j,x_s⟩+b) ⟨x_r,x_s⟩
  -- Bound each block.
  -- σ-block per-neuron drift.
  set Cσ : ℝ := 2 * M * Lσℝ * X with hCσ_def
  set Cσ'₁ : ℝ := 2 * Aa * M' ^ 2 * G with hCσ'₁_def
  set Cσ'₂ : ℝ := 2 * Aa ^ 2 * M' * Lσ'ℝ * X * G with hCσ'₂_def
  set Ctot : ℝ := Cσ + Cσ'₁ + Cσ'₂ with hCtot_def
  -- Bounds: each summand of the σ-block contributes `Cσ · Δ` to the drift.
  have h_sigma_drift : ∀ j : Fin m,
      |σ (inner ℝ (θ.2 j) (xs r) + b j) *
          σ (inner ℝ (θ.2 j) (xs s) + b j)
        - σ (inner ℝ (θ₀.2 j) (xs r) + b j) *
            σ (inner ℝ (θ₀.2 j) (xs s) + b j)|
      ≤ Cσ * Δ := by
    intro j
    set u : ℝ := inner ℝ (θ.2 j) (xs r) + b j
    set u₀ : ℝ := inner ℝ (θ₀.2 j) (xs r) + b j
    set v : ℝ := inner ℝ (θ.2 j) (xs s) + b j
    set v₀ : ℝ := inner ℝ (θ₀.2 j) (xs s) + b j
    -- σ(u) σ(v) - σ(u₀) σ(v₀) = (σ(u) - σ(u₀))·σ(v) + σ(u₀)·(σ(v) - σ(v₀)).
    have hsplit :
        σ u * σ v - σ u₀ * σ v₀
          = (σ u - σ u₀) * σ v + σ u₀ * (σ v - σ v₀) := by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    -- Bound `|(σ u - σ u₀) · σ v| ≤ Lσ · |u - u₀| · M`.
    have h_du : |σ u - σ u₀| ≤ Lσℝ * |u - u₀| := by
      have := hσ_lip.dist_le_mul u u₀
      simpa [Real.dist_eq] using this
    have h_dv : |σ v - σ v₀| ≤ Lσℝ * |v - v₀| := by
      have := hσ_lip.dist_le_mul v v₀
      simpa [Real.dist_eq] using this
    -- |u - u₀| = |⟨θ.2 j - θ₀.2 j, xs r⟩| ≤ ‖θ.2 j - θ₀.2 j‖ · X ≤ X · Δ.
    have h_u_diff_eq :
        u - u₀ = inner ℝ (θ.2 j - θ₀.2 j) (xs r) := by
      simp [u, u₀, inner_sub_left]
    have h_v_diff_eq :
        v - v₀ = inner ℝ (θ.2 j - θ₀.2 j) (xs s) := by
      simp [v, v₀, inner_sub_left]
    have h_u_abs : |u - u₀| ≤ X * Δ := by
      rw [h_u_diff_eq]
      have h1 : |inner ℝ (θ.2 j - θ₀.2 j) (xs r)|
                  ≤ ‖θ.2 j - θ₀.2 j‖ * ‖xs r‖ :=
        abs_real_inner_le_norm _ _
      have h2 : ‖θ.2 j - θ₀.2 j‖ * ‖xs r‖ ≤ Δ * X := by
        have hxr_nn : 0 ≤ ‖xs r‖ := norm_nonneg _
        have hnorm_nn : 0 ≤ ‖θ.2 j - θ₀.2 j‖ := norm_nonneg _
        exact mul_le_mul (h_dw j) (hX r) hxr_nn
          (le_trans hnorm_nn (h_dw j))
      have h3 : Δ * X = X * Δ := by ring
      linarith
    have h_v_abs : |v - v₀| ≤ X * Δ := by
      rw [h_v_diff_eq]
      have h1 : |inner ℝ (θ.2 j - θ₀.2 j) (xs s)|
                  ≤ ‖θ.2 j - θ₀.2 j‖ * ‖xs s‖ :=
        abs_real_inner_le_norm _ _
      have h2 : ‖θ.2 j - θ₀.2 j‖ * ‖xs s‖ ≤ Δ * X := by
        have hxs_nn : 0 ≤ ‖xs s‖ := norm_nonneg _
        have hnorm_nn : 0 ≤ ‖θ.2 j - θ₀.2 j‖ := norm_nonneg _
        exact mul_le_mul (h_dw j) (hX s) hxs_nn
          (le_trans hnorm_nn (h_dw j))
      have h3 : Δ * X = X * Δ := by ring
      linarith
    -- |(σ u - σ u₀) σ v| ≤ (Lσ · X · Δ) · M.
    have h_t1 : |(σ u - σ u₀) * σ v| ≤ Lσℝ * (X * Δ) * M := by
      rw [abs_mul]
      have hA : |σ u - σ u₀| ≤ Lσℝ * (X * Δ) := by
        have h_a1 := h_du
        have h_a2 :=
          mul_le_mul_of_nonneg_left h_u_abs hLσ_nn
        linarith
      have hB : |σ v| ≤ M := hσ_bdd v
      have hA_nn : 0 ≤ Lσℝ * (X * Δ) :=
        le_trans (abs_nonneg _) hA
      exact mul_le_mul hA hB (abs_nonneg _) hA_nn
    -- |σ u₀ · (σ v - σ v₀)| ≤ M · (Lσ · X · Δ).
    have h_t2 : |σ u₀ * (σ v - σ v₀)| ≤ M * (Lσℝ * (X * Δ)) := by
      rw [abs_mul]
      have hA : |σ u₀| ≤ M := hσ_bdd u₀
      have hB : |σ v - σ v₀| ≤ Lσℝ * (X * Δ) := by
        have h_b1 := h_dv
        have h_b2 :=
          mul_le_mul_of_nonneg_left h_v_abs hLσ_nn
        linarith
      exact mul_le_mul hA hB (abs_nonneg _) hM
    -- Combine: t1 + t2 ≤ 2 M Lσ X Δ = Cσ · Δ.
    have hsum_le : |(σ u - σ u₀) * σ v| + |σ u₀ * (σ v - σ v₀)|
                    ≤ Cσ * Δ := by
      have : Lσℝ * (X * Δ) * M + M * (Lσℝ * (X * Δ))
              = 2 * M * Lσℝ * X * Δ := by ring
      rw [hCσ_def]
      have hgoal :
          Lσℝ * (X * Δ) * M + M * (Lσℝ * (X * Δ))
            = 2 * M * Lσℝ * X * Δ := by ring
      linarith [h_t1, h_t2]
    exact hsum_le
  -- σ'-block per-neuron drift.
  have h_grad_drift : ∀ j : Fin m,
      |θ.1 j ^ 2 *
          σ' (inner ℝ (θ.2 j) (xs r) + b j) *
          σ' (inner ℝ (θ.2 j) (xs s) + b j) *
          inner ℝ (xs r) (xs s)
        - θ₀.1 j ^ 2 *
            σ' (inner ℝ (θ₀.2 j) (xs r) + b j) *
            σ' (inner ℝ (θ₀.2 j) (xs s) + b j) *
            inner ℝ (xs r) (xs s)|
      ≤ (Cσ'₁ + Cσ'₂) * Δ := by
    intro j
    set Pa : ℝ := θ.1 j with hPa_def
    set Pa₀ : ℝ := θ₀.1 j with hPa₀_def
    set u : ℝ := inner ℝ (θ.2 j) (xs r) + b j
    set u₀ : ℝ := inner ℝ (θ₀.2 j) (xs r) + b j
    set v : ℝ := inner ℝ (θ.2 j) (xs s) + b j
    set v₀ : ℝ := inner ℝ (θ₀.2 j) (xs s) + b j
    set ip : ℝ := inner ℝ (xs r) (xs s) with hip_def
    -- Three-term telescoping.
    have hsplit :
        Pa ^ 2 * σ' u * σ' v * ip - Pa₀ ^ 2 * σ' u₀ * σ' v₀ * ip
          = (Pa ^ 2 - Pa₀ ^ 2) * σ' u * σ' v * ip
            + Pa₀ ^ 2 * (σ' u - σ' u₀) * σ' v * ip
            + Pa₀ ^ 2 * σ' u₀ * (σ' v - σ' v₀) * ip := by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    have h_abs_split :
        |(Pa ^ 2 - Pa₀ ^ 2) * σ' u * σ' v * ip
          + Pa₀ ^ 2 * (σ' u - σ' u₀) * σ' v * ip|
          + |Pa₀ ^ 2 * σ' u₀ * (σ' v - σ' v₀) * ip|
        ≤ |(Pa ^ 2 - Pa₀ ^ 2) * σ' u * σ' v * ip|
          + |Pa₀ ^ 2 * (σ' u - σ' u₀) * σ' v * ip|
          + |Pa₀ ^ 2 * σ' u₀ * (σ' v - σ' v₀) * ip| := by
      have h_first := abs_add_le ((Pa ^ 2 - Pa₀ ^ 2) * σ' u * σ' v * ip)
        (Pa₀ ^ 2 * (σ' u - σ' u₀) * σ' v * ip)
      linarith
    refine le_trans h_abs_split ?_
    -- Bound |a² - a₀²| ≤ 2·Aa·Δ via |a² - a₀²| = |a - a₀|·|a + a₀|.
    have h_da_j : |Pa - Pa₀| ≤ Δ := h_da j
    have h_a_plus_a₀_abs : |Pa + Pa₀| ≤ 2 * Aa := by
      calc |Pa + Pa₀| ≤ |Pa| + |Pa₀| := abs_add_le _ _
        _ ≤ Aa + Aa := add_le_add (ha_bound j) (ha₀_bound j)
        _ = 2 * Aa := by ring
    have h_a_sq_diff_abs : |Pa ^ 2 - Pa₀ ^ 2| ≤ 2 * Aa * Δ := by
      have h_factor : Pa ^ 2 - Pa₀ ^ 2 = (Pa - Pa₀) * (Pa + Pa₀) := by ring
      rw [h_factor, abs_mul]
      have h_mul_le : |Pa - Pa₀| * |Pa + Pa₀| ≤ Δ * (2 * Aa) := by
        have hp_nn : 0 ≤ |Pa + Pa₀| := abs_nonneg _
        have hd_nn : 0 ≤ Δ :=
          le_trans (abs_nonneg _) h_da_j
        exact mul_le_mul h_da_j h_a_plus_a₀_abs hp_nn hd_nn
      have : Δ * (2 * Aa) = 2 * Aa * Δ := by ring
      linarith
    -- Term 1: (a² - a₀²) σ' u σ' v ip.
    have hM'_sq_G_nn : 0 ≤ M' ^ 2 * G := by positivity
    have h_t1 :
        |(Pa ^ 2 - Pa₀ ^ 2) * σ' u * σ' v * ip|
          ≤ (2 * Aa * Δ) * M' ^ 2 * G := by
      -- |x·σ'·σ'·ip| = |x| · |σ' u| · |σ' v| · |ip|.
      have h_eq : |(Pa ^ 2 - Pa₀ ^ 2) * σ' u * σ' v * ip|
        = |Pa ^ 2 - Pa₀ ^ 2| * |σ' u| * |σ' v| * |ip| := by
        rw [abs_mul, abs_mul, abs_mul]
      rw [h_eq]
      -- Bound |σ' u| ≤ M', |σ' v| ≤ M', |ip| ≤ G, |a² - a₀²| ≤ 2 Aa Δ.
      have hs_u : |σ' u| ≤ M' := hσ'_bdd u
      have hs_v : |σ' v| ≤ M' := hσ'_bdd v
      have hip_le : |ip| ≤ G := hG r s
      -- Stepwise multiplication.
      have hp1 : |Pa ^ 2 - Pa₀ ^ 2| * |σ' u| ≤ (2 * Aa * Δ) * M' := by
        have h1 : 0 ≤ |σ' u| := abs_nonneg _
        have h2 : 0 ≤ 2 * Aa * Δ := le_trans (abs_nonneg _) h_a_sq_diff_abs
        exact mul_le_mul h_a_sq_diff_abs hs_u h1 h2
      have hp1_nn : 0 ≤ (2 * Aa * Δ) * M' :=
        le_trans (mul_nonneg (abs_nonneg _) (abs_nonneg _)) hp1
      have hp2 : |Pa ^ 2 - Pa₀ ^ 2| * |σ' u| * |σ' v|
                  ≤ (2 * Aa * Δ) * M' * M' := by
        exact mul_le_mul hp1 hs_v (abs_nonneg _) hp1_nn
      have hp2_nn : 0 ≤ (2 * Aa * Δ) * M' * M' :=
        le_trans
          (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _))
          hp2
      have hp3 : |Pa ^ 2 - Pa₀ ^ 2| * |σ' u| * |σ' v| * |ip|
                  ≤ (2 * Aa * Δ) * M' * M' * G := by
        exact mul_le_mul hp2 hip_le (abs_nonneg _) hp2_nn
      have hpow : (2 * Aa * Δ) * M' * M' * G
                    = (2 * Aa * Δ) * M' ^ 2 * G := by ring
      linarith
    -- Term 2: a₀² (σ' u - σ' u₀) σ' v ip.
    have h_aj₀_sq_nn : 0 ≤ Pa₀ ^ 2 := sq_nonneg _
    have h_aj₀_sq_le : Pa₀ ^ 2 ≤ Aa ^ 2 := by
      have h_abs := ha₀_bound j
      have h_nn : 0 ≤ |Pa₀| := abs_nonneg _
      have h_sq_le : |Pa₀| ^ 2 ≤ Aa ^ 2 :=
        pow_le_pow_left₀ h_nn h_abs 2
      have h_eq : Pa₀ ^ 2 = |Pa₀| ^ 2 := by rw [sq_abs]
      rw [h_eq]; exact h_sq_le
    -- σ' u - σ' u₀ bounded by Lσ' · |u - u₀|, with |u - u₀| ≤ X · Δ.
    have h_du : |σ' u - σ' u₀| ≤ Lσ'ℝ * |u - u₀| := by
      have := hσ'_lip.dist_le_mul u u₀
      simpa [Real.dist_eq] using this
    have h_dv : |σ' v - σ' v₀| ≤ Lσ'ℝ * |v - v₀| := by
      have := hσ'_lip.dist_le_mul v v₀
      simpa [Real.dist_eq] using this
    have h_u_diff_eq :
        u - u₀ = inner ℝ (θ.2 j - θ₀.2 j) (xs r) := by
      simp [u, u₀, inner_sub_left]
    have h_v_diff_eq :
        v - v₀ = inner ℝ (θ.2 j - θ₀.2 j) (xs s) := by
      simp [v, v₀, inner_sub_left]
    have h_u_abs : |u - u₀| ≤ X * Δ := by
      rw [h_u_diff_eq]
      have h1 : |inner ℝ (θ.2 j - θ₀.2 j) (xs r)|
                  ≤ ‖θ.2 j - θ₀.2 j‖ * ‖xs r‖ :=
        abs_real_inner_le_norm _ _
      have hxr_nn : 0 ≤ ‖xs r‖ := norm_nonneg _
      have hnorm_nn : 0 ≤ ‖θ.2 j - θ₀.2 j‖ := norm_nonneg _
      have h2 : ‖θ.2 j - θ₀.2 j‖ * ‖xs r‖ ≤ Δ * X :=
        mul_le_mul (h_dw j) (hX r) hxr_nn
          (le_trans hnorm_nn (h_dw j))
      have h3 : Δ * X = X * Δ := by ring
      linarith
    have h_v_abs : |v - v₀| ≤ X * Δ := by
      rw [h_v_diff_eq]
      have h1 : |inner ℝ (θ.2 j - θ₀.2 j) (xs s)|
                  ≤ ‖θ.2 j - θ₀.2 j‖ * ‖xs s‖ :=
        abs_real_inner_le_norm _ _
      have hxs_nn : 0 ≤ ‖xs s‖ := norm_nonneg _
      have hnorm_nn : 0 ≤ ‖θ.2 j - θ₀.2 j‖ := norm_nonneg _
      have h2 : ‖θ.2 j - θ₀.2 j‖ * ‖xs s‖ ≤ Δ * X :=
        mul_le_mul (h_dw j) (hX s) hxs_nn
          (le_trans hnorm_nn (h_dw j))
      have h3 : Δ * X = X * Δ := by ring
      linarith
    have h_du_bound : |σ' u - σ' u₀| ≤ Lσ'ℝ * X * Δ := by
      have h_a1 := h_du
      have h_a2 :=
        mul_le_mul_of_nonneg_left h_u_abs hLσ'_nn
      have h_eq : Lσ'ℝ * (X * Δ) = Lσ'ℝ * X * Δ := by ring
      linarith
    have h_dv_bound : |σ' v - σ' v₀| ≤ Lσ'ℝ * X * Δ := by
      have h_a1 := h_dv
      have h_a2 :=
        mul_le_mul_of_nonneg_left h_v_abs hLσ'_nn
      have h_eq : Lσ'ℝ * (X * Δ) = Lσ'ℝ * X * Δ := by ring
      linarith
    have hAa_sq_nn : 0 ≤ Aa ^ 2 := sq_nonneg _
    have hLσ'_X_Δ_nn : 0 ≤ Lσ'ℝ * X * Δ := le_trans (abs_nonneg _) h_du_bound
    have h_t2 :
        |Pa₀ ^ 2 * (σ' u - σ' u₀) * σ' v * ip|
          ≤ Aa ^ 2 * (Lσ'ℝ * X * Δ) * M' * G := by
      have h_eq : |Pa₀ ^ 2 * (σ' u - σ' u₀) * σ' v * ip|
        = Pa₀ ^ 2 * |σ' u - σ' u₀| * |σ' v| * |ip| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg h_aj₀_sq_nn]
      rw [h_eq]
      -- Stepwise bound.
      have hp1 : Pa₀ ^ 2 * |σ' u - σ' u₀| ≤ Aa ^ 2 * (Lσ'ℝ * X * Δ) :=
        mul_le_mul h_aj₀_sq_le h_du_bound (abs_nonneg _) hAa_sq_nn
      have hp1_nn : 0 ≤ Aa ^ 2 * (Lσ'ℝ * X * Δ) :=
        le_trans (mul_nonneg h_aj₀_sq_nn (abs_nonneg _)) hp1
      have hs_v : |σ' v| ≤ M' := hσ'_bdd v
      have hp2 : Pa₀ ^ 2 * |σ' u - σ' u₀| * |σ' v|
                  ≤ Aa ^ 2 * (Lσ'ℝ * X * Δ) * M' :=
        mul_le_mul hp1 hs_v (abs_nonneg _) hp1_nn
      have hp2_nn : 0 ≤ Aa ^ 2 * (Lσ'ℝ * X * Δ) * M' :=
        le_trans
          (mul_nonneg (mul_nonneg h_aj₀_sq_nn (abs_nonneg _)) (abs_nonneg _))
          hp2
      have hip_le : |ip| ≤ G := hG r s
      have hp3 : Pa₀ ^ 2 * |σ' u - σ' u₀| * |σ' v| * |ip|
                  ≤ Aa ^ 2 * (Lσ'ℝ * X * Δ) * M' * G :=
        mul_le_mul hp2 hip_le (abs_nonneg _) hp2_nn
      exact hp3
    -- Term 3: a₀² σ' u₀ (σ' v - σ' v₀) ip.
    have h_t3 :
        |Pa₀ ^ 2 * σ' u₀ * (σ' v - σ' v₀) * ip|
          ≤ Aa ^ 2 * M' * (Lσ'ℝ * X * Δ) * G := by
      have h_eq : |Pa₀ ^ 2 * σ' u₀ * (σ' v - σ' v₀) * ip|
        = Pa₀ ^ 2 * |σ' u₀| * |σ' v - σ' v₀| * |ip| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg h_aj₀_sq_nn]
      rw [h_eq]
      have hs_u₀ : |σ' u₀| ≤ M' := hσ'_bdd u₀
      have hp1 : Pa₀ ^ 2 * |σ' u₀| ≤ Aa ^ 2 * M' :=
        mul_le_mul h_aj₀_sq_le hs_u₀ (abs_nonneg _) hAa_sq_nn
      have hp1_nn : 0 ≤ Aa ^ 2 * M' :=
        le_trans (mul_nonneg h_aj₀_sq_nn (abs_nonneg _)) hp1
      have hp2 : Pa₀ ^ 2 * |σ' u₀| * |σ' v - σ' v₀|
                  ≤ Aa ^ 2 * M' * (Lσ'ℝ * X * Δ) :=
        mul_le_mul hp1 h_dv_bound (abs_nonneg _) hp1_nn
      have hp2_nn : 0 ≤ Aa ^ 2 * M' * (Lσ'ℝ * X * Δ) :=
        le_trans
          (mul_nonneg (mul_nonneg h_aj₀_sq_nn (abs_nonneg _)) (abs_nonneg _))
          hp2
      have hip_le : |ip| ≤ G := hG r s
      exact mul_le_mul hp2 hip_le (abs_nonneg _) hp2_nn
    -- Combine: t1 + t2 + t3 ≤ Cσ'₁·Δ + (Cσ'₂/2)·Δ + (Cσ'₂/2)·Δ.
    -- Actually: Cσ'₁ := 2·Aa·M'²·G,  Cσ'₂ := 2·Aa²·M'·Lσ'·X·G,
    -- so RHS = (2·Aa·Δ)·M'²·G + Aa²·(Lσ'·X·Δ)·M'·G + Aa²·M'·(Lσ'·X·Δ)·G
    --       = Cσ'₁·Δ + Cσ'₂·Δ  (the two σ'-Lipschitz terms split Cσ'₂ in half).
    have h_simplify :
        (2 * Aa * Δ) * M' ^ 2 * G
          + Aa ^ 2 * (Lσ'ℝ * X * Δ) * M' * G
          + Aa ^ 2 * M' * (Lσ'ℝ * X * Δ) * G
          = (Cσ'₁ + Cσ'₂) * Δ := by
      rw [hCσ'₁_def, hCσ'₂_def]; ring
    linarith [h_t1, h_t2, h_t3, h_simplify]
  -- Now assemble: |K_θ - K_θ₀| ≤ Cσ Δ + (Cσ'₁ + Cσ'₂) Δ = Ctot Δ.
  -- The LHS expands as
  -- (1/m)·(Σ σσ - Σ σ₀σ₀) + (1/m)·(Σ a²σ'σ'ip - Σ a₀²σ'₀σ'₀ip).
  -- We bound each via Finset.abs_sum_le_sum_abs and the per-summand
  -- drift estimates.
  set Sσ_diff : ℝ :=
      ∑ j, (σ (inner ℝ (θ.2 j) (xs r) + b j) *
                σ (inner ℝ (θ.2 j) (xs s) + b j)
            - σ (inner ℝ (θ₀.2 j) (xs r) + b j) *
                σ (inner ℝ (θ₀.2 j) (xs s) + b j)) with hSσ_diff_def
  set Sσ'_diff : ℝ :=
      ∑ j, (θ.1 j ^ 2 *
                σ' (inner ℝ (θ.2 j) (xs r) + b j) *
                σ' (inner ℝ (θ.2 j) (xs s) + b j) *
                inner ℝ (xs r) (xs s)
            - θ₀.1 j ^ 2 *
                σ' (inner ℝ (θ₀.2 j) (xs r) + b j) *
                σ' (inner ℝ (θ₀.2 j) (xs s) + b j) *
                inner ℝ (xs r) (xs s)) with hSσ'_diff_def
  -- |Sσ_diff| ≤ m · Cσ · Δ.
  have h_Sσ_abs : |Sσ_diff| ≤ (m : ℝ) * (Cσ * Δ) := by
    have hsum_abs :
        |Sσ_diff|
          ≤ ∑ j : Fin m,
              |σ (inner ℝ (θ.2 j) (xs r) + b j) *
                  σ (inner ℝ (θ.2 j) (xs s) + b j)
                - σ (inner ℝ (θ₀.2 j) (xs r) + b j) *
                    σ (inner ℝ (θ₀.2 j) (xs s) + b j)| := by
      rw [hSσ_diff_def]
      exact Finset.abs_sum_le_sum_abs _ _
    have hsum_bound :
        ∑ j : Fin m,
            |σ (inner ℝ (θ.2 j) (xs r) + b j) *
                σ (inner ℝ (θ.2 j) (xs s) + b j)
              - σ (inner ℝ (θ₀.2 j) (xs r) + b j) *
                  σ (inner ℝ (θ₀.2 j) (xs s) + b j)|
          ≤ ∑ _j : Fin m, Cσ * Δ :=
        Finset.sum_le_sum (fun j _ => h_sigma_drift j)
    have hsum_const : ∑ _j : Fin m, Cσ * Δ = (m : ℝ) * (Cσ * Δ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  -- |Sσ'_diff| ≤ m · (Cσ'₁ + Cσ'₂) · Δ.
  have h_Sσ'_abs :
      |Sσ'_diff| ≤ (m : ℝ) * ((Cσ'₁ + Cσ'₂) * Δ) := by
    have hsum_abs :
        |Sσ'_diff|
          ≤ ∑ j : Fin m,
              |θ.1 j ^ 2 *
                  σ' (inner ℝ (θ.2 j) (xs r) + b j) *
                  σ' (inner ℝ (θ.2 j) (xs s) + b j) *
                  inner ℝ (xs r) (xs s)
                - θ₀.1 j ^ 2 *
                    σ' (inner ℝ (θ₀.2 j) (xs r) + b j) *
                    σ' (inner ℝ (θ₀.2 j) (xs s) + b j) *
                    inner ℝ (xs r) (xs s)| := by
      rw [hSσ'_diff_def]
      exact Finset.abs_sum_le_sum_abs _ _
    have hsum_bound :
        ∑ j : Fin m,
            |θ.1 j ^ 2 *
                σ' (inner ℝ (θ.2 j) (xs r) + b j) *
                σ' (inner ℝ (θ.2 j) (xs s) + b j) *
                inner ℝ (xs r) (xs s)
              - θ₀.1 j ^ 2 *
                  σ' (inner ℝ (θ₀.2 j) (xs r) + b j) *
                  σ' (inner ℝ (θ₀.2 j) (xs s) + b j) *
                  inner ℝ (xs r) (xs s)|
          ≤ ∑ _j : Fin m, (Cσ'₁ + Cσ'₂) * Δ :=
        Finset.sum_le_sum (fun j _ => h_grad_drift j)
    have hsum_const :
        ∑ _j : Fin m, (Cσ'₁ + Cσ'₂) * Δ
          = (m : ℝ) * ((Cσ'₁ + Cσ'₂) * Δ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  -- Now rewrite the LHS as (1/m)·Sσ_diff + (1/m)·Sσ'_diff.
  have hLHS_eq :
      fullTrainingKernel σ σ' b θ xs r s
        - fullTrainingKernel σ σ' b θ₀ xs r s
        = (1 / (m : ℝ)) * Sσ_diff + (1 / (m : ℝ)) * Sσ'_diff := by
    -- Both sides distribute over the sums identically.
    rw [hSσ_diff_def, hSσ'_diff_def]
    -- LHS = K_θ - K_θ₀ where each K_θ is a sum of two (1/m)·Σ blocks.
    show (1 / (m : ℝ)) *
        ∑ j, σ (inner ℝ (θ.2 j) (xs r) + b j) *
                σ (inner ℝ (θ.2 j) (xs s) + b j)
      + (1 / (m : ℝ)) *
          ∑ j, θ.1 j ^ 2 *
                  σ' (inner ℝ (θ.2 j) (xs r) + b j) *
                  σ' (inner ℝ (θ.2 j) (xs s) + b j) *
                  inner ℝ (xs r) (xs s)
      - ((1 / (m : ℝ)) *
          ∑ j, σ (inner ℝ (θ₀.2 j) (xs r) + b j) *
                  σ (inner ℝ (θ₀.2 j) (xs s) + b j)
        + (1 / (m : ℝ)) *
          ∑ j, θ₀.1 j ^ 2 *
                  σ' (inner ℝ (θ₀.2 j) (xs r) + b j) *
                  σ' (inner ℝ (θ₀.2 j) (xs s) + b j) *
                  inner ℝ (xs r) (xs s))
        = (1 / (m : ℝ)) *
            ∑ j, (σ (inner ℝ (θ.2 j) (xs r) + b j) *
                      σ (inner ℝ (θ.2 j) (xs s) + b j)
                - σ (inner ℝ (θ₀.2 j) (xs r) + b j) *
                      σ (inner ℝ (θ₀.2 j) (xs s) + b j))
          + (1 / (m : ℝ)) *
              ∑ j, (θ.1 j ^ 2 *
                      σ' (inner ℝ (θ.2 j) (xs r) + b j) *
                      σ' (inner ℝ (θ.2 j) (xs s) + b j) *
                      inner ℝ (xs r) (xs s)
                    - θ₀.1 j ^ 2 *
                      σ' (inner ℝ (θ₀.2 j) (xs r) + b j) *
                      σ' (inner ℝ (θ₀.2 j) (xs s) + b j) *
                      inner ℝ (xs r) (xs s))
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    ring
  -- Combine the two block bounds.
  -- Cases on m.
  rcases Nat.eq_zero_or_pos m with hm0 | hm_pos
  · -- m = 0: LHS = 0; need 0 ≤ Ctot · Δ, which holds since Ctot ≥ 0
    -- and we have hΔ_nn : 0 ≤ Δ.
    subst hm0
    have hSσ_zero : Sσ_diff = 0 := by simp [hSσ_diff_def]
    have hSσ'_zero : Sσ'_diff = 0 := by simp [hSσ'_diff_def]
    have hLHS_zero :
        fullTrainingKernel σ σ' b θ xs r s
          - fullTrainingKernel σ σ' b θ₀ xs r s = 0 := by
      rw [hLHS_eq, hSσ_zero, hSσ'_zero]; ring
    rw [hLHS_zero, abs_zero]
    have hCσ_nn : 0 ≤ Cσ := by rw [hCσ_def]; positivity
    have hCσ'₁_nn : 0 ≤ Cσ'₁ := by rw [hCσ'₁_def]; positivity
    have hCσ'₂_nn : 0 ≤ Cσ'₂ := by rw [hCσ'₂_def]; positivity
    have hC_full_nn :
        0 ≤ 2 * M * Lσℝ * X + 2 * Aa * M' ^ 2 * G
            + 2 * Aa ^ 2 * M' * Lσ'ℝ * X * G := by
      have heq : 2 * M * Lσℝ * X + 2 * Aa * M' ^ 2 * G
            + 2 * Aa ^ 2 * M' * Lσ'ℝ * X * G = Cσ + Cσ'₁ + Cσ'₂ := by
        rw [hCσ_def, hCσ'₁_def, hCσ'₂_def]
      rw [heq]; linarith
    exact mul_nonneg hC_full_nn hΔ_nn
  · -- m > 0 branch.
    have hm_pos_real : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
    have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos_real
    have h_inv_nn : 0 ≤ 1 / (m : ℝ) := by positivity
    -- Δ ≥ 0 by hypothesis.
    -- Bound |(1/m)·Sσ_diff| ≤ Cσ·Δ.
    have h_block1 : |(1 / (m : ℝ)) * Sσ_diff| ≤ Cσ * Δ := by
      rw [abs_mul, abs_of_nonneg h_inv_nn]
      have h_bound :
          (1 / (m : ℝ)) * |Sσ_diff|
            ≤ (1 / (m : ℝ)) * ((m : ℝ) * (Cσ * Δ)) :=
        mul_le_mul_of_nonneg_left h_Sσ_abs h_inv_nn
      have h_simplify :
          (1 / (m : ℝ)) * ((m : ℝ) * (Cσ * Δ)) = Cσ * Δ := by
        field_simp
      linarith
    -- Bound |(1/m)·Sσ'_diff| ≤ (Cσ'₁ + Cσ'₂)·Δ.
    have h_block2 :
        |(1 / (m : ℝ)) * Sσ'_diff| ≤ (Cσ'₁ + Cσ'₂) * Δ := by
      rw [abs_mul, abs_of_nonneg h_inv_nn]
      have h_bound :
          (1 / (m : ℝ)) * |Sσ'_diff|
            ≤ (1 / (m : ℝ)) * ((m : ℝ) * ((Cσ'₁ + Cσ'₂) * Δ)) :=
        mul_le_mul_of_nonneg_left h_Sσ'_abs h_inv_nn
      have h_simplify :
          (1 / (m : ℝ)) * ((m : ℝ) * ((Cσ'₁ + Cσ'₂) * Δ))
            = (Cσ'₁ + Cσ'₂) * Δ := by
        field_simp
      linarith
    -- Combine via triangle inequality on (1/m)·Sσ_diff + (1/m)·Sσ'_diff.
    have h_tri :
        |(1 / (m : ℝ)) * Sσ_diff + (1 / (m : ℝ)) * Sσ'_diff|
          ≤ |(1 / (m : ℝ)) * Sσ_diff| + |(1 / (m : ℝ)) * Sσ'_diff| :=
      abs_add_le _ _
    have h_total :
        |(1 / (m : ℝ)) * Sσ_diff + (1 / (m : ℝ)) * Sσ'_diff|
          ≤ (Cσ + Cσ'₁ + Cσ'₂) * Δ := by
      have h_arith : Cσ * Δ + (Cσ'₁ + Cσ'₂) * Δ
                      = (Cσ + Cσ'₁ + Cσ'₂) * Δ := by ring
      linarith
    rw [hLHS_eq]
    have h_C_unfold : Cσ + Cσ'₁ + Cσ'₂
        = 2 * M * Lσℝ * X + 2 * Aa * M' ^ 2 * G
          + 2 * Aa ^ 2 * M' * Lσ'ℝ * X * G := by
      rw [hCσ_def, hCσ'₁_def, hCσ'₂_def]
    linarith [h_total]

end ProbabilityTheory
