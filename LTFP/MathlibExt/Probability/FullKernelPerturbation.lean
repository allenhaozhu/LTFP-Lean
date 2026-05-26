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

end ProbabilityTheory
