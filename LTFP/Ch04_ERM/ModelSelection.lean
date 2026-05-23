/-
LTFP §4.6 — Model selection (♦).

Bach (2024) §4.6, pp. 103-105. Given a sequence of hypothesis classes
`H₁ ⊆ H₂ ⊆ …`, structural risk minimization (SRM) selects the class
that minimizes empirical risk plus a complexity penalty `pen(Hₖ)`.
Validation-set selection picks the class minimizing held-out risk.

For Phase 3b we land just the SRM penalty operator's monotonicity:
adding a larger penalty produces a larger penalized risk. The full
oracle inequality (♦) is left for a follow-up wave.
-/
import LTFP.Ch02_SupervisedLearning.ERM

namespace LTFP

variable {𝒳 𝒴 𝒵 : Type*}

/-- §4.6 — Penalized empirical risk: empirical risk plus a non-negative
    complexity penalty `pen` for the hypothesis class. -/
noncomputable def penalizedEmpiricalRisk
    (ℓ : LossFunction 𝒴 𝒵) (n : ℕ) (S : Fin n → 𝒳 × 𝒴)
    (f : 𝒳 → 𝒵) (pen : ℝ) : ℝ :=
  empiricalRisk ℓ n S f + pen

/-- §4.6 — Monotonicity in the penalty: larger penalties yield larger
    penalized risks. -/
theorem penalizedEmpiricalRisk_mono
    (ℓ : LossFunction 𝒴 𝒵) (n : ℕ) (S : Fin n → 𝒳 × 𝒴)
    (f : 𝒳 → 𝒵) {p1 p2 : ℝ} (h : p1 ≤ p2) :
    penalizedEmpiricalRisk ℓ n S f p1 ≤ penalizedEmpiricalRisk ℓ n S f p2 := by
  unfold penalizedEmpiricalRisk
  linarith

/-- §4.6 — Penalized risk with zero penalty equals empirical risk. -/
theorem penalizedEmpiricalRisk_zero_pen
    (ℓ : LossFunction 𝒴 𝒵) (n : ℕ) (S : Fin n → 𝒳 × 𝒴) (f : 𝒳 → 𝒵) :
    penalizedEmpiricalRisk ℓ n S f 0 = empiricalRisk ℓ n S f := by
  unfold penalizedEmpiricalRisk
  ring

/-- §4.6 — Penalized risk is additive in the penalty. -/
theorem penalizedEmpiricalRisk_add_pen
    (ℓ : LossFunction 𝒴 𝒵) (n : ℕ) (S : Fin n → 𝒳 × 𝒴) (f : 𝒳 → 𝒵)
    (p₁ p₂ : ℝ) :
    penalizedEmpiricalRisk ℓ n S f (p₁ + p₂) =
      penalizedEmpiricalRisk ℓ n S f p₁ + p₂ := by
  unfold penalizedEmpiricalRisk
  ring

/-- §4.6 — **Penalty floors the empirical risk.** Any non-negative
    penalty `pen ≥ 0` enlarges the empirical risk into the SRM
    objective. This is the algebraic content of "the penalty
    discourages large classes" (Bach §4.6, p. 103) and is the
    inequality used to lower-bound the SRM selector. -/
theorem empiricalRisk_le_penalizedEmpiricalRisk
    (ℓ : LossFunction 𝒴 𝒵) (n : ℕ) (S : Fin n → 𝒳 × 𝒴)
    (f : 𝒳 → 𝒵) {pen : ℝ} (hpen : 0 ≤ pen) :
    empiricalRisk ℓ n S f ≤ penalizedEmpiricalRisk ℓ n S f pen := by
  unfold penalizedEmpiricalRisk
  linarith

/-! ### Finite SRM / oracle algebraic core (Bach §4.6, p. 103-105)

Given a finite indexed family `f : ι → (𝒳 → 𝒵)` of candidate predictors
(one per hypothesis class in `H₁ ⊆ H₂ ⊆ …`, e.g. each `f i` is an ERM
on `H i`) with complexity penalty `pen : ι → ℝ`, the structural risk
minimizer selects the index that minimizes `R̂(f i) + pen i`.

The deterministic algebraic content of the oracle inequality is:
**the selected predictor's empirical risk is bounded above by the
oracle's empirical risk plus the penalty gap `pen oracle - pen selected`.**
Bach states the high-probability oracle inequality on top of this
deterministic algebra; here we land the deterministic core. -/

/-- §4.6 — **SRM oracle algebraic core.** If `selected` minimizes the
    penalized empirical risk over a finite family `f : ι → (𝒳 → 𝒵)`
    with penalty `pen : ι → ℝ`, then for *any* `oracle` index, the
    empirical risk of the selected predictor is at most the oracle's
    empirical risk plus the penalty gap `pen oracle - pen selected`.

    This is the deterministic algebraic content of Bach §4.6's oracle
    inequality (p. 104-105): the statistical part adds uniform
    concentration on top of this algebra. -/
theorem srm_selected_empiricalRisk_le_oracle_add_penalty_gap
    {ι : Type*} (ℓ : LossFunction 𝒴 𝒵) (n : ℕ) (S : Fin n → 𝒳 × 𝒴)
    (f : ι → (𝒳 → 𝒵)) (pen : ι → ℝ) (selected oracle : ι)
    (hsel : ∀ i, penalizedEmpiricalRisk ℓ n S (f selected) (pen selected) ≤
      penalizedEmpiricalRisk ℓ n S (f i) (pen i)) :
    empiricalRisk ℓ n S (f selected) ≤
      empiricalRisk ℓ n S (f oracle) + pen oracle - pen selected := by
  have h := hsel oracle
  unfold penalizedEmpiricalRisk at h
  linarith

/-- §4.6 — **SRM oracle inequality, nonneg-penalty corollary.** When
    every penalty `pen i` is non-negative (the standard case: penalty
    measures complexity ≥ 0), the SRM selector's empirical risk is at
    most the oracle's empirical risk plus the oracle's penalty alone
    (no minus term). This is the form Bach typically states. -/
theorem srm_selected_empiricalRisk_le_oracle_add_oracle_penalty
    {ι : Type*} (ℓ : LossFunction 𝒴 𝒵) (n : ℕ) (S : Fin n → 𝒳 × 𝒴)
    (f : ι → (𝒳 → 𝒵)) (pen : ι → ℝ) (selected oracle : ι)
    (hsel : ∀ i, penalizedEmpiricalRisk ℓ n S (f selected) (pen selected) ≤
      penalizedEmpiricalRisk ℓ n S (f i) (pen i))
    (hpen : ∀ i, 0 ≤ pen i) :
    empiricalRisk ℓ n S (f selected) ≤
      empiricalRisk ℓ n S (f oracle) + pen oracle := by
  have h := srm_selected_empiricalRisk_le_oracle_add_penalty_gap
    ℓ n S f pen selected oracle hsel
  have hs : 0 ≤ pen selected := hpen selected
  linarith

/-- §4.6 — **SRM selected achieves the minimum penalized risk.** The
    penalized empirical risk of the selected index is the minimum over
    the (finite, nonempty) family — the elementary `Finset.inf'`
    formulation of the SRM selection rule. -/
theorem srm_penalizedEmpiricalRisk_selected_eq_inf'
    {ι : Type*} [Fintype ι] [Nonempty ι]
    (ℓ : LossFunction 𝒴 𝒵) (n : ℕ) (S : Fin n → 𝒳 × 𝒴)
    (f : ι → (𝒳 → 𝒵)) (pen : ι → ℝ) (selected : ι)
    (hsel : ∀ i, penalizedEmpiricalRisk ℓ n S (f selected) (pen selected) ≤
      penalizedEmpiricalRisk ℓ n S (f i) (pen i)) :
    penalizedEmpiricalRisk ℓ n S (f selected) (pen selected) =
      (Finset.univ : Finset ι).inf' Finset.univ_nonempty
        (fun i => penalizedEmpiricalRisk ℓ n S (f i) (pen i)) := by
  apply le_antisymm
  · exact Finset.le_inf' _ _ (fun i _ => hsel i)
  · exact Finset.inf'_le _ (Finset.mem_univ selected)

end LTFP
