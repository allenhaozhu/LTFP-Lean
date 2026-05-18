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

end LTFP
