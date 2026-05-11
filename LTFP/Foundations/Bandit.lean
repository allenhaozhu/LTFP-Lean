/-
LTFP foundation: multi-armed bandits.

Phase-3a anchor for Ch 11.3 (UCB, explore-then-commit, optimism,
adversarial bandits). A `K`-armed bandit instance is a vector of
reward distributions; an algorithm produces a sequence of arm pulls.
The cumulative regret over `T` rounds is `T · μ⋆ − ∑ₜ μ_{aₜ}`.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators

namespace LTFP

/-- §F8b — Cumulative regret over `T` rounds against the best arm.
    Given mean rewards `μ : Fin K → ℝ` and a sequence of arm pulls
    `actions : Fin T → Fin K`, the regret is
    `T · max μ − ∑ₜ μ(actions t)`. -/
def banditRegret {K T : ℕ}
    (μ : Fin K → ℝ) (actions : Fin T → Fin K) (mu_star : ℝ) : ℝ :=
  T * mu_star - ∑ t, μ (actions t)

/-- §F8b sanity lemma: regret on an empty trajectory (`T = 0`)
    is zero, regardless of the mean rewards. -/
theorem banditRegret_zero {K : ℕ}
    (μ : Fin K → ℝ) (mu_star : ℝ) :
    banditRegret (T := 0) μ Fin.elim0 mu_star = 0 := by
  unfold banditRegret
  simp

/-- §F8b — Regret depends linearly on the optimal mean `μ⋆`. -/
theorem banditRegret_smul_mu_star {K T : ℕ}
    (μ : Fin K → ℝ) (actions : Fin T → Fin K) (c mu_star : ℝ) :
    banditRegret μ actions (c * mu_star) =
      T * (c * mu_star) - ∑ t, μ (actions t) := rfl

/-- §F8b — Bandit regret rewritten via gap function summation. -/
theorem banditRegret_eq_T_mu_minus_sum {K T : ℕ}
    (μ : Fin K → ℝ) (actions : Fin T → Fin K) (mu_star : ℝ) :
    banditRegret μ actions mu_star =
      (T : ℝ) * mu_star - ∑ t, μ (actions t) := rfl

/-- §F8b — Regret with constant action: when every round picks the same arm
    `a`, regret = T·μ⋆ − T·μ_a. -/
theorem banditRegret_constant_action {K T : ℕ}
    (μ : Fin K → ℝ) (a : Fin K) (mu_star : ℝ) :
    banditRegret μ (fun _ : Fin T => a) mu_star =
      (T : ℝ) * mu_star - (T : ℝ) * μ a := by
  unfold banditRegret
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end LTFP
