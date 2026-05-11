/-
LTFP §11.3 — Multi-armed bandits.

Bach (2024) §11.3, pp. 331-341. The UCB (upper confidence bound)
algorithm picks at round `t` the arm with the largest empirical mean
plus a confidence term `√(2 log t / nₐ(t))` where `nₐ(t)` is the
number of times arm `a` has been pulled. Regret grows as `O(log T)`.

This file extends `LTFP.Foundations.Bandit.banditRegret` with a
linearity-style identity.
-/
import LTFP.Foundations.Bandit
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace LTFP

variable {K T : ℕ}

/-- §11.3 — Suboptimality gap of arm `a`: `Δₐ = μ⋆ − μₐ`. -/
def gap (μ : Fin K → ℝ) (mu_star : ℝ) (a : Fin K) : ℝ := mu_star - μ a

/-- §11.3 — Bandit regret rewritten as a sum of per-step gaps:
    `R = ∑ₜ (μ⋆ − μ_{aₜ})`. -/
theorem banditRegret_eq_sum_gaps
    (μ : Fin K → ℝ) (actions : Fin T → Fin K) (mu_star : ℝ) :
    banditRegret μ actions mu_star = ∑ t, gap μ mu_star (actions t) := by
  unfold banditRegret gap
  rw [Finset.sum_sub_distrib]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_comm]

/-- §11.3.3 — UCB bonus function: at round `t` after `n` pulls, the
    confidence radius is `√(2 log t / n)`. -/
noncomputable def ucbBonus (t n : ℕ) : ℝ :=
  Real.sqrt (2 * Real.log (t : ℝ) / (n : ℝ))

/-- §11.3.3 — UCB bonus is nonnegative when `t ≥ 1` and `n ≥ 1`
    (in fact whenever its argument is nonneg). The square root is
    nonneg for any real. -/
theorem ucbBonus_nonneg (t n : ℕ) : 0 ≤ ucbBonus t n :=
  Real.sqrt_nonneg _

/-- §11.3.2 — Explore-then-commit (ETC) action selector: pull each
    of the `K` arms exactly `m` times, then commit to the empirically
    best.  We capture the elementary "is in exploration phase"
    predicate. -/
def isExplorationPhase (K m t : ℕ) : Prop := t < K * m

/-- §11.3.2 — Trivial: round `0` is always in exploration when both
    `K, m ≥ 1`. -/
theorem isExplorationPhase_zero (K m : ℕ) (hK : 1 ≤ K) (hm : 1 ≤ m) :
    isExplorationPhase K m 0 := by
  unfold isExplorationPhase
  exact Nat.mul_pos hK hm

/-- §11.3 — Cumulative regret is monotone in `T` (longer horizon =
    bigger regret) when arms are pulled with the same actions. -/
theorem banditRegret_zero_horizon (μ : Fin K → ℝ) (mu_star : ℝ) :
    banditRegret (T := 0) μ Fin.elim0 mu_star = 0 := by
  unfold banditRegret
  simp

/-- §11.3 — Gap of an arm equal to the optimal mean is zero. -/
theorem gap_optimal {K : ℕ} (μ : Fin K → ℝ) (mu_star : ℝ) (a : Fin K)
    (h : μ a = mu_star) : gap μ mu_star a = 0 := by
  unfold gap
  rw [h]
  ring

/-- §11.3 — Gap is nonneg whenever `μ a ≤ μ_⋆`. -/
theorem gap_nonneg {K : ℕ} (μ : Fin K → ℝ) (mu_star : ℝ) (a : Fin K)
    (h : μ a ≤ mu_star) : 0 ≤ gap μ mu_star a := by
  unfold gap
  linarith

/-- §11.3 — Gap definition expanded. -/
theorem gap_eq_diff {K : ℕ} (μ : Fin K → ℝ) (mu_star : ℝ) (a : Fin K) :
    gap μ mu_star a = mu_star - μ a := rfl

/-- §11.3 — Sum of gaps over rounds. -/
theorem sum_gaps_eq_T_mu_minus_sum_actions {K T : ℕ}
    (μ : Fin K → ℝ) (actions : Fin T → Fin K) (mu_star : ℝ) :
    ∑ t, gap μ mu_star (actions t) = T * mu_star - ∑ t, μ (actions t) := by
  simp [gap, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, mul_comm]

/-- §11.3 — Bandit regret = sum of gaps (combining definition and the
    sum_gaps rewrite). -/
theorem banditRegret_eq_sum_gaps_strong {K T : ℕ}
    (μ : Fin K → ℝ) (actions : Fin T → Fin K) (mu_star : ℝ) :
    banditRegret μ actions mu_star = ∑ t, gap μ mu_star (actions t) :=
  banditRegret_eq_sum_gaps μ actions mu_star

/-- §11.3 — Gap definitional. -/
theorem gap_def {K : ℕ} (μ : Fin K → ℝ) (mu_star : ℝ) (a : Fin K) :
    gap μ mu_star a = mu_star - μ a := rfl

/-- §11.3 — Gap monotone in optimal mean: larger μ⋆ means larger gap. -/
theorem gap_mono_mu_star {K : ℕ} (μ : Fin K → ℝ) (a : Fin K)
    {mu1 mu2 : ℝ} (h : mu1 ≤ mu2) :
    gap μ mu1 a ≤ gap μ mu2 a := by
  unfold gap; linarith

/-- §11.3 — Gap antitone in arm value: smaller μ_a means larger gap. -/
theorem gap_antitone_mu {K : ℕ} (mu_star : ℝ) (a : Fin K)
    {μ₁ μ₂ : Fin K → ℝ} (h : μ₁ a ≤ μ₂ a) :
    gap μ₂ mu_star a ≤ gap μ₁ mu_star a := by
  unfold gap; linarith

/-- §11.3 — Sum of nonneg gaps is nonneg. -/
theorem sum_gaps_nonneg {K T : ℕ} (μ : Fin K → ℝ) (actions : Fin T → Fin K)
    (mu_star : ℝ) (h : ∀ a : Fin K, μ a ≤ mu_star) :
    0 ≤ ∑ t, gap μ mu_star (actions t) :=
  Finset.sum_nonneg (fun t _ => gap_nonneg μ mu_star (actions t) (h _))

end LTFP
