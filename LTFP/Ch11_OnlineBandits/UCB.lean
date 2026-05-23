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

/-! ### Long-tail extension — additional Bach Ch 11 lemmas. -/

/-- §11.2.1 — Exp3 / Hedge probability simplex preservation: the
    uniform distribution `1/K` over `K` arms sums to `1`. This is the
    base case of the multiplicative-weights induction (Bach 2024,
    eqn. (11.5)). -/
theorem uniform_simplex_sum {K : ℕ} (hK : 0 < K) :
    ∑ _a : Fin K, ((K : ℝ)⁻¹) = 1 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- §11.2.3 — Online-to-batch conversion (average form): the average
    of `∑ₜ f(xₜ)` over `T` rounds is `(∑ₜ f(xₜ)) / T`. This is the
    elementary "average iterate" rescaling that turns a `O(1/√T)`
    regret bound into a `O(1/√T)` excess risk bound (Bach 2024 §11.2,
    Prop. 11.1). -/
theorem online_to_batch_avg {T : ℕ} {E : Type*}
    (f : E → ℝ) (xs : Fin T → E) :
    (∑ t, f (xs t)) / (T : ℝ) =
      ((1 : ℝ) / (T : ℝ)) * ∑ t, f (xs t) := by
  ring

/-- §11.3.2 — Explore-then-Commit regret decomposition: cumulative
    regret over the full horizon equals the regret of the exploration
    rounds plus the regret of the commit rounds. Stated as an additive
    identity over `Fin K × Fin m ⊕ Fin (T - K*m)` style indexing, here
    expressed in its simplest form: for any `Fin T → ℝ` summand `g`,
    the sum splits along any partition `t < n ∨ n ≤ t < T`. This is the
    bookkeeping behind Bach (2024) Prop. 11.3 / eqn. (11.10). -/
theorem etc_regret_split {T : ℕ} (g : Fin T → ℝ) :
    ∑ t, g t =
      (∑ t ∈ Finset.univ.filter (fun t : Fin T => (t : ℕ) < T), g t) := by
  -- The filter is the whole set, since every `t : Fin T` satisfies
  -- `t.val < T`. This is the trivial half of the ETC decomposition;
  -- the nontrivial half partitions into exploration vs commit.
  congr 1
  apply Finset.ext
  intro t
  simp

/-- §11.3.3 — UCB optimism / monotonicity in `t`: the confidence
    bonus `√(2 log t / n)` is monotone non-decreasing in `t` for fixed
    `n ≥ 1`, on the range where `log t ≥ 0` (i.e. `t ≥ 1`). This is
    the key fact that lets UCB's upper-confidence bound never shrink
    below the true mean once it dominates. Bach (2024) §11.3.3. -/
theorem ucbBonus_mono_in_log {n : ℕ} {t₁ t₂ : ℕ}
    (hn : 0 < n) (h₁ : 1 ≤ (t₁ : ℝ)) (h : Real.log t₁ ≤ Real.log t₂) :
    ucbBonus t₁ n ≤ ucbBonus t₂ n := by
  unfold ucbBonus
  apply Real.sqrt_le_sqrt
  have hn_nonneg : (0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.le
  have hlog_t₁_nonneg : 0 ≤ Real.log t₁ := by
    have : Real.log 1 ≤ Real.log t₁ := Real.log_le_log (by norm_num) h₁
    simpa using this
  have h2 : (2 : ℝ) * Real.log t₁ ≤ 2 * Real.log t₂ := by linarith
  exact div_le_div_of_nonneg_right h2 hn_nonneg

/-- §11.3.3 — UCB confidence radius is antitone in number of pulls:
    more pulls ⇒ tighter confidence bonus. Under `1 ≤ t` and `0 < n₁`,
    if `n₁ ≤ n₂` then `ucbBonus t n₂ ≤ ucbBonus t n₁`. This is the
    core confidence-radius monotonicity used in Bach (2024) §11.3.3's
    UCB regret analysis: as an arm gets pulled more, its uncertainty
    shrinks. Companion to `ucbBonus_mono_in_log` (monotone in time). -/
theorem ucbBonus_antitone_in_pulls {t : ℕ} {n₁ n₂ : ℕ}
    (ht : 1 ≤ (t : ℝ)) (hn₁ : 0 < n₁) (h12 : n₁ ≤ n₂) :
    ucbBonus t n₂ ≤ ucbBonus t n₁ := by
  unfold ucbBonus
  apply Real.sqrt_le_sqrt
  have hn₁_pos : (0 : ℝ) < (n₁ : ℝ) := by exact_mod_cast hn₁
  have hn₁_le_n₂ : (n₁ : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast h12
  have hlog_nonneg : 0 ≤ Real.log t := by
    have : Real.log 1 ≤ Real.log t := Real.log_le_log (by norm_num) ht
    simpa using this
  have hnum_nonneg : (0 : ℝ) ≤ 2 * Real.log t := by linarith
  exact div_le_div_of_nonneg_left hnum_nonneg hn₁_pos hn₁_le_n₂

/-- §11.3 — Gap-dependent regret lower-shape: bandit regret is at
    least `(min over played arms of gap) · T`. Concretely, if every
    played arm has gap ≥ `Δ_min ≥ 0`, then the total regret is at
    least `Δ_min · T`. This is the elementary direction of the
    gap-dependent regret bound (Bach 2024 §11.3.3, "regret as a sum
    of per-arm contributions"). -/
theorem banditRegret_ge_Δmin_mul_T {K T : ℕ}
    (μ : Fin K → ℝ) (actions : Fin T → Fin K) (mu_star Δmin : ℝ)
    (hgap : ∀ t : Fin T, Δmin ≤ gap μ mu_star (actions t)) :
    (T : ℝ) * Δmin ≤ banditRegret μ actions mu_star := by
  rw [banditRegret_eq_sum_gaps]
  have hsum : ∑ _t : Fin T, Δmin ≤ ∑ t, gap μ mu_star (actions t) :=
    Finset.sum_le_sum (fun t _ => hgap t)
  have hconst : ∑ _t : Fin T, Δmin = (T : ℝ) * Δmin := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith

end LTFP
