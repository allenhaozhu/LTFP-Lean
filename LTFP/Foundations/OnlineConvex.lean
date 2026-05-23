/-
LTFP foundation: online convex optimization.

Phase-3a anchor for Ch 11 (online convex optimization, bandits,
online mirror descent, online lower bounds) and Ch 12. In OCO, at
round `t` the player picks `xₜ` from a convex set, suffers loss
`fₜ(xₜ)`, and seeks to minimize regret
`R_T(x⋆) = ∑ₜ fₜ(xₜ) − ∑ₜ fₜ(x⋆)` against the best fixed `x⋆`.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace LTFP

/-- §F8a — OCO regret of a sequence of plays `xs : Fin T → E`
    against a comparator `xstar : E`, given a sequence of loss
    functions `fs : Fin T → E → ℝ`. -/
def regret {T : ℕ} {E : Type*}
    (fs : Fin T → E → ℝ) (xs : Fin T → E) (xstar : E) : ℝ :=
  ∑ t, fs t (xs t) - ∑ t, fs t xstar

/-- §F8a sanity lemma: regret of the comparator against itself is zero. -/
theorem regret_self {T : ℕ} {E : Type*}
    (fs : Fin T → E → ℝ) (xstar : E) :
    regret fs (fun _ => xstar) xstar = 0 := by
  unfold regret
  exact sub_self _

/-- §F8a — Cumulative loss `L_T(x) = ∑ₜ fₜ(x)` of a fixed action `x`. -/
def cumLoss {T : ℕ} {E : Type*} (fs : Fin T → E → ℝ) (x : E) : ℝ :=
  ∑ t, fs t x

/-- §F8a — Regret rewritten via cumulative losses:
    `R_T(xstar) = L_T(xs) − L_T(xstar)` where the first cumulative
    loss is along the played trajectory. -/
theorem regret_eq_cumLoss_diff {T : ℕ} {E : Type*}
    (fs : Fin T → E → ℝ) (xs : Fin T → E) (xstar : E) :
    regret fs xs xstar = (∑ t, fs t (xs t)) - cumLoss fs xstar := rfl

/-- §F8a — Cumulative loss on an empty horizon is zero. -/
theorem cumLoss_zero_horizon {E : Type*}
    (fs : Fin 0 → E → ℝ) (x : E) :
    cumLoss fs x = 0 := by
  unfold cumLoss
  simp

/-- §F8a — Cumulative loss with all-zero loss functions is zero. -/
theorem cumLoss_zero_fs {T : ℕ} {E : Type*} (x : E) :
    cumLoss (fun _ : Fin T => fun _ : E => (0 : ℝ)) x = 0 := by
  unfold cumLoss
  simp

/-- §F8a — Cumulative loss with constant loss `c` over `T` rounds is `T·c`. -/
theorem cumLoss_const {T : ℕ} {E : Type*} (c : ℝ) (x : E) :
    cumLoss (fun _ : Fin T => fun _ : E => c) x = T * c := by
  unfold cumLoss
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- §F8a — Cumulative loss is additive in the loss functions:
    `cumLoss (f + g) x = cumLoss f x + cumLoss g x`. -/
theorem cumLoss_add {T : ℕ} {E : Type*}
    (fs gs : Fin T → E → ℝ) (x : E) :
    cumLoss (fun t y => fs t y + gs t y) x = cumLoss fs x + cumLoss gs x := by
  unfold cumLoss
  exact Finset.sum_add_distrib

/-- §F8a — With all-zero loss functions, regret vanishes against any
    comparator and any play sequence. -/
theorem regret_zero_loss {T : ℕ} {E : Type*}
    (xs : Fin T → E) (xstar : E) :
    regret (fun _ : Fin T => fun _ : E => (0 : ℝ)) xs xstar = 0 := by
  unfold regret
  simp

/-- §F8a — With constant loss `c` independent of action, regret is zero:
    every player and comparator pays the same cumulative loss. -/
theorem regret_const_loss {T : ℕ} {E : Type*}
    (c : ℝ) (xs : Fin T → E) (xstar : E) :
    regret (fun _ : Fin T => fun _ : E => c) xs xstar = 0 := by
  unfold regret
  simp

/-- §F8a — Adding a per-round constant `c t` (independent of the action)
    to the loss functions leaves regret invariant. The constants cancel
    between the played trajectory and the comparator. -/
theorem regret_add_const {T : ℕ} {E : Type*}
    (fs : Fin T → E → ℝ) (c : Fin T → ℝ) (xs : Fin T → E) (xstar : E) :
    regret (fun t y => fs t y + c t) xs xstar = regret fs xs xstar := by
  unfold regret
  have h₁ : ∑ t, (fs t (xs t) + c t) = (∑ t, fs t (xs t)) + ∑ t, c t :=
    Finset.sum_add_distrib
  have h₂ : ∑ t, (fs t xstar + c t) = (∑ t, fs t xstar) + ∑ t, c t :=
    Finset.sum_add_distrib
  rw [h₁, h₂]
  ring

/-- §F8a — Average-regret bound: if regret is bounded by `B` and the
    horizon is positive, the per-round (average) regret is bounded by
    `B / T`. This is the elementary rearrangement underlying every
    online-learning rate. -/
theorem average_regret_le_of_regret_le {T : ℕ} {E : Type*}
    (fs : Fin T → E → ℝ) (xs : Fin T → E) (xstar : E) (B : ℝ)
    (hT : 0 < T) (h : regret fs xs xstar ≤ B) :
    regret fs xs xstar / T ≤ B / T := by
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  exact (div_le_div_iff_of_pos_right hTpos).mpr h

end LTFP
