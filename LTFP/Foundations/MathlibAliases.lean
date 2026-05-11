/-
LTFP foundation: Mathlib aliases.

A grab-bag of LTFP-namespace aliases for commonly-cited Mathlib lemmas
appearing throughout Bach (2024). Each is a one-line re-export to
keep downstream chapter files terse and consistent in naming.
-/
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Tactic.Linarith

namespace LTFP

open Real

/-- §F10 alias — Real exp is positive. -/
theorem exp_pos_alias (x : ℝ) : 0 < Real.exp x := exp_pos x

/-- §F10 alias — Real log composition: `log (exp x) = x`. -/
theorem log_exp_alias (x : ℝ) : log (Real.exp x) = x := Real.log_exp x

/-- §F10 alias — `1 + α ≤ exp α`. -/
theorem one_plus_le_exp (α : ℝ) : 1 + α ≤ Real.exp α := by
  simpa [add_comm] using Real.add_one_le_exp α

/-- §F10 alias — Power nonneg from nonneg base. -/
theorem pow_nonneg_anchor {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : 0 ≤ x^n :=
  pow_nonneg hx n

/-- §F10 alias — Triangle inequality for absolute value: `|x + y| ≤ |x| + |y|`. -/
theorem abs_triangle (x y : ℝ) : |x + y| ≤ |x| + |y| := abs_add_le x y

/-- §F10 alias — Squared real is nonneg. -/
theorem sq_nonneg_anchor (x : ℝ) : 0 ≤ x^2 := sq_nonneg x

/-- §F10 alias — sqrt(x²) = |x|. -/
theorem sqrt_sq_eq_abs (x : ℝ) : Real.sqrt (x^2) = |x| := Real.sqrt_sq_eq_abs x

/-- §F10 alias — exp is strictly monotone. -/
theorem exp_strict_mono : StrictMono Real.exp := Real.exp_strictMono

/-- §F10 alias — `log 1 = 0`. -/
theorem log_one_alias : Real.log 1 = 0 := Real.log_one

/-- §F10 alias — `0 ≤ exp x - 1 - x` (convexity of exp at 0). -/
theorem exp_sub_one_sub_self_nonneg (x : ℝ) :
    0 ≤ Real.exp x - 1 - x := by
  have h := one_plus_le_exp x
  linarith

/-- §F10 alias — `1 ≤ exp` for nonneg arguments. -/
theorem one_le_exp_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 1 ≤ Real.exp x := by
  have h := one_plus_le_exp x
  linarith

/-- §F10 — Combination: `2 ≤ exp 1 + 1` follows from `e > 1`. -/
theorem two_le_exp_one_plus_one : (2 : ℝ) ≤ Real.exp 1 + 1 := by
  have h := one_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)
  linarith

/-- §F10 alias — `Real.log 1 ≤ Real.log x` for `1 ≤ x`. -/
theorem log_nonneg_of_one_le {x : ℝ} (hx : 1 ≤ x) : 0 ≤ Real.log x :=
  Real.log_nonneg hx

/-- §F10 — exp(0) = 1. -/
theorem exp_zero_eq_one : Real.exp 0 = 1 := Real.exp_zero

/-- §F10 — exp(neg) flips sign. -/
theorem exp_neg_eq_inv (x : ℝ) : Real.exp (-x) = (Real.exp x)⁻¹ := Real.exp_neg x

/-- §F10 — sub_nonneg via linarith. -/
theorem sub_nonneg_of_le {a b : ℝ} (h : a ≤ b) : 0 ≤ b - a := by linarith

/-- §F10 — abs of zero is zero. -/
theorem abs_zero_eq_zero : |(0 : ℝ)| = 0 := abs_zero

/-- §F10 — abs is nonneg. -/
theorem abs_nonneg_anchor (x : ℝ) : 0 ≤ |x| := abs_nonneg x

/-- §F10 — abs preserves under negation. -/
theorem abs_neg_anchor (x : ℝ) : |-x| = |x| := abs_neg x

end LTFP
