/-
LTFP §4.1 — Convexification of the risk.

Bach (2024) §4.1, pp. 72-79. For binary classification with `𝒴 = {-1, 1}`
and 0-1 loss, optimization is intractable directly. The standard remedy
is to learn a real-valued *score function* `g : 𝒳 → ℝ` and predict
`f(x) = sign g(x)`, replacing the 0-1 loss with a convex *surrogate*
`Φ : ℝ → ℝ` so the empirical risk becomes
`(1/n) ∑ᵢ Φ(yᵢ · g(xᵢ))`.

This file defines the four classical surrogates (square, logistic,
hinge, exponential) and proves their nonnegativity. The full
classification-calibration theorem (Bartlett et al. 2006,
Proposition 4.1, ♦) is left for a follow-up wave.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace LTFP

open Real

/-- §4.1 — Square / quadratic surrogate `Φ(u) = (u − 1)²`.
    Yields least-squares classification when paired with `y · g(x)`. -/
def phiSquare (u : ℝ) : ℝ := (u - 1)^2

/-- §4.1 — Hinge surrogate `Φ(u) = max(1 − u, 0)`.
    Yields the support vector machine (SVM). -/
noncomputable def phiHinge (u : ℝ) : ℝ := max (1 - u) 0

/-- §4.1 — Logistic surrogate `Φ(u) = log(1 + exp(-u))`.
    Yields logistic regression / cross-entropy loss. -/
noncomputable def phiLogistic (u : ℝ) : ℝ := log (1 + exp (-u))

/-- §4.1 — Exponential surrogate `Φ(u) = exp(-u)`.
    Yields the AdaBoost framework (Ch 10). -/
noncomputable def phiExponential (u : ℝ) : ℝ := exp (-u)

/-- §4.1 — The square surrogate is nonnegative everywhere. -/
theorem phiSquare_nonneg (u : ℝ) : 0 ≤ phiSquare u := by
  unfold phiSquare; exact sq_nonneg _

/-- §4.1 — The hinge surrogate is nonnegative everywhere. -/
theorem phiHinge_nonneg (u : ℝ) : 0 ≤ phiHinge u := by
  unfold phiHinge; exact le_max_right _ _

/-- §4.1 — The logistic surrogate is nonnegative everywhere.
    `log(1 + exp(-u)) ≥ log 1 = 0` since `exp(-u) ≥ 0`. -/
theorem phiLogistic_nonneg (u : ℝ) : 0 ≤ phiLogistic u := by
  unfold phiLogistic
  have h : (1 : ℝ) ≤ 1 + exp (-u) := by
    have := exp_pos (-u); linarith
  calc (0 : ℝ) = log 1 := by simp
    _ ≤ log (1 + exp (-u)) := log_le_log one_pos h

/-- §4.1 — The exponential surrogate is positive everywhere. -/
theorem phiExponential_pos (u : ℝ) : 0 < phiExponential u := by
  unfold phiExponential; exact exp_pos _

/-- §4.1.4 — Margin-based 0-1 surrogate `Φ_{0-1}(u) = ½ · 1[u ≤ 0] +
    ½ · 1[u < 0]`, simplified here to the equivalent
    `Φ_{0-1}(u) = ½ · (1 − sign u)` form's even simpler bound:
    the indicator `1[u ≤ 0]` is nonneg and at most 1. -/
noncomputable def phiZeroOne (u : ℝ) : ℝ := if u ≤ 0 then 1 else 0

/-- §4.1.4 — The 0-1 surrogate is nonnegative. -/
theorem phiZeroOne_nonneg (u : ℝ) : 0 ≤ phiZeroOne u := by
  unfold phiZeroOne
  split_ifs <;> norm_num

/-- §4.1.4 — The 0-1 surrogate is at most 1. -/
theorem phiZeroOne_le_one (u : ℝ) : phiZeroOne u ≤ 1 := by
  unfold phiZeroOne
  split_ifs <;> norm_num

/-- §4.1.4 — **Φ_hinge upper-bounds the 0-1 surrogate.** This is the
    classical "hinge majorizes 0-1" inequality used in the Φ-risk
    bounds of §4.1.4. For `u ≤ 0`: `1 − u ≥ 1 = phiZeroOne u`. For
    `u > 0`: `phiZeroOne u = 0 ≤ phiHinge u`. -/
theorem phiZeroOne_le_phiHinge (u : ℝ) : phiZeroOne u ≤ phiHinge u := by
  unfold phiZeroOne phiHinge
  split_ifs with h
  · exact le_max_of_le_left (by linarith)
  · exact le_max_right _ _

/-- §4.1 — Hinge surrogate vanishes on `u ≥ 1`. -/
theorem phiHinge_eq_zero_of_ge_one (u : ℝ) (h : 1 ≤ u) : phiHinge u = 0 := by
  unfold phiHinge
  rw [max_eq_right (by linarith : (1 - u) ≤ 0)]

/-- §4.1 — On `u ≤ 1`, hinge equals `1 − u`. -/
theorem phiHinge_eq_one_sub_of_le_one (u : ℝ) (h : u ≤ 1) :
    phiHinge u = 1 - u := by
  unfold phiHinge
  rw [max_eq_left (by linarith : (0 : ℝ) ≤ 1 - u)]

/-- §4.1 — Squared surrogate at the well-classified point `u = 1`
    vanishes (the only zero of `Φ_square`). -/
theorem phiSquare_one : phiSquare 1 = 0 := by
  unfold phiSquare; norm_num

/-- §4.1 — Logistic surrogate at zero is `log 2`. -/
theorem phiLogistic_zero : phiLogistic 0 = log 2 := by
  unfold phiLogistic
  simp [exp_zero]
  ring_nf

/-- §4.1 — Exponential surrogate at zero equals 1. -/
theorem phiExponential_zero : phiExponential 0 = 1 := by
  unfold phiExponential; rw [neg_zero, exp_zero]

/-- §4.1 — Square surrogate at zero equals 1. -/
theorem phiSquare_zero : phiSquare 0 = 1 := by
  unfold phiSquare; norm_num

/-- §4.1 — Hinge surrogate at zero equals 1. -/
theorem phiHinge_zero : phiHinge 0 = 1 := by
  unfold phiHinge
  rw [sub_zero]
  exact max_eq_left (by linarith : (0 : ℝ) ≤ 1)

/-- §4.1 — Hinge surrogate is monotone-decreasing in `u`. -/
theorem phiHinge_antitone {u v : ℝ} (h : u ≤ v) :
    phiHinge v ≤ phiHinge u := by
  unfold phiHinge
  exact max_le_max (by linarith) le_rfl

/-- §4.1 — Square surrogate at `u = 1` minus `u = 0`: `phiSquare 1 < phiSquare 0`. -/
theorem phiSquare_one_lt_zero : phiSquare 1 < phiSquare 0 := by
  rw [phiSquare_one, phiSquare_zero]
  norm_num

/-- §4.1 — phiSquare(u) ≥ 0 with equality iff u = 1. -/
theorem phiSquare_eq_zero_iff (u : ℝ) : phiSquare u = 0 ↔ u = 1 := by
  unfold phiSquare
  rw [sq_eq_zero_iff, sub_eq_zero]

/-- §4.1 — Hinge value for `u = 0` is 1 (positive margin failure). -/
theorem phiHinge_at_zero_is_one : phiHinge 0 = 1 := phiHinge_zero

/-- §4.1 — Square surrogate is symmetric around `u = 1`. -/
theorem phiSquare_symm_around_one (u : ℝ) :
    phiSquare (1 + u) = phiSquare (1 - u) := by
  unfold phiSquare; ring

/-- §4.1 — phiExp(u) ≥ phiExp(v) when u ≤ v. -/
theorem phiExponential_antitone {u v : ℝ} (h : u ≤ v) :
    phiExponential v ≤ phiExponential u := by
  unfold phiExponential
  exact Real.exp_le_exp.mpr (by linarith)

/-- §4.1 — phiExp at large positive value is small (anchor). -/
theorem phiExponential_le_one_of_nonneg {u : ℝ} (hu : 0 ≤ u) :
    phiExponential u ≤ 1 := by
  unfold phiExponential
  rw [show (1 : ℝ) = Real.exp 0 from by rw [Real.exp_zero]]
  exact Real.exp_le_exp.mpr (by linarith)

/-- §4.1.4 — **Exponential surrogate majorizes the 0-1 surrogate.**
    This is the key "calibration" inequality for AdaBoost
    (Bach §4.1, p. 76, eq. (4.4) / Schapire-Freund 1997): if `u ≤ 0`
    the 0-1 indicator is `1 ≤ exp(-u)`; if `u > 0` the indicator is
    `0 < exp(-u)`. Hence minimizing the exponential Φ-risk controls
    the 0-1 misclassification rate. -/
theorem phiZeroOne_le_phiExponential (u : ℝ) :
    phiZeroOne u ≤ phiExponential u := by
  unfold phiZeroOne phiExponential
  split_ifs with h
  · -- u ≤ 0, so -u ≥ 0, so exp(-u) ≥ exp 0 = 1
    have : (1 : ℝ) = Real.exp 0 := by rw [Real.exp_zero]
    rw [this]
    exact Real.exp_le_exp.mpr (by linarith)
  · -- u > 0, RHS positive, LHS = 0
    exact (Real.exp_pos _).le

/-- §4.1 — **Hinge surrogate is positive exactly when `u < 1`.** This
    pins down the *sparsity* of the SVM support: only points with
    margin `< 1` contribute to the loss (Bach §4.1, p. 75). The two
    directions follow from the case split of the `max`. -/
theorem phiHinge_pos_iff_lt_one (u : ℝ) :
    0 < phiHinge u ↔ u < 1 := by
  unfold phiHinge
  constructor
  · intro h
    by_contra hge
    push_neg at hge
    have : max (1 - u) 0 = 0 :=
      max_eq_right (by linarith : (1 - u) ≤ 0)
    linarith
  · intro h
    have : (1 - u) ≤ max (1 - u) 0 := le_max_left _ _
    linarith

/-- §4.1.4 — **Square surrogate majorizes the 0-1 surrogate.** Together
    with `phiZeroOne_le_phiHinge` and `phiZeroOne_le_phiExponential`,
    this is the third pillar of surrogate-majorization (Bach §4.1.4,
    pp. 76-77). For `u ≤ 0`: `(u-1)^2 ≥ 1 = phiZeroOne u` since
    `u - 1 ≤ -1`. For `u > 0`: `phiZeroOne u = 0 ≤ (u-1)^2`. -/
theorem phiZeroOne_le_phiSquare (u : ℝ) :
    phiZeroOne u ≤ phiSquare u := by
  unfold phiZeroOne phiSquare
  split_ifs with h
  · -- u ≤ 0, so u - 1 ≤ -1, so (u - 1)^2 ≥ 1
    have h1 : u - 1 ≤ -1 := by linarith
    -- (u - 1)^2 = (1 - u)^2 ≥ 1 since 1 - u ≥ 1
    have h2 : (1 : ℝ) ≤ 1 - u := by linarith
    have h3 : (u - 1)^2 = (1 - u)^2 := by ring
    rw [h3]
    have h4 : (1 : ℝ)^2 ≤ (1 - u)^2 :=
      pow_le_pow_left₀ (by norm_num) h2 2
    simpa using h4
  · -- u > 0, RHS nonneg, LHS = 0
    exact sq_nonneg _

/-- §4.1.4 — **Scaled logistic surrogate majorizes the 0-1 surrogate.**
    `phiZeroOne u ≤ phiLogistic u / log 2`. Together with the hinge,
    exponential, and square majorizations, this completes the four
    classical Φ-risk bounds (Bach §4.1.4, eq. (4.4)). For `u ≤ 0`:
    `phiLogistic u ≥ phiLogistic 0 = log 2`, so the quotient is `≥ 1`.
    For `u > 0`: `phiLogistic u ≥ 0` and `log 2 > 0`, so quotient ≥ 0. -/
theorem phiZeroOne_le_phiLogistic_div_log_two (u : ℝ) :
    phiZeroOne u ≤ phiLogistic u / Real.log 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  unfold phiZeroOne phiLogistic
  split_ifs with h
  · -- u ≤ 0, so -u ≥ 0, so exp(-u) ≥ 1, so 1 + exp(-u) ≥ 2,
    -- so log(1 + exp(-u)) ≥ log 2, so the quotient ≥ 1.
    have hexp : (1 : ℝ) ≤ Real.exp (-u) := by
      rw [show (1 : ℝ) = Real.exp 0 from by rw [Real.exp_zero]]
      exact Real.exp_le_exp.mpr (by linarith)
    have h2 : (2 : ℝ) ≤ 1 + Real.exp (-u) := by linarith
    have hpos : (0 : ℝ) < 1 + Real.exp (-u) := by
      have := Real.exp_pos (-u); linarith
    have hlog : Real.log 2 ≤ Real.log (1 + Real.exp (-u)) :=
      Real.log_le_log (by norm_num) h2
    rw [le_div_iff₀ hlog2]
    linarith
  · -- u > 0, RHS nonneg, LHS = 0
    apply div_nonneg _ hlog2.le
    have hpos : (1 : ℝ) ≤ 1 + Real.exp (-u) := by
      have := Real.exp_pos (-u); linarith
    calc (0 : ℝ) = Real.log 1 := by simp
      _ ≤ Real.log (1 + Real.exp (-u)) := Real.log_le_log one_pos hpos

end LTFP
