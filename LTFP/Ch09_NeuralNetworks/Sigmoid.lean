/-
LTFP §9.1 — Sigmoid activation function.

Bach (2024) §9.1, pp. 247-249. The logistic sigmoid is the historical
companion to ReLU as a neural-network activation. It is defined by
`σ(z) = 1 / (1 + exp(-z))`, is smooth, strictly increasing, and squashes
the real line into the open interval `(0, 1)`. It satisfies the
point-symmetry identity `σ(-z) = 1 - σ(z)` about the centre `(0, 1/2)`,
which is the basis for its use as a probabilistic output in binary
classification (logistic regression, cf. Bach (2024) §4.1) and as the
hidden activation in the Cybenko (1989) form of the universal
approximation theorem.
-/
import Mathlib.Analysis.SpecialFunctions.Exp

namespace LTFP

open Real

/-- §9.1 — Logistic sigmoid `σ(z) = 1 / (1 + exp(-z))`. -/
noncomputable def sigmoid (z : ℝ) : ℝ := 1 / (1 + Real.exp (-z))

/-- §9.1 — The denominator `1 + exp(-z)` is strictly positive. Used as
the standing positivity witness whenever we divide by it. -/
theorem one_add_exp_neg_pos (z : ℝ) : 0 < 1 + Real.exp (-z) := by
  have h : 0 < Real.exp (-z) := Real.exp_pos _
  linarith

/-- §9.1 — Sigmoid is strictly positive everywhere: `0 < σ(z)`. -/
theorem sigmoid_pos (z : ℝ) : 0 < sigmoid z := by
  unfold sigmoid
  exact div_pos one_pos (one_add_exp_neg_pos z)

/-- §9.1 — Sigmoid is strictly less than `1` everywhere: `σ(z) < 1`.
This is one half of the "squash into `(0,1)`" property used to read
sigmoid outputs as probabilities (Bach (2024) §4.1, p. 99). -/
theorem sigmoid_lt_one (z : ℝ) : sigmoid z < 1 := by
  unfold sigmoid
  rw [div_lt_one (one_add_exp_neg_pos z)]
  have h : 0 < Real.exp (-z) := Real.exp_pos _
  linarith

/-- §9.1 — Value at the origin: `σ(0) = 1/2`. The centre of symmetry
of the logistic curve. -/
theorem sigmoid_zero : sigmoid 0 = 1 / 2 := by
  unfold sigmoid
  rw [neg_zero, Real.exp_zero]
  norm_num

/-- §9.1 — Point symmetry about `(0, 1/2)`: `σ(-z) = 1 - σ(z)`. This is
the algebraic identity behind the use of sigmoid as a binary-class
posterior, where `P(y = 1 | x) = σ(f(x))` and `P(y = -1 | x) = σ(-f(x))`
(Bach (2024) §4.1, equations 4.4-4.5). -/
theorem sigmoid_neg (z : ℝ) : sigmoid (-z) = 1 - sigmoid z := by
  unfold sigmoid
  have hpos : 0 < 1 + Real.exp (-z) := one_add_exp_neg_pos z
  have hposn : 0 < 1 + Real.exp (-(-z)) := one_add_exp_neg_pos (-z)
  rw [neg_neg]
  -- Goal: `1 / (1 + exp z) = 1 - 1 / (1 + exp (-z))`.
  -- Use `exp (-z) = 1 / exp z` to rewrite the right-hand side.
  have hez : Real.exp (-z) = 1 / Real.exp z := by
    rw [Real.exp_neg, one_div]
  have hez_pos : 0 < Real.exp z := Real.exp_pos _
  rw [hez]
  field_simp
  ring

end LTFP
