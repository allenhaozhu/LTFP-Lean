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

/-- §9.1 — Sigmoid is nonnegative everywhere: `0 ≤ σ(z)`. Weak form of
`sigmoid_pos`, convenient when chaining with lemmas that consume the
nonstrict bound (e.g. `Real.sqrt_le_sqrt`, monotone integrals). -/
theorem sigmoid_nonneg (z : ℝ) : 0 ≤ sigmoid z :=
  (sigmoid_pos z).le

/-- §9.1 — Sigmoid is at most `1` everywhere: `σ(z) ≤ 1`. Weak form of
`sigmoid_lt_one`, packaged for use with monotone-bound APIs that
require a nonstrict upper bound. -/
theorem sigmoid_le_one (z : ℝ) : sigmoid z ≤ 1 :=
  (sigmoid_lt_one z).le

/-- §9.1 — Sigmoid is nonzero everywhere: `σ(z) ≠ 0`. Direct consequence
of `sigmoid_pos`; useful as a `ne_of_gt` hypothesis when dividing by
`σ(z)` in cross-entropy or log-likelihood expressions. -/
theorem sigmoid_ne_zero (z : ℝ) : sigmoid z ≠ 0 :=
  (sigmoid_pos z).ne'

/-- §9.1 — Sigmoid never reaches `1`: `σ(z) ≠ 1`. Direct consequence of
`sigmoid_lt_one`; useful when dividing by `1 - σ(z)` in cross-entropy
or odds-ratio expressions. -/
theorem sigmoid_ne_one (z : ℝ) : sigmoid z ≠ 1 :=
  (sigmoid_lt_one z).ne

/-- §9.1 — Flip of `sigmoid_neg`: `1 - σ(z) = σ(-z)`. Same point-symmetry
identity, oriented to rewrite the complementary probability `1 - σ(z)`
into a single sigmoid evaluation. -/
theorem one_sub_sigmoid (z : ℝ) : 1 - sigmoid z = sigmoid (-z) :=
  (sigmoid_neg z).symm

/-- §9.1 — Partition-of-unity identity: `σ(z) + σ(-z) = 1`. The binary
posterior `P(y = 1 | x) + P(y = -1 | x) = 1` reading of the sigmoid as
used in logistic regression (Bach (2024) §4.1, equations 4.4-4.5). -/
theorem sigmoid_add_sigmoid_neg (z : ℝ) : sigmoid z + sigmoid (-z) = 1 := by
  rw [sigmoid_neg]; ring

end LTFP
