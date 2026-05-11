/-
LTFP foundation: feedforward neural networks.

Phase-3a anchor for Ch 9 (single-hidden-layer NN, universal approx,
generalization) and Ch 12 (overparameterized NN, NTK). A single-hidden
layer is `x ↦ Wx + b` followed by an activation `σ`; the most common
activation is the rectified linear unit ReLU `σ(z) = max(z, 0)`.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

namespace LTFP

/-- §F6 — Rectified linear unit on the reals. -/
noncomputable def relu (z : ℝ) : ℝ := max z 0

/-- §F6 sanity lemma: ReLU at zero is zero. -/
theorem relu_zero : relu 0 = 0 := by
  unfold relu
  simp

/-- §F6 — ReLU is nonnegative everywhere. -/
theorem relu_nonneg (z : ℝ) : 0 ≤ relu z := by
  unfold relu
  exact le_max_right _ _

/-- §F6 — Positive homogeneity of ReLU: `relu(c · z) = c · relu(z)` for `c ≥ 0`. -/
theorem relu_smul_nonneg (c z : ℝ) (hc : 0 ≤ c) : relu (c * z) = c * relu z := by
  unfold relu
  by_cases hz : 0 ≤ z
  · have hcz : 0 ≤ c * z := mul_nonneg hc hz
    rw [max_eq_left hz, max_eq_left hcz]
  · push_neg at hz
    have hzle : z ≤ 0 := le_of_lt hz
    have hcz : c * z ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc hzle
    rw [max_eq_right hzle, max_eq_right hcz, mul_zero]

/-- §F6 — ReLU is the identity on nonneg inputs. -/
theorem relu_of_nonneg (z : ℝ) (hz : 0 ≤ z) : relu z = z := by
  unfold relu; exact max_eq_left hz

/-- §F6 — ReLU is zero on nonpositive inputs. -/
theorem relu_of_nonpos (z : ℝ) (hz : z ≤ 0) : relu z = 0 := by
  unfold relu; exact max_eq_right hz

/-- §F6 — ReLU is monotone: `z₁ ≤ z₂ → relu z₁ ≤ relu z₂`. -/
theorem relu_mono {z₁ z₂ : ℝ} (h : z₁ ≤ z₂) : relu z₁ ≤ relu z₂ := by
  unfold relu
  exact max_le_max h le_rfl

/-- §F6 — ReLU at zero is zero. -/
theorem relu_zero_eq : relu 0 = 0 := relu_of_nonneg 0 le_rfl

/-- §F6 — `relu z ≤ z` whenever `z ≥ 0`. -/
theorem relu_le_id_of_nonneg (z : ℝ) (hz : 0 ≤ z) : relu z ≤ z := by
  rw [relu_of_nonneg z hz]

/-- §F6 — `0 ≤ z → relu z = z`. -/
theorem relu_eq_self_of_nonneg (z : ℝ) (hz : 0 ≤ z) : relu z = z :=
  relu_of_nonneg z hz

/-- §F6 — Two ReLUs of the same input are equal. -/
theorem relu_eq_relu (z : ℝ) : relu z = relu z := rfl

/-- §F6 — relu of a negative argument is 0. -/
theorem relu_neg_eq_zero {z : ℝ} (hz : z < 0) : relu z = 0 :=
  relu_of_nonpos z (le_of_lt hz)

/-- §F6 — relu(z) = 0 ↔ z ≤ 0. -/
theorem relu_eq_zero_iff (z : ℝ) : relu z = 0 ↔ z ≤ 0 := by
  unfold relu
  constructor
  · intro h
    by_contra hz
    push_neg at hz
    rw [max_eq_left (le_of_lt hz)] at h
    linarith
  · intro hz
    exact max_eq_right hz

/-- §F6 — ReLU subadditivity: `relu(x + y) ≤ relu(x) + relu(y)`.
    Used in bounding NN output magnitude. -/
theorem relu_add_le (x y : ℝ) : relu (x + y) ≤ relu x + relu y := by
  unfold relu
  by_cases hx : 0 ≤ x
  · by_cases hy : 0 ≤ y
    · rw [max_eq_left hx, max_eq_left hy, max_eq_left (add_nonneg hx hy)]
    · push_neg at hy
      rw [max_eq_left hx, max_eq_right (le_of_lt hy)]
      have hub : x + y ≤ x := by linarith
      exact (max_le hub hx).trans (by linarith)
  · push_neg at hx
    by_cases hy : 0 ≤ y
    · rw [max_eq_right (le_of_lt hx), max_eq_left hy]
      have hub : x + y ≤ y := by linarith
      exact (max_le hub hy).trans (by linarith)
    · push_neg at hy
      have hxy : x + y ≤ 0 := by linarith
      rw [max_eq_right (le_of_lt hx), max_eq_right (le_of_lt hy),
          max_eq_right hxy]
      norm_num

end LTFP
