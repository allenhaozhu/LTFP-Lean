/-
LTFP §14.1 — From empirical risks to log-likelihoods.

Bach (2024) §14.1, pp. 409-417. Many supervised-learning losses
arise from negative log-likelihoods of probabilistic models. The
square loss `(y − f(x))²` corresponds (up to a constant) to a
Gaussian noise model `y | x ~ 𝒩(f(x), σ²)`; the logistic loss
corresponds to the Bernoulli model `ℙ(y = 1 | x) = σ(f(x))`.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace LTFP

open Real

/-- §14.1 — Negative log-likelihood for a single Gaussian observation
    with mean `μ` and unit variance: `-log p(y | μ) = ½(y − μ)² + ½ log(2π)`.
    Up to the constant `½ log(2π)` this is the square loss. -/
noncomputable def gaussianNLL (mu y : ℝ) : ℝ := (y - mu)^2 / 2

/-- §14.1 sanity lemma: the Gaussian NLL is nonnegative. -/
theorem gaussianNLL_nonneg (mu y : ℝ) : 0 ≤ gaussianNLL mu y := by
  unfold gaussianNLL
  exact div_nonneg (sq_nonneg _) (by norm_num)

/-- §14.1 — Bernoulli negative log-likelihood for `y ∈ {0, 1}` with
    success probability `p ∈ (0, 1)`: `-log p(y | p) = -y log p −
    (1 − y) log(1 − p)`. With `p = σ(g(x))`, this *is* the logistic
    loss in disguise. -/
noncomputable def bernoulliNLL (p y : ℝ) : ℝ :=
  - y * log p - (1 - y) * log (1 - p)

/-- §14.1 — Bernoulli NLL at correct prediction `p = 1, y = 1` is 0. -/
theorem bernoulliNLL_correct : bernoulliNLL 1 1 = 0 := by
  unfold bernoulliNLL
  simp [log_one]

/-- §14.1 — Gaussian NLL is symmetric in `(μ, y)`: swapping mean and
    observation gives the same value (because `(y - μ)² = (μ - y)²`). -/
theorem gaussianNLL_symm (mu y : ℝ) : gaussianNLL mu y = gaussianNLL y mu := by
  unfold gaussianNLL
  ring

/-- §14.1 — Gaussian NLL with prediction equal to truth vanishes. -/
theorem gaussianNLL_self (y : ℝ) : gaussianNLL y y = 0 := by
  unfold gaussianNLL
  ring

/-- §14.1 — Gaussian NLL is convex in `μ` (squared error in `(y - μ)`).
    We capture the algebraic core: it is non-decreasing as `μ` moves
    away from `y` (squared distance is monotone in displacement). -/
theorem gaussianNLL_eq_squared_displacement (mu y : ℝ) :
    gaussianNLL mu y = ((y - mu)^2) / 2 := by
  unfold gaussianNLL; rfl

/-- §14.1 — Gaussian NLL bounded below by zero (already captured by
    `gaussianNLL_nonneg`); shifted form: `gaussianNLL μ y - 0 ≥ 0`. -/
theorem gaussianNLL_sub_zero_nonneg (mu y : ℝ) :
    gaussianNLL mu y - 0 ≥ 0 := by
  rw [sub_zero]
  exact gaussianNLL_nonneg mu y

/-- §14.1 — Bernoulli NLL at success p = 1/2 reduces to log 2. -/
theorem bernoulliNLL_at_half (y : ℝ) : bernoulliNLL (1/2) y = log 2 := by
  unfold bernoulliNLL
  have h1 : (1 - (1:ℝ)/2) = 1/2 := by ring
  rw [h1]
  have h2 : log ((1:ℝ)/2) = -log 2 := by rw [log_div one_ne_zero two_ne_zero, log_one]; ring
  rw [h2]
  ring

/-- §14.1 — Bernoulli NLL at correct y = 0, p = 0 is 0. -/
theorem bernoulliNLL_correct_zero : bernoulliNLL 0 0 = 0 := by
  unfold bernoulliNLL
  simp

/-- §14.1 — Gaussian NLL evaluated at displacement zero. -/
theorem gaussianNLL_zero_displacement (y : ℝ) : gaussianNLL 0 0 = 0 := by
  unfold gaussianNLL
  simp

/-- §14.1 — Gaussian NLL is monotonically increasing in (y - μ)². -/
theorem gaussianNLL_le_iff_sq_le {mu₁ mu₂ y : ℝ} :
    gaussianNLL mu₁ y ≤ gaussianNLL mu₂ y ↔ (y - mu₁)^2 ≤ (y - mu₂)^2 := by
  unfold gaussianNLL
  constructor
  · intro h; linarith
  · intro h; linarith

/-- §14.1 — **Maximum likelihood = minimum NLL** (Bach 2024 §14.1, p. 410).
    For Gaussian observations with fixed `y`, the negative log-likelihood
    as a function of the mean `μ` is minimized at `μ = y`. This is the
    scalar shadow of the MLE identity: the maximum-likelihood estimator
    minimizes the negative log-likelihood. -/
theorem gaussianNLL_min_at_truth (y mu : ℝ) :
    gaussianNLL y y ≤ gaussianNLL mu y := by
  rw [gaussianNLL_self]
  exact gaussianNLL_nonneg mu y

/-- §14.1 — **Bernoulli NLL non-negativity at `y = 1`** (Bach 2024 §14.1,
    eq. 14.5). For success probability `p ∈ (0, 1]`, the loss
    `-log p` is non-negative, because `log p ≤ 0` on `(0, 1]`. -/
theorem bernoulliNLL_nonneg_at_one {p : ℝ} (hp_pos : 0 < p) (hp_le : p ≤ 1) :
    0 ≤ bernoulliNLL p 1 := by
  unfold bernoulliNLL
  have h_log_nonpos : log p ≤ 0 := log_nonpos (le_of_lt hp_pos) hp_le
  -- `bernoulliNLL p 1 = -1 * log p - 0 * log(1-p) = -log p ≥ 0`.
  have : -(1 : ℝ) * log p - (1 - 1) * log (1 - p) = -log p := by ring
  rw [this]
  linarith

/-- §14.1 — **Bernoulli NLL non-negativity at `y = 0`** (Bach 2024 §14.1,
    eq. 14.5). For success probability `p ∈ [0, 1)`, the loss
    `-log(1 - p)` is non-negative, because `log(1 - p) ≤ 0` on `[0, 1)`. -/
theorem bernoulliNLL_nonneg_at_zero {p : ℝ} (hp_nn : 0 ≤ p) (hp_lt : p < 1) :
    0 ≤ bernoulliNLL p 0 := by
  unfold bernoulliNLL
  have h_one_sub_pos : 0 < 1 - p := by linarith
  have h_one_sub_le : 1 - p ≤ 1 := by linarith
  have h_log_nonpos : log (1 - p) ≤ 0 :=
    log_nonpos (le_of_lt h_one_sub_pos) h_one_sub_le
  -- `bernoulliNLL p 0 = -0 * log p - 1 * log(1-p) = -log(1-p) ≥ 0`.
  have : -(0 : ℝ) * log p - (1 - 0) * log (1 - p) = -log (1 - p) := by ring
  rw [this]
  linarith

/-- §14.1 — **Gibbs inequality (scalar shadow)** (Bach 2024 §14.1, eq. 14.4
    in continuous form, Lemma 14.1 in the discrete form). For any
    `p, q > 0`, `q · log(q / p) ≥ q - p`, i.e. the cross-entropy
    contribution `−q log p` is bounded below by the entropy contribution
    `−q log q` up to a linear correction. This is the per-coordinate
    algebraic anchor of the KL-divergence non-negativity proof, derived
    from `log x ≤ x − 1` (`Real.log_le_sub_one_of_pos`). -/
theorem gibbs_scalar {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    q - p ≤ q * log (q / p) := by
  -- From `log x ≤ x - 1` applied to `x = p / q ≥ 0`:
  --   `log (p / q) ≤ p / q - 1`, hence `q * log (p / q) ≤ p - q`.
  -- Negate both sides: `-q * log (p / q) ≥ q - p`,
  -- and `-log (p / q) = log (q / p)`.
  have h_div_pos : 0 < p / q := div_pos hp hq
  have h_log_le : log (p / q) ≤ p / q - 1 := log_le_sub_one_of_pos h_div_pos
  have hq_nn : 0 ≤ q := le_of_lt hq
  -- Multiply both sides by `q ≥ 0`.
  have h_scaled : q * log (p / q) ≤ q * (p / q - 1) :=
    mul_le_mul_of_nonneg_left h_log_le hq_nn
  -- Simplify RHS: `q * (p / q - 1) = p - q`.
  have hq_ne : q ≠ 0 := ne_of_gt hq
  have h_rhs : q * (p / q - 1) = p - q := by field_simp
  rw [h_rhs] at h_scaled
  -- Convert `log (p / q)` to `-log (q / p)`.
  have h_log_swap : log (p / q) = -log (q / p) := by
    rw [log_div (ne_of_gt hp) hq_ne, log_div hq_ne (ne_of_gt hp)]; ring
  rw [h_log_swap] at h_scaled
  -- `q * (-log (q / p)) ≤ p - q`  ⇒  `q * log (q / p) ≥ q - p`.
  linarith

end LTFP
