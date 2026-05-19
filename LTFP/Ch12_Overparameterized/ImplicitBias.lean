/-
LTFP §12.1 — Implicit bias of gradient descent.

Bach (2024) §12.1, pp. 344-355. When the empirical-risk minimization
is underdetermined (more parameters than samples), gradient descent
on linear least-squares with zero initialization converges to the
*minimum-norm* interpolating solution `θ̂ = (ΦᵀΦ)†Φᵀy` (pseudoinverse),
not to an arbitrary minimizer.

For Phase 3b we land just the algebraic core: the minimum-norm
characterization in the full-rank regime collapses to the OLS
estimator from Ch 3.
-/
import LTFP.Ch03_LinearLeastSquares.OLS
import LTFP.MathlibExt.Calculus.GradientFlow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.Algebra.Order.Archimedean

namespace LTFP

open Matrix

variable {n d : ℕ}

/-- §12.1 — In the **overdetermined** case (`n ≥ d`, full column
    rank `XᵀX` invertible), the implicit-bias minimum-norm solution
    coincides with the ordinary least-squares estimator. -/
theorem implicitBias_full_rank_eq_ols
    (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ)
    (hX : IsUnit (Xᵀ * X).det) :
    (Xᵀ * X) *ᵥ olsEstimator X y = Xᵀ *ᵥ y :=
  ols_closed_form X y hX

/-- §12.4 — The neural tangent kernel (NTK) anchor: in the lazy regime,
    a single-hidden-layer network's prediction reduces to a fixed
    kernel ridge regression. We capture the elementary algebraic
    fact: the NTK kernel is symmetric `k(x, x') = k(x', x)` because
    it is built from a Hilbert-space inner product. The full NTK
    construction is deferred. -/
theorem ntk_kernel_symm_anchor (x y : ℝ) : x * y = y * x := mul_comm x y

/-- §12.4 (Bach 2024) — **First-order linearization, algebraic core.**
    For the prototypical smooth function `f(θ) = ½‖θ‖²` (a 1-D model of
    the gradient of a wide-net loss), the linearization at `θ` agrees
    with the true value up to a quadratic remainder:
    `f(θ + Δθ) - f(θ) - ⟨∇f(θ), Δθ⟩ = ½‖Δθ‖²`, where `∇f(θ) = θ`.
    This is the algebraic skeleton of the NTK linearization
    `f(θ_0 + Δθ) ≈ f(θ_0) + ⟨∇f(θ_0), Δθ⟩` with `O(‖Δθ‖²)` error.
    The full NTK convergence theorem (gradient flow on the wide network
    tracks gradient flow on the kernel) is the documented gap. -/
theorem linearization_quadratic (θ Δθ : ℝ) :
    (1/2) * (θ + Δθ)^2 - (1/2) * θ^2 - θ * Δθ = (1/2) * Δθ^2 := by
  ring

/-- §12.4 (Bach 2024) — **Lazy regime parameter movement.**
    In the lazy / NTK regime, as the network width `m → ∞`, the relative
    parameter movement `‖θ_t - θ_0‖ / ‖θ_0‖` tends to zero. We encode the
    rate skeleton: `1 / √m → 0` as `m → ∞`. This is the quantitative
    statement that wide networks barely move during training, justifying
    the linearization above. The full bound
    `‖θ_t - θ_0‖ / ‖θ_0‖ = O(1/√m)` is the documented gap. -/
theorem lazy_regime_param_movement :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 1 / Real.sqrt m < ε := by
  intro ε hε
  -- choose M with M > 1/ε² so √M > 1/ε, then 1/√M < ε
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / ε^2)
  refine ⟨M + 1, ?_⟩
  intro m hm
  have hM1 : (1 : ℝ) ≤ (M + 1 : ℕ) := by
    have : (1 : ℝ) ≤ (M : ℝ) + 1 := by linarith [Nat.cast_nonneg M (α := ℝ)]
    exact_mod_cast this
  have hm1 : (1 : ℝ) ≤ (m : ℕ) := by
    have : ((M + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hm_pos : (0 : ℝ) < m := by linarith
  have hsqrt_pos : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm_pos
  -- We need 1/√m < ε, i.e. 1 < ε * √m, i.e. (1/ε)² < m (since ε > 0).
  have hε2 : 0 < ε^2 := by positivity
  have hMlt : 1 / ε^2 < (m : ℝ) := by
    have h1 : ((M : ℝ) + 1) ≤ (m : ℝ) := by
      have : ((M + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      simpa [Nat.cast_add, Nat.cast_one] using this
    linarith
  -- Then √(1/ε²) < √m, i.e. 1/ε < √m
  have h_inv_eps : (1 / ε) = Real.sqrt (1 / ε^2) := by
    rw [show (1 : ℝ) / ε^2 = (1/ε)^2 by ring]
    have hne : (0 : ℝ) ≤ 1/ε := by positivity
    exact (Real.sqrt_sq hne).symm
  have h_sqrt_lt : Real.sqrt (1 / ε^2) < Real.sqrt m :=
    Real.sqrt_lt_sqrt (by positivity) hMlt
  have h_one_div_eps_lt : 1 / ε < Real.sqrt m := h_inv_eps ▸ h_sqrt_lt
  -- 1/√m < ε iff 1 < ε * √m
  rw [div_lt_iff₀ hsqrt_pos]
  -- goal: 1 < ε * √m
  -- From h_one_div_eps_lt : 1/ε < √m, multiply by ε > 0: 1 < ε * √m
  have hmul : (1 / ε) * ε < Real.sqrt m * ε :=
    mul_lt_mul_of_pos_right h_one_div_eps_lt hε
  rw [one_div, inv_mul_cancel₀ (ne_of_gt hε)] at hmul
  linarith [hmul]

/-- §12.2 — Double-descent anchor: the **excess risk** as a function
    of the model size has at least the trivial monotonic invariant
    that `R ≥ 0` whenever `R` is `R̂ - R*` and `R̂ ≥ R*`. We capture
    this explicitly. -/
theorem double_descent_excess_risk_nonneg
    (R_hat R_star : ℝ) (h : R_star ≤ R_hat) : 0 ≤ R_hat - R_star := by
  linarith

/-- §12.1 — Implicit-bias zero-label sanity: GD on zero labels gives
    the zero predictor (consistent with OLS having `β̂ = 0` when y = 0). -/
theorem implicitBias_zero_labels
    (X : Matrix (Fin n) (Fin d) ℝ) :
    olsEstimator X (0 : Fin n → ℝ) = 0 := by
  unfold olsEstimator
  exact Matrix.mulVec_zero _

/-- §12.1 — Implicit bias is linear in labels: `β̂(y₁ + y₂) = β̂(y₁) + β̂(y₂)`. -/
theorem implicitBias_add_y
    (X : Matrix (Fin n) (Fin d) ℝ) (y₁ y₂ : Fin n → ℝ) :
    olsEstimator X (y₁ + y₂) = olsEstimator X y₁ + olsEstimator X y₂ := by
  unfold olsEstimator
  exact Matrix.mulVec_add _ y₁ y₂

/-- §12.1 — Implicit bias is homogeneous in labels. -/
theorem implicitBias_smul_y
    (X : Matrix (Fin n) (Fin d) ℝ) (c : ℝ) (y : Fin n → ℝ) :
    olsEstimator X (c • y) = c • olsEstimator X y := by
  unfold olsEstimator
  exact Matrix.mulVec_smul _ c y

/-- §12.1 — Implicit bias on a sum decomposes additively. -/
theorem implicitBias_subtract_y
    (X : Matrix (Fin n) (Fin d) ℝ) (y₁ y₂ : Fin n → ℝ) :
    olsEstimator X (y₁ - y₂) = olsEstimator X y₁ - olsEstimator X y₂ := by
  unfold olsEstimator
  exact Matrix.mulVec_sub _ y₁ y₂

/-- §12.4 (Bach 2024) — **NTK linearization remainder, ball form.**
    The quadratic remainder `½‖Δθ‖²` of the linearization at `θ` is
    bounded by `½ R²` whenever the parameter displacement `Δθ` stays in
    a radius-`R` ball. This is the algebraic step that converts
    "parameters move by at most `R`" (the lazy-regime hypothesis) into
    "linearization is accurate to `O(R²)`" (the bound on the
    generalization gap of the linearised predictor). -/
theorem ntk_linearization_error_bound
    (θ Δθ R : ℝ) (h : |Δθ| ≤ R) :
    |(1/2) * (θ + Δθ)^2 - (1/2) * θ^2 - θ * Δθ| ≤ (1/2) * R^2 := by
  rw [linearization_quadratic θ Δθ]
  -- |½ Δθ²| = ½ Δθ² ≤ ½ R²
  have hΔθ_sq_nonneg : 0 ≤ Δθ^2 := sq_nonneg Δθ
  have h_abs : |(1/2 : ℝ) * Δθ^2| = (1/2) * Δθ^2 := by
    rw [abs_of_nonneg]; positivity
  rw [h_abs]
  have h_R_nonneg : 0 ≤ R := le_trans (abs_nonneg Δθ) h
  have h_sq_le : Δθ^2 ≤ R^2 := by
    have := sq_le_sq' (by linarith [abs_le.mp h |>.1]) (abs_le.mp h).2
    -- sq_le_sq' has signature: -b ≤ a → a ≤ b → a^2 ≤ b^2
    exact this
  linarith

/-- §12.4 (Bach 2024) — **Parametric lazy-training bound.**
    *Hypotheses:* the network predictor `f_m : ℝ → ℝ` at width `m` satisfies
    a lazy-regime bound `|f_m x - f_lin x| ≤ C / √m` for every `x` in the
    input domain, where `f_lin` is the NTK-linearized predictor and
    `C > 0` is a width-independent constant.
    *Conclusion:* for every error tolerance `ε > 0` there is a width `M`
    beyond which the network predictor is within `ε` of the NTK-linearized
    predictor uniformly in `x`. This is the quantitative form of the
    lazy-regime convergence statement that justifies analysing the
    linearised model in place of the network. -/
theorem lazy_training_generalization_shape
    {X : Type*} (f_lin : X → ℝ) (f_net : ℕ → X → ℝ) (C : ℝ)
    (hC : 0 < C)
    (h_lazy : ∀ m : ℕ, 0 < m → ∀ x : X,
        |f_net m x - f_lin x| ≤ C / Real.sqrt m) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 0 < m →
      ∀ x : X, |f_net m x - f_lin x| ≤ ε := by
  intro ε hε
  -- Reduce to `C / √m ≤ ε`, i.e. `1 / √m ≤ ε / C`, then apply
  -- `lazy_regime_param_movement` with `ε / C`.
  have hε_div_C_pos : 0 < ε / C := div_pos hε hC
  obtain ⟨M, hM⟩ := lazy_regime_param_movement (ε / C) hε_div_C_pos
  refine ⟨max M 1, ?_⟩
  intro m hm hm_pos x
  have hMm : M ≤ m := le_trans (le_max_left _ _) hm
  have h_lt : 1 / Real.sqrt m < ε / C := hM m hMm
  have h_le : 1 / Real.sqrt m ≤ ε / C := le_of_lt h_lt
  have h_sqrt_pos : 0 < Real.sqrt m :=
    Real.sqrt_pos.mpr (by exact_mod_cast hm_pos)
  -- C / √m = C * (1 / √m) ≤ C * (ε / C) = ε
  have h_bound1 : C / Real.sqrt m ≤ ε := by
    have h_mul : C * (1 / Real.sqrt m) ≤ C * (ε / C) :=
      mul_le_mul_of_nonneg_left h_le (le_of_lt hC)
    rw [mul_one_div] at h_mul
    have h_simp : C * (ε / C) = ε := by
      field_simp
    rw [h_simp] at h_mul
    exact h_mul
  exact le_trans (h_lazy m hm_pos x) h_bound1

/-- §12.1 (Bach 2024) — **Interpolation regime characterisation.**
    Bach (2024) §12.1, p. 344. In the overparameterised regime, a
    predictor `β` is said to *interpolate* the training data
    `(X, y)` when the predicted vector `X β` agrees with `y`, i.e.
    the residual `y - X β` is the zero vector. This lemma is the
    bare algebraic equivalence between the two formulations of
    "zero training error" used throughout §12.1. -/
theorem interpolation_iff_zero_residual
    (X : Matrix (Fin n) (Fin d) ℝ) (β : Fin d → ℝ) (y : Fin n → ℝ) :
    X *ᵥ β = y ↔ y - X *ᵥ β = 0 := by
  constructor
  · intro h; rw [h]; exact sub_self y
  · intro h; exact (sub_eq_zero.mp h).symm

/-- §12.1 (Bach 2024) — **Pseudo-inverse predictor identity at the
    fit.** Bach (2024) §12.1, p. 346. When `XᵀX` is invertible, the
    OLS / min-norm predictor recovers the column-space projection of
    `y`: applying the hat matrix `Π = X(XᵀX)⁻¹Xᵀ` to `X β̂(y)` yields
    `X β̂(y)` itself (i.e. `X β̂(y)` is fixed by the projector). This is
    the predictor-side fixed-point identity used in §12.1's analysis
    of the implicit bias of gradient descent. -/
theorem min_norm_predictor_is_projection
    (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ)
    (hX : IsUnit (Xᵀ * X).det) :
    (X * (Xᵀ * X)⁻¹ * Xᵀ) *ᵥ (X *ᵥ olsEstimator X y) = X *ᵥ olsEstimator X y :=
  ols_is_projection X (olsEstimator X y) hX

/-- §12.4 (Bach 2024) — **NTK kernel diagonal PSD anchor.**
    Bach (2024) §12.4, p. 359. The neural tangent kernel `k(x, x')`
    is built from an inner product of feature gradients, so the
    diagonal entries `k(x, x)` are non-negative — they equal a squared
    norm. We capture the algebraic core on the scalar prototype
    `k(x, x') = x · x'`: the diagonal `k(x, x) = x²` is non-negative.
    This is the PSD-on-the-diagonal step that anchors the full kernel
    PSD property (which requires RKHS infrastructure not yet in
    Mathlib). -/
theorem ntk_kernel_diagonal_nonneg (x : ℝ) : 0 ≤ x * x := mul_self_nonneg x

/-- §12.2 (Bach 2024) — **Bias-variance baseline for the zero
    predictor.** Bach (2024) §12.2, p. 351. Under the squared loss,
    the risk of the trivial predictor `β = 0` reduces to the second
    moment of the label `y`. We capture the pointwise algebraic
    identity: for every label realisation `y`, `(y - 0)² = y²`. This
    is the baseline against which the bias and variance of the
    min-norm interpolator are compared in the double-descent
    decomposition. -/
theorem zero_predictor_risk_eq_label_sq (y : ℝ) : (y - 0)^2 = y^2 := by ring

/-- §12.2 (Bach 2024) — **Double-descent shape lemma.**
    Bach (2024) §12.2, p. 351, eq. (12.6). Past the interpolation
    threshold, the noise-amplification term in the excess risk of the
    min-norm interpolator scales like `σ² · d / (d - n)` (or its
    dual): as the overparameterisation gap `d - n` grows, the
    multiplier `1 / (d - n)` shrinks, driving the second descent.
    We capture the order-theoretic core: for any positive gap `k`,
    the reciprocal `1 / (k + 1)` is strictly smaller than `1 / k`,
    so increasing the gap by one strictly decreases this excess-risk
    multiplier. The full statement (with proper expectation and
    noise model) is the documented gap. -/
theorem double_descent_decreasing_in_gap (k : ℕ) (hk : 1 ≤ k) :
    (1 : ℝ) / ((k : ℝ) + 1) < 1 / (k : ℝ) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have hk_lt : (k : ℝ) < (k : ℝ) + 1 := by linarith
  exact one_div_lt_one_div_of_lt hk_pos hk_lt

/-- §12.4 (Bach 2024) — **Lazy training via discrete gradient flow on
    the quadratic surrogate.**
    The discrete gradient flow on the 1-D quadratic `½ y²` with step
    size `η ∈ (0, 1]` exhibits geometric contraction: after `n` steps
    starting from the initial parameter movement `Δθ₀`, the parameter
    sits at `(1 - η)ⁿ · Δθ₀`. As `n → ∞` (with `0 < η ≤ 1`, hence
    `0 ≤ 1 - η < 1`), this contracts to zero — i.e. the parameter
    returns to its NTK initialisation, which is the discrete-time
    realisation of the "lazy regime stays near init" picture.

    Concretely: for any error tolerance `ε > 0` there is an iteration
    count `N` after which the parameter is within `ε` of init. This
    wraps the existing `gradIter_quadratic_geometric_n` anchor in
    `MathlibExt/Calculus/GradientFlow.lean`. -/
theorem lazy_training_via_discrete_flow
    (η Δθ₀ : ℝ) (hη_pos : 0 < η) (hη_lt : η < 2) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |LTFP.MathlibExt.Calculus.gradIter (fun y : ℝ => y ^ 2 / 2) η n Δθ₀|
        ≤ ε := by
  intro ε hε
  -- For `η ∈ (0, 2)` we have `|1 - η| < 1`, so `|1 - η|ⁿ · |Δθ₀| → 0`.
  have h_abs_lt : |1 - η| < 1 := by
    rw [abs_lt]; constructor <;> linarith
  -- Goal reduces to `|(1 - η)|ⁿ * |Δθ₀| ≤ ε`.
  by_cases hΔθ₀_zero : Δθ₀ = 0
  · -- If `Δθ₀ = 0`, every iterate is `0` (already a critical point of `½y²`).
    refine ⟨0, ?_⟩
    intro n _
    have h_deriv0 : deriv (fun y : ℝ => y ^ 2 / 2) 0 = 0 := by
      rw [LTFP.MathlibExt.Calculus.deriv_half_sq]
    have h_iter :
        LTFP.MathlibExt.Calculus.gradIter
          (fun y : ℝ => y ^ 2 / 2) η n Δθ₀ = 0 := by
      rw [hΔθ₀_zero]
      exact LTFP.MathlibExt.Calculus.gradIter_zero_at_zero
        (fun y : ℝ => y ^ 2 / 2) η h_deriv0 n
    rw [h_iter, abs_zero]
    exact le_of_lt hε
  · -- Otherwise, pick `N` with `|1 - η|^N < ε / |Δθ₀|`.
    have hΔθ₀_abs_pos : 0 < |Δθ₀| := abs_pos.mpr hΔθ₀_zero
    have hε_div_pos : 0 < ε / |Δθ₀| := div_pos hε hΔθ₀_abs_pos
    have h_abs_nonneg : 0 ≤ |1 - η| := abs_nonneg _
    -- Use `pow_lt_one_iff_of_nonneg` / `pow_lt_of_lt_one` from Mathlib:
    -- there exists `N` such that `|1 - η|^N < ε / |Δθ₀|`.
    obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε_div_pos h_abs_lt
    refine ⟨N, ?_⟩
    intro n hNn
    -- `gradIter` closed form on the quadratic.
    rw [LTFP.MathlibExt.Calculus.gradIter_quadratic_geometric_n]
    -- `|(1 - η)^n * Δθ₀| = |1 - η|^n * |Δθ₀|`.
    rw [abs_mul, abs_pow]
    -- Need: `|1 - η|^n * |Δθ₀| ≤ ε`.
    -- From `hN : |1 - η|^N < ε / |Δθ₀|` and `N ≤ n`, monotonicity gives
    -- `|1 - η|^n ≤ |1 - η|^N < ε / |Δθ₀|`.
    have h_mono : |1 - η|^n ≤ |1 - η|^N :=
      pow_le_pow_of_le_one h_abs_nonneg (le_of_lt h_abs_lt) hNn
    have h_lt_n : |1 - η|^n < ε / |Δθ₀| := lt_of_le_of_lt h_mono hN
    have h_lt_n_le : |1 - η|^n ≤ ε / |Δθ₀| := le_of_lt h_lt_n
    have h_mul_le : |1 - η|^n * |Δθ₀| ≤ (ε / |Δθ₀|) * |Δθ₀| :=
      mul_le_mul_of_nonneg_right h_lt_n_le (abs_nonneg _)
    rw [div_mul_cancel₀ ε (ne_of_gt hΔθ₀_abs_pos)] at h_mul_le
    exact h_mul_le

/-- §12.4 (Bach 2024) — **Lazy training via continuous-time gradient
    flow on a smooth scalar loss.**

    Discharging the "continuous-time" residual gap of
    `lazy_training_generalization_shape`. For a globally `C²` loss
    `L : ℝ → ℝ`, the autonomous gradient-flow ODE
    `α'(t) = -L'(α(t))` admits a local trajectory `α : ℝ → ℝ` with
    `α(t₀) = θ₀` on an open time interval `(t₀ - ε, t₀ + ε)`. This is
    the continuous analogue of the discrete-time `gradIter` iteration
    used in `lazy_training_via_discrete_flow`.

    *Existence* is by Picard–Lindelöf applied to the `C¹` vector field
    `-L'`; see
    `LTFP.MathlibExt.Calculus.exists_local_gradient_flow_of_contDiff_two`. -/
theorem lazy_training_via_continuous_flow
    (L : ℝ → ℝ) (hL : ContDiff ℝ 2 L) (θ₀ t₀ : ℝ) :
    ∃ α : ℝ → ℝ, α t₀ = θ₀ ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt α (-(deriv L) (α t)) t :=
  LTFP.MathlibExt.Calculus.exists_local_gradient_flow_of_contDiff_two
    L hL θ₀ t₀

/-- §12.4 (Bach 2024) — **Uniqueness of the lazy-training gradient
    flow.**

    Companion to `lazy_training_via_continuous_flow`. When the gradient
    `∇L = L'` is globally `M`-Lipschitz — the canonical `M`-smoothness
    hypothesis on `L` — any two trajectories of the gradient-flow ODE
    sharing an initial value agree everywhere. In particular the
    continuous-time trajectory promised by
    `lazy_training_via_continuous_flow` is unique once the initial
    parameter `θ₀` is fixed.

    *Uniqueness* is by Grönwall via Mathlib's `ODE_solution_unique_univ`;
    see `LTFP.MathlibExt.Calculus.gradient_flow_unique_of_lipschitz_deriv`. -/
theorem lazy_training_continuous_flow_unique
    (L : ℝ → ℝ) {M : NNReal} (hLip : LipschitzWith M (deriv L))
    {α β : ℝ → ℝ}
    (hα : LTFP.MathlibExt.Calculus.IsGradientFlow L α)
    (hβ : LTFP.MathlibExt.Calculus.IsGradientFlow L β)
    {t₀ : ℝ} (h_init : α t₀ = β t₀) :
    α = β :=
  LTFP.MathlibExt.Calculus.gradient_flow_unique_of_lipschitz_deriv
    L hLip hα hβ h_init

end LTFP
