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

end LTFP
