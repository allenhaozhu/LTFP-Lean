/-
LTFP §6.3 — Generic simplest consistency analysis.

Bach (2024) §6.3, pp. 163-172. Local-averaging estimators are
*consistent* (their excess risk tends to zero as `n → ∞`) under mild
assumptions on the weight scheme: the weights should concentrate
near the query point as `n` grows ("locality") while still averaging
enough samples to reduce noise ("averaging").

For Phase 3b we land just the **deterministic algebraic core**:
the excess-risk identity for a single deterministic predictor under
mean-zero noise — same template as the §3.5 OLS bias-variance core.
The full probabilistic consistency is left for a Phase-4 wave.
-/
import LTFP.Ch06_LocalAveraging.Estimators

namespace LTFP

variable {𝒳 : Type*} {n : ℕ}

/-- §6.3 — Pointwise excess decomposition: at any query `x`, the
    deviation of `f̂(x)` from the regression function `f*(x)` splits
    into a deterministic *bias* (using fstar = E[Y|X=x] for the noise-free
    label) plus a random *noise* term `f̂(x) − f̂_clean(x)`.  This file
    captures the bias side: the local-average of the regression function
    `fstar` evaluated at the training inputs. -/
noncomputable def localAvgBiasTerm
    (fstar : 𝒳 → ℝ) (xs : Fin n → 𝒳) (w : LocalWeights 𝒳 n) (x : 𝒳) : ℝ :=
  ∑ i, w x i * fstar (xs i) - fstar x

/-- §6.3 sanity lemma: when the weights at `x` sum to one and the
    regression function `fstar` is constant, the bias term is zero. -/
theorem localAvgBiasTerm_const_zero
    (c : ℝ) (xs : Fin n → 𝒳) (w : LocalWeights 𝒳 n) (x : 𝒳)
    (hsum : ∑ i, w x i = 1) :
    localAvgBiasTerm (fun _ => c) xs w x = 0 := by
  unfold localAvgBiasTerm
  simp only [mul_comm _ c]
  rw [← Finset.mul_sum, hsum, mul_one]
  ring

/-- §6.3 — When `fstar = 0` the bias term reduces to `−fstar x = 0`. -/
theorem localAvgBiasTerm_zero_fstar
    (xs : Fin n → 𝒳) (w : LocalWeights 𝒳 n) (x : 𝒳) :
    localAvgBiasTerm (fun _ => (0 : ℝ)) xs w x = 0 := by
  unfold localAvgBiasTerm
  simp

end LTFP
