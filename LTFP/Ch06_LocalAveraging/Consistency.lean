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

/-- §6.3 — Lipschitz-locality bias bound (Bach §6.3 consistency first step).

If the weights at `x` are nonnegative, sum to `1`, and the support is
contained in the ball of radius `r` around `x` (i.e. `w x i ≠ 0` forces
`dist (xs i) x ≤ r`), then for any `L`-Lipschitz regression function
`fstar` the bias term is bounded in absolute value by `L · r`. This is
the deterministic locality estimate that drives the consistency proof:
as the weight-support radius shrinks, the bias vanishes. -/
theorem localAvgBiasTerm_abs_le_of_lipschitz_local
    [PseudoMetricSpace 𝒳] (fstar : 𝒳 → ℝ) (xs : Fin n → 𝒳)
    (w : LocalWeights 𝒳 n) (x : 𝒳) (L : NNReal) (r : ℝ) (_hr : 0 ≤ r)
    (hLip : LipschitzWith L fstar)
    (hw : ∀ i, 0 ≤ w x i) (hsum : ∑ i, w x i = 1)
    (hlocal : ∀ i, w x i ≠ 0 → dist (xs i) x ≤ r) :
    |localAvgBiasTerm fstar xs w x| ≤ (L : ℝ) * r := by
  have hbias :
      localAvgBiasTerm fstar xs w x =
        ∑ i, w x i * (fstar (xs i) - fstar x) := by
    unfold localAvgBiasTerm
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  rw [hbias]
  calc
    |∑ i, w x i * (fstar (xs i) - fstar x)|
        ≤ ∑ i, |w x i * (fstar (xs i) - fstar x)| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, w x i * |fstar (xs i) - fstar x| := by
          apply Finset.sum_congr rfl
          intro i _
          rw [abs_mul, abs_of_nonneg (hw i)]
    _ ≤ ∑ i, w x i * ((L : ℝ) * r) := by
          apply Finset.sum_le_sum
          intro i _
          by_cases hi : w x i = 0
          · simp [hi]
          · apply mul_le_mul_of_nonneg_left _ (hw i)
            calc
              |fstar (xs i) - fstar x|
                  = dist (fstar (xs i)) (fstar x) := by rw [Real.dist_eq]
              _ ≤ (L : ℝ) * dist (xs i) x := hLip.dist_le_mul _ _
              _ ≤ (L : ℝ) * r :=
                  mul_le_mul_of_nonneg_left (hlocal i hi) L.coe_nonneg
    _ = (L : ℝ) * r := by rw [← Finset.sum_mul, hsum, one_mul]

end LTFP
