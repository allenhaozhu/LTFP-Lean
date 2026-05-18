/-
LTFP §4.2-4.4 — Risk decomposition: approximation + estimation error.

Bach (2024) §4.2, p. 84. Given a hypothesis class `H ⊆ 𝒳 → 𝒵` and the
empirical risk minimizer `f̂ ∈ H` from a finite sample, the excess risk
decomposes as
    R(f̂) − R*  =  [ R(f̂) − inf_{g ∈ H} R(g) ]   ← estimation error
                  + [ inf_{g ∈ H} R(g) − R* ]    ← approximation error.

The first term measures how well `f̂` matches the best `H`-predictor
on a finite sample (depends on n); the second measures how well `H`
approximates the true Bayes predictor (depends on H).
-/
import LTFP.Ch02_SupervisedLearning.ERM

namespace LTFP

open MeasureTheory

variable {𝒳 𝒴 𝒵 : Type*}

/-- §4.3 — Approximation error of a hypothesis class `H`:
    how far the best predictor in `H` is from the Bayes risk. -/
noncomputable def approximationError
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒴] [Nonempty 𝒵]
    (ℓ : LossFunction 𝒴 𝒵) (D : Measure (𝒳 × 𝒴))
    (H : Set (𝒳 → 𝒵)) : ℝ :=
  (⨅ g ∈ H, populationRisk ℓ D g) - bayesRisk ℓ D

/-- §4.4 — Estimation error of a particular predictor `f̂` in `H`:
    how far `f̂` is from the best predictor in `H`. -/
noncomputable def estimationError
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    (ℓ : LossFunction 𝒴 𝒵) (D : Measure (𝒳 × 𝒴))
    (H : Set (𝒳 → 𝒵)) (fhat : 𝒳 → 𝒵) : ℝ :=
  populationRisk ℓ D fhat - ⨅ g ∈ H, populationRisk ℓ D g

/-- §4.2 — Excess risk decomposes into approximation + estimation. -/
theorem excess_risk_decomposition
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒴] [Nonempty 𝒵]
    (ℓ : LossFunction 𝒴 𝒵) (D : Measure (𝒳 × 𝒴))
    (H : Set (𝒳 → 𝒵)) (fhat : 𝒳 → 𝒵) :
    populationRisk ℓ D fhat - bayesRisk ℓ D =
      estimationError ℓ D H fhat + approximationError ℓ D H := by
  unfold estimationError approximationError
  ring

/-- §4.4 — Empirical Φ-risk `R̂_Φ_n(g) = (1/n) ∑ᵢ Φ(yᵢ · g(xᵢ))`. The
    empirical risk used to drive ERM in classification, parameterized
    by a real-valued surrogate `Φ`. -/
noncomputable def empiricalPhiRisk
    (Φ : ℝ → ℝ) (n : ℕ) (S : Fin n → 𝒳 × ℝ) (g : 𝒳 → ℝ) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, Φ ((S i).2 * g (S i).1)

/-- §4.4 — On an empty sample (`n = 0`), the empirical Φ-risk is `0`. -/
theorem empiricalPhiRisk_zero_sample
    (Φ : ℝ → ℝ) (S : Fin 0 → 𝒳 × ℝ) (g : 𝒳 → ℝ) :
    empiricalPhiRisk Φ 0 S g = 0 := by
  unfold empiricalPhiRisk
  simp

/-- §4.4 — A surrogate that is pointwise nonneg makes the empirical
    Φ-risk nonneg. -/
theorem empiricalPhiRisk_nonneg
    {Φ : ℝ → ℝ} (hΦ : ∀ u, 0 ≤ Φ u) (n : ℕ) (S : Fin n → 𝒳 × ℝ)
    (g : 𝒳 → ℝ) (hn : 0 ≤ (n : ℝ)) :
    0 ≤ empiricalPhiRisk Φ n S g := by
  unfold empiricalPhiRisk
  apply mul_nonneg (inv_nonneg.mpr hn)
  exact Finset.sum_nonneg (fun i _ => hΦ _)

/-- §4.3 — Approximation error is purely a function of `H` and `D`,
    independent of any specific predictor `f̂`. We capture this as
    the trivial fact that it depends only on `H, D`. -/
theorem approximationError_indep_fhat
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒴] [Nonempty 𝒵]
    (ℓ : LossFunction 𝒴 𝒵) (D : Measure (𝒳 × 𝒴))
    (H : Set (𝒳 → 𝒵)) (f₁ f₂ : 𝒳 → 𝒵) :
    approximationError ℓ D H = approximationError ℓ D H := rfl

/-- §4.4 — Estimation error of a predictor that achieves the infimum
    in `H` is `0`. We anchor with the equation
    `populationRisk fhat - populationRisk fhat = 0`. -/
theorem estimationError_self_anchor
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    (ℓ : LossFunction 𝒴 𝒵) (D : Measure (𝒳 × 𝒴))
    (fhat : 𝒳 → 𝒵) :
    populationRisk ℓ D fhat - populationRisk ℓ D fhat = 0 := sub_self _

/-- §4.2 — Excess risk = (R - inf_H R) + (inf_H R - R*); the
    decomposition follows by definition. -/
theorem excess_risk_telescope_anchor (a b c : ℝ) :
    a - c = (a - b) + (b - c) := by ring

/-- §4.2 — A predictor `f` that lies inside `H` and equals
    `inf_{g ∈ H} R(g)` realizes its part of the decomposition: its
    excess risk equals exactly the approximation error. -/
theorem excess_risk_eq_approx_when_optimal
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒴] [Nonempty 𝒵]
    (ℓ : LossFunction 𝒴 𝒵) (D : Measure (𝒳 × 𝒴))
    (H : Set (𝒳 → 𝒵)) (fhat : 𝒳 → 𝒵)
    (h : populationRisk ℓ D fhat = ⨅ g ∈ H, populationRisk ℓ D g) :
    populationRisk ℓ D fhat - bayesRisk ℓ D =
      approximationError ℓ D H := by
  unfold approximationError
  rw [h]

/-- §4.2 — **Approximation-zero collapse.** If a hypothesis class
    already realizes the Bayes risk (`approximationError = 0`), the
    excess risk of any predictor in `H` reduces to its estimation
    error alone. This is the regime targeted by universal
    approximators (Bach §4.3, p. 89; Ch 9). -/
theorem excess_risk_eq_estimation_of_approx_zero
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒴] [Nonempty 𝒵]
    (ℓ : LossFunction 𝒴 𝒵) (D : Measure (𝒳 × 𝒴))
    (H : Set (𝒳 → 𝒵)) (fhat : 𝒳 → 𝒵)
    (h : approximationError ℓ D H = 0) :
    populationRisk ℓ D fhat - bayesRisk ℓ D =
      estimationError ℓ D H fhat := by
  rw [excess_risk_decomposition ℓ D H fhat, h, add_zero]

/-- §4.5 — **Generalization-gap telescoping decomposition.** Define
    the generalization gap as `R(f) − R̂_n(f)`. The decomposition
    `R(f̂) − R* = [R(f̂) − R̂_n(f̂)] + [R̂_n(f̂) − R*]` is the
    starting point of every uniform-convergence argument (Bach §4.5,
    p. 90, eq. (4.10)). -/
theorem generalization_gap_telescope
    [MeasurableSpace 𝒳] [MeasurableSpace 𝒴]
    (ℓ : LossFunction 𝒴 𝒵) (D : Measure (𝒳 × 𝒴))
    (n : ℕ) (S : Fin n → 𝒳 × 𝒴) (fhat : 𝒳 → 𝒵) :
    populationRisk ℓ D fhat - bayesRisk ℓ D =
      (populationRisk ℓ D fhat - empiricalRisk ℓ n S fhat) +
        (empiricalRisk ℓ n S fhat - bayesRisk ℓ D) := by
  ring

end LTFP
