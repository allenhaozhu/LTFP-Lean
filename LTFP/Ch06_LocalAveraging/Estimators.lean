/-
LTFP §6.2 — Local averaging estimators.

Bach (2024) §6.2, pp. 157-162. A *local averaging* predictor at a query
point `x ∈ 𝒳` returns a weighted sum `f̂(x) = ∑ᵢ wᵢ(x) yᵢ` of the
training labels, where the weights `wᵢ(x)` depend on `x` and the
training inputs.

This file collects three classical instantiations:
- Linear estimators (any `wᵢ(x)` linear in `x`),
- Partition estimators (`wᵢ(x)` constant on each cell of a fixed
  partition of `𝒳`),
- Kernel-regression / Nadaraya-Watson estimators (`wᵢ(x) = K(x − xᵢ)
  / ∑ⱼ K(x − xⱼ)` for a kernel `K`).

We extend Ch 2's `localAvg` skeleton with a simple uniform-weights
specialization and a sanity lemma.
-/
import LTFP.Ch02_SupervisedLearning.LocalAveraging

namespace LTFP

variable {𝒳 : Type*} {n : ℕ}

/-- §6.2.1 — Uniform local-averaging weights: every training point
    contributes equally to every query.  `wᵢ(x) = 1/n` for all `i, x`. -/
noncomputable def uniformWeights (n : ℕ) : LocalWeights 𝒳 n :=
  fun _ _ => (n : ℝ)⁻¹

/-- §6.2.1 — The uniform-weights local average is the empirical mean
    of the training labels (independent of `x`). -/
theorem uniformWeights_localAvg_eq_mean (Y : Fin n → ℝ) (x : 𝒳) :
    localAvg Y (uniformWeights n) x = (n : ℝ)⁻¹ * ∑ i, Y i := by
  unfold localAvg uniformWeights
  rw [← Finset.mul_sum]

/-- §6.2.2 — Partition-based weights: the weight `wᵢ(x)` is `1` if
    `xᵢ` lies in the same cell of a partition `P : 𝒳 → ℕ` as the query
    `x`, and `0` otherwise (unnormalized form).  This is the
    histogram-style estimator before normalization. -/
def partitionWeights (P : 𝒳 → ℕ) (xs : Fin n → 𝒳) : LocalWeights 𝒳 n :=
  fun x i => if P x = P (xs i) then 1 else 0

/-- §6.2.3 — Nearest-neighbour indicator weights (1-NN special case):
    `wᵢ(x) = 1` if the function `dist : 𝒳 × 𝒳 → ℝ` returns its minimum
    among the training points at index `i`, `0` otherwise.  We
    parameterize directly by the witness index for cleanliness. -/
def nnWeights (witness : 𝒳 → Fin n) : LocalWeights 𝒳 n :=
  fun x i => if witness x = i then 1 else 0

/-- §6.2.3 — At any query `x`, the 1-NN local average evaluates to the
    label at the witness index. -/
theorem nnWeights_localAvg
    (Y : Fin n → ℝ) (witness : 𝒳 → Fin n) (x : 𝒳) :
    localAvg Y (nnWeights witness) x = Y (witness x) := by
  unfold localAvg nnWeights
  simp [Finset.sum_ite_eq']

/-- §6.2 — `localAvg` is linear in the labels Y. -/
theorem localAvg_add_Y (Y₁ Y₂ : Fin n → ℝ) (w : LocalWeights 𝒳 n) (x : 𝒳) :
    localAvg (Y₁ + Y₂) w x = localAvg Y₁ w x + localAvg Y₂ w x := by
  simp only [localAvg, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- §6.2 — `localAvg` is homogeneous in the labels. -/
theorem localAvg_smul_Y (c : ℝ) (Y : Fin n → ℝ)
    (w : LocalWeights 𝒳 n) (x : 𝒳) :
    localAvg (c • Y) w x = c * localAvg Y w x := by
  unfold localAvg
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  show w x i * (c * Y i) = c * (w x i * Y i)
  ring

/-- §6.2 — Negation of labels: `localAvg (-Y) = -localAvg Y`. -/
theorem localAvg_neg_Y (Y : Fin n → ℝ) (w : LocalWeights 𝒳 n) (x : 𝒳) :
    localAvg (-Y) w x = -(localAvg Y w x) := by
  unfold localAvg
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  show w x i * (-Y i) = -(w x i * Y i)
  ring

end LTFP
