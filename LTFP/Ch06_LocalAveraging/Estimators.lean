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

/-- §6.2 — Zero weights yield the zero predictor: a vacuous boundary
    case used implicitly in bias-variance decompositions (the
    "predict-zero" reference estimator). Bach (2024) §6.2, p. 158. -/
theorem localAvg_zero_weights (Y : Fin n → ℝ) (x : 𝒳) :
    localAvg Y (fun _ _ => (0 : ℝ)) x = 0 := by
  unfold localAvg
  simp

/-- §6.2.2 — A training point `xᵢ` always lies in its own partition
    cell, so the unnormalized partition weight evaluated at `xᵢ` and
    index `i` equals one. This is the "self-membership" identity used
    when proving partition estimators interpolate training inputs
    of singleton cells. Bach (2024) §6.2, p. 160 (histogram rule). -/
theorem partitionWeights_self (P : 𝒳 → ℕ) (xs : Fin n → 𝒳) (i : Fin n) :
    partitionWeights P xs (xs i) i = 1 := by
  unfold partitionWeights
  simp

/-- §6.2.2 — Partition weights are bounded above by `1`: useful when
    deriving uniform variance bounds for histogram-style estimators.
    Bach (2024) §6.2, p. 160. -/
theorem partitionWeights_le_one
    (P : 𝒳 → ℕ) (xs : Fin n → 𝒳) (x : 𝒳) (i : Fin n) :
    partitionWeights P xs x i ≤ 1 := by
  unfold partitionWeights
  split_ifs with h
  · exact le_refl 1
  · exact zero_le_one

/-- §6.2.3 — Nearest-neighbour weights sum to one at every query.
    This is the "convex-combination" property: 1-NN is itself a valid
    local-averaging predictor with normalized weights, a prerequisite
    for the consistency analysis. Bach (2024) §6.2, p. 161. -/
theorem nnWeights_sum_one (witness : 𝒳 → Fin n) (x : 𝒳) :
    ∑ i, nnWeights witness x i = 1 := by
  unfold nnWeights
  rw [Finset.sum_eq_single (witness x)]
  · simp
  · intro i _ hi
    rw [if_neg (fun h => hi h.symm)]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- §6.2 — If the weights at `x` are nonnegative and sum to one, the
    local-averaging predictor is bounded above by the maximum label.
    Together with `localAvg_const_of_sum_one`, this is the standard
    "no-extrapolation" property of convex-combination predictors
    (k-NN, Nadaraya-Watson, partition estimators). Bach (2024) §6.2,
    p. 159. -/
theorem localAvg_le_max
    (Y : Fin n → ℝ) (w : LocalWeights 𝒳 n) (x : 𝒳)
    (M : ℝ) (hY : ∀ i, Y i ≤ M)
    (hw : ∀ i, 0 ≤ w x i) (hsum : ∑ i, w x i = 1) :
    localAvg Y w x ≤ M := by
  unfold localAvg
  have hbound : ∑ i, w x i * Y i ≤ ∑ i, w x i * M := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hY i) (hw i)
  calc ∑ i, w x i * Y i
      ≤ ∑ i, w x i * M := hbound
    _ = (∑ i, w x i) * M := by rw [Finset.sum_mul]
    _ = 1 * M := by rw [hsum]
    _ = M := one_mul M

end LTFP
