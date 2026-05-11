/-
LTFP §2.3.1 — Local averaging predictors.

Bach (2024) §2.3.1, p. 31. A *local averaging* predictor at point `x`
returns a weighted sum (or argmax) of the training labels `y₁ … yₙ`,
where the weights `wᵢ(x)` depend on `x` and the training inputs but
are typically nonnegative and sum to one. Special cases include
k-nearest-neighbours, partition (histogram) predictors, and the
Nadaraya–Watson kernel estimator.

This file defines the abstract weight-then-average shape and a
soundness lemma; concrete weight schemes (kNN, partition, kernel)
sit in later wave files.
-/
import LTFP.Ch02_SupervisedLearning.Defs

namespace LTFP

variable {𝒳 : Type*} {n : ℕ}

/-- A local-averaging *weight function* assigns to each query point
    `x : 𝒳` a vector of `n` real weights over the training inputs. -/
abbrev LocalWeights (𝒳 : Type*) (n : ℕ) : Type _ := 𝒳 → Fin n → ℝ

/-- §2.3.1 — Local averaging predictor: `f̂(x) = ∑ᵢ wᵢ(x) · yᵢ`.

    Given training labels `Y : Fin n → ℝ` and a weight function
    `w : LocalWeights 𝒳 n`, returns the prediction at any query `x`. -/
def localAvg (Y : Fin n → ℝ) (w : LocalWeights 𝒳 n) : 𝒳 → ℝ :=
  fun x => ∑ i, w x i * Y i

/-- If the weights at `x` sum to one and one label is constant `c`,
    the local average at `x` equals `c`. A first sanity check. -/
lemma localAvg_const_of_sum_one (c : ℝ) (w : LocalWeights 𝒳 n)
    (x : 𝒳) (hsum : ∑ i, w x i = 1) :
    localAvg (fun _ => c) w x = c := by
  unfold localAvg
  simp only [mul_comm _ c]
  rw [← Finset.mul_sum]
  rw [hsum, mul_one]

end LTFP
