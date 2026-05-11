/-
LTFP foundation: positive-definite kernels.

Phase-3a anchor for Ch 7 (kernel methods), Ch 9 (NN-RKHS connection),
and Ch 12 (NTK regime). A kernel `k : 𝒳 × 𝒳 → ℝ` is positive
semidefinite when, for any finite sample, its Gram matrix is PSD.

We re-export Mathlib's `Matrix.PosSemidef` machinery and add the
LTFP-namespace predicate `IsPSDKernel`.
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Real.StarOrdered

namespace LTFP

variable {𝒳 : Type*}

/-- A real-valued kernel `k : 𝒳 → 𝒳 → ℝ` is **positive semidefinite**
    when the Gram matrix `[k(xᵢ, xⱼ)]` is PSD for every finite sample. -/
def IsPSDKernel (k : 𝒳 → 𝒳 → ℝ) : Prop :=
  ∀ {n : ℕ} (xs : Fin n → 𝒳),
    (Matrix.of fun i j => k (xs i) (xs j)).PosSemidef

/-- §F4a sanity lemma: the constant-zero kernel is PSD.
    The zero matrix is positive semidefinite (one-liner). -/
theorem isPSDKernel_zero : IsPSDKernel (fun _ _ : 𝒳 => (0 : ℝ)) := by
  intro n xs
  have : (Matrix.of fun _ _ : Fin n => (0 : ℝ)) = 0 := by
    ext i j; simp
  rw [this]
  exact Matrix.PosSemidef.zero

/-- §F4a — Linear kernel `k(x, y) = ⟨x, y⟩` on real vectors.  -/
def linearKernel {d : ℕ} : (Fin d → ℝ) → (Fin d → ℝ) → ℝ :=
  fun x y => ∑ i, x i * y i

/-- §F4a — The linear kernel is symmetric. -/
theorem linearKernel_symm {d : ℕ} (x y : Fin d → ℝ) :
    linearKernel x y = linearKernel y x := by
  unfold linearKernel
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- §F4a — The linear kernel of `x` with itself is the squared Euclidean
    norm `‖x‖² = ∑ᵢ x i²`. -/
theorem linearKernel_self {d : ℕ} (x : Fin d → ℝ) :
    linearKernel x x = ∑ i, (x i)^2 := by
  unfold linearKernel
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- §F4a — Linear kernel with zero left argument is zero. -/
theorem linearKernel_zero_left {d : ℕ} (y : Fin d → ℝ) :
    linearKernel (0 : Fin d → ℝ) y = 0 := by
  unfold linearKernel
  simp

/-- §F4a — Linear kernel of x with itself is nonneg. -/
theorem linearKernel_self_nonneg {d : ℕ} (x : Fin d → ℝ) :
    0 ≤ linearKernel x x := by
  rw [linearKernel_self]
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- §F4a — Linear kernel with zero right argument is zero. -/
theorem linearKernel_zero_right {d : ℕ} (x : Fin d → ℝ) :
    linearKernel x (0 : Fin d → ℝ) = 0 := by
  unfold linearKernel
  simp

/-- §F4a — Linear kernel is bilinear in left argument (additivity). -/
theorem linearKernel_add_left {d : ℕ} (x₁ x₂ y : Fin d → ℝ) :
    linearKernel (x₁ + x₂) y = linearKernel x₁ y + linearKernel x₂ y := by
  unfold linearKernel
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  show (x₁ + x₂) i * y i = x₁ i * y i + x₂ i * y i
  rw [Pi.add_apply]; ring

/-- §F4a — Linear kernel is bilinear in right argument (additivity). -/
theorem linearKernel_add_right {d : ℕ} (x y₁ y₂ : Fin d → ℝ) :
    linearKernel x (y₁ + y₂) = linearKernel x y₁ + linearKernel x y₂ := by
  unfold linearKernel
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  show x i * (y₁ + y₂) i = x i * y₁ i + x i * y₂ i
  rw [Pi.add_apply]; ring

end LTFP
