/-
LTFP §7.4 — Kernel algorithms.

Bach (2024) §7.4, pp. 196-202. Kernel ridge regression solves
`α̂ = (K + nλI)⁻¹ y` where `K ∈ ℝⁿˣⁿ` is the Gram matrix
`Kᵢⱼ = k(xᵢ, xⱼ)` and `y ∈ ℝⁿ` are the labels. The predicted score
at a new query is `f̂(x) = ∑ᵢ α̂ᵢ k(x, xᵢ)` (representer-theorem form).
-/
import LTFP.Ch07_Kernels.Representer
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace LTFP

variable {𝒳 : Type*} {n : ℕ}

/-- §7.4 — Gram matrix `Kᵢⱼ = k(xᵢ, xⱼ)` of a kernel `k` on a sample. -/
def gramMatrix (k : 𝒳 → 𝒳 → ℝ) (xs : Fin n → 𝒳) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => k (xs i) (xs j)

/-- §7.4 — Kernel ridge regression coefficient vector
    `α̂_λ = (K + nλI)⁻¹ y`. -/
noncomputable def krrCoeffs
    (k : 𝒳 → 𝒳 → ℝ) (xs : Fin n → 𝒳) (y : Fin n → ℝ) (lam : ℝ) :
    Fin n → ℝ :=
  ((gramMatrix k xs + (n * lam) • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹).mulVec y

/-- §7.4 — KRR predictor: kernel expansion with the coefficients above. -/
noncomputable def krrPredictor
    (k : 𝒳 → 𝒳 → ℝ) (xs : Fin n → 𝒳) (y : Fin n → ℝ) (lam : ℝ) (x : 𝒳) :
    ℝ :=
  kernelExpansion k xs (krrCoeffs k xs y lam) x

/-- §7.4 sanity lemma: KRR with zero labels gives the zero predictor. -/
theorem krrPredictor_zero_labels
    (k : 𝒳 → 𝒳 → ℝ) (xs : Fin n → 𝒳) (lam : ℝ) (x : 𝒳) :
    krrPredictor k xs (0 : Fin n → ℝ) lam x = 0 := by
  unfold krrPredictor krrCoeffs
  rw [Matrix.mulVec_zero]
  exact kernelExpansion_zero _ _ _

/-- §7.4.6 — Kernelization-of-linear-algorithms identity: a kernel
    expansion is linear in its coefficients (key fact behind the
    representer theorem and dual algorithms). -/
theorem kernelExpansion_add
    (k : 𝒳 → 𝒳 → ℝ) (xs : Fin n → 𝒳) (α β : Fin n → ℝ) (x : 𝒳) :
    kernelExpansion k xs (α + β) x =
      kernelExpansion k xs α x + kernelExpansion k xs β x := by
  simp only [kernelExpansion, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- §7.4 — KRR with the zero kernel is the zero predictor everywhere. -/
theorem krrPredictor_zero_kernel
    (xs : Fin n → 𝒳) (y : Fin n → ℝ) (lam : ℝ) (x : 𝒳) :
    krrPredictor (fun _ _ : 𝒳 => (0 : ℝ)) xs y lam x = 0 := by
  unfold krrPredictor kernelExpansion
  simp

/-- §7.4 — Gram matrix is diagonal-symmetric for any kernel:
    `K i i = k(xᵢ, xᵢ)`. -/
theorem gramMatrix_diag (k : 𝒳 → 𝒳 → ℝ) (xs : Fin n → 𝒳) (i : Fin n) :
    gramMatrix k xs i i = k (xs i) (xs i) := rfl

/-- §7.4 — Off-diagonal Gram entries: `K i j = k(xᵢ, xⱼ)`. -/
theorem gramMatrix_eq_kernel (k : 𝒳 → 𝒳 → ℝ) (xs : Fin n → 𝒳) (i j : Fin n) :
    gramMatrix k xs i j = k (xs i) (xs j) := rfl

/-- §7.4 — Gram matrix of zero kernel is zero matrix. -/
theorem gramMatrix_zero (xs : Fin n → 𝒳) :
    gramMatrix (fun _ _ : 𝒳 => (0 : ℝ)) xs = 0 := by
  unfold gramMatrix
  ext i j
  simp

/-- §7.4 — Gram matrix is symmetric for symmetric kernels. -/
theorem gramMatrix_symm_of_symm_kernel
    (k : 𝒳 → 𝒳 → ℝ) (hk : ∀ x y, k x y = k y x)
    (xs : Fin n → 𝒳) (i j : Fin n) :
    gramMatrix k xs i j = gramMatrix k xs j i := by
  unfold gramMatrix
  simp [Matrix.of_apply, hk]

/-- §7.4 — KRR coefficient is linear in labels. -/
theorem krrCoeffs_add_y
    (k : 𝒳 → 𝒳 → ℝ) (xs : Fin n → 𝒳) (y₁ y₂ : Fin n → ℝ) (lam : ℝ) :
    krrCoeffs k xs (y₁ + y₂) lam =
      krrCoeffs k xs y₁ lam + krrCoeffs k xs y₂ lam := by
  unfold krrCoeffs
  exact Matrix.mulVec_add _ y₁ y₂

/-- §7.4 — KRR coefficient is homogeneous in labels. -/
theorem krrCoeffs_smul_y
    (k : 𝒳 → 𝒳 → ℝ) (xs : Fin n → 𝒳) (c : ℝ) (y : Fin n → ℝ) (lam : ℝ) :
    krrCoeffs k xs (c • y) lam = c • krrCoeffs k xs y lam := by
  unfold krrCoeffs
  exact Matrix.mulVec_smul _ c y

/-- §7.4 — KRR coefficient with zero labels is zero. -/
theorem krrCoeffs_zero_labels
    (k : 𝒳 → 𝒳 → ℝ) (xs : Fin n → 𝒳) (lam : ℝ) :
    krrCoeffs k xs (0 : Fin n → ℝ) lam = 0 := by
  unfold krrCoeffs
  exact Matrix.mulVec_zero _

/-- §7.4 — KRR predictor is linear in labels. -/
theorem krrPredictor_add_y
    (k : 𝒳 → 𝒳 → ℝ) (xs : Fin n → 𝒳) (y₁ y₂ : Fin n → ℝ) (lam : ℝ) (x : 𝒳) :
    krrPredictor k xs (y₁ + y₂) lam x =
      krrPredictor k xs y₁ lam x + krrPredictor k xs y₂ lam x := by
  unfold krrPredictor
  rw [krrCoeffs_add_y, kernelExpansion_add]

end LTFP
