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

/-- §7.4 — KRR predictor is homogeneous in labels: scaling the label
    vector by `c` scales the prediction at every test point by `c`.
    Together with `krrPredictor_add_y` this gives ℝ-linearity of the
    KRR map `y ↦ f̂_y` for fixed `(k, xs, λ)` — a standard structural
    fact behind closed-form risk decompositions in Bach (2024) §7.4. -/
theorem krrPredictor_smul_y
    (k : 𝒳 → 𝒳 → ℝ) (xs : Fin n → 𝒳) (c : ℝ) (y : Fin n → ℝ)
    (lam : ℝ) (x : 𝒳) :
    krrPredictor k xs (c • y) lam x = c * krrPredictor k xs y lam x := by
  unfold krrPredictor
  rw [krrCoeffs_smul_y, kernelExpansion_smul]

/-! ### PSD-kernel closure properties (Bach 2024 §7.1)

Bach (2024) §7.1, pp. 184-185 lists the standard closure properties of
positive-semidefinite kernels: PSD-ness is preserved under
addition and non-negative scalar multiplication of kernels, and
therefore under arbitrary non-negative linear combinations. The proofs
reduce to the corresponding closure properties of PSD matrices applied
pointwise to Gram matrices.
-/

/-- §7.1 (Bach 2024, p. 184) — **Sum of PSD kernels is PSD.**

If `k₁` and `k₂` are positive-semidefinite kernels on `𝒳`, then their
pointwise sum `(x, y) ↦ k₁(x, y) + k₂(x, y)` is also PSD. Indeed, the
Gram matrix of `k₁ + k₂` on any sample equals the sum of the Gram
matrices, and PSD matrices are closed under addition. -/
theorem IsPSDKernel.add {k₁ k₂ : 𝒳 → 𝒳 → ℝ}
    (h₁ : IsPSDKernel k₁) (h₂ : IsPSDKernel k₂) :
    IsPSDKernel (fun x y => k₁ x y + k₂ x y) := by
  intro n xs
  have hsum :
      (Matrix.of fun i j : Fin n => k₁ (xs i) (xs j) + k₂ (xs i) (xs j)) =
        (Matrix.of fun i j : Fin n => k₁ (xs i) (xs j)) +
          (Matrix.of fun i j : Fin n => k₂ (xs i) (xs j)) := by
    ext i j; simp
  rw [hsum]
  exact (h₁ xs).add (h₂ xs)

/-- §7.1 (Bach 2024, p. 184) — **Non-negative scalar multiple of a PSD
    kernel is PSD.**

If `k` is positive-semidefinite and `c ≥ 0`, then the rescaled kernel
`(x, y) ↦ c * k(x, y)` is also PSD. The Gram matrix of `c · k` is the
scalar multiple `c • (Gram matrix of k)`, and PSD matrices are closed
under non-negative scalar multiplication. -/
theorem IsPSDKernel.smul_nonneg {k : 𝒳 → 𝒳 → ℝ}
    (hk : IsPSDKernel k) {c : ℝ} (hc : 0 ≤ c) :
    IsPSDKernel (fun x y => c * k x y) := by
  intro n xs
  have hsmul :
      (Matrix.of fun i j : Fin n => c * k (xs i) (xs j)) =
        c • (Matrix.of fun i j : Fin n => k (xs i) (xs j)) := by
    ext i j; simp [Matrix.smul_apply, smul_eq_mul]
  rw [hsmul]
  exact (hk xs).smul hc

/-- §7.1 (Bach 2024, p. 184) — **Diagonal non-negativity for PSD
    kernels.**

If `k` is positive-semidefinite, then `k(x, x) ≥ 0` for every
`x : 𝒳`. Specialising the PSD predicate to the one-point sample
`xs := fun _ => x` reduces the claim to the standard fact that PSD
matrices have non-negative diagonal entries. -/
theorem IsPSDKernel.self_nonneg {k : 𝒳 → 𝒳 → ℝ}
    (hk : IsPSDKernel k) (x : 𝒳) :
    0 ≤ k x x := by
  -- Use the 1-point Gram matrix `[[k(x,x)]]`, which is PSD, so its
  -- single diagonal entry is non-negative.
  have hG := hk (n := 1) (fun _ => x)
  have hdiag : 0 ≤
      (Matrix.of fun _ _ : Fin 1 => k x x) (0 : Fin 1) (0 : Fin 1) :=
    hG.diag_nonneg
  simpa using hdiag

/-! ### Symmetric-kernel predicate and Gram-matrix transpose

A kernel `k : 𝒳 → 𝒳 → ℝ` is **symmetric** when `k(x, y) = k(y, x)` for
all `x, y`. Every PSD kernel is symmetric (an immediate consequence of
its Gram matrix being Hermitian), but symmetry alone is strictly
weaker. We package the predicate and record that the Gram matrix of a
symmetric kernel coincides with its transpose. Cf. Bach (2024) §7.1,
p. 183.
-/

/-- §7.1 — A real-valued kernel `k` is **symmetric** when
`k(x, y) = k(y, x)` for all `x, y : 𝒳`. -/
def IsSymmKernel (k : 𝒳 → 𝒳 → ℝ) : Prop :=
  ∀ x y : 𝒳, k x y = k y x

/-- §7.1 — Every PSD kernel is symmetric: its Gram matrix on any
    two-point sample `(x, y)` is Hermitian, which in `ℝ` means
    `k(x, y) = k(y, x)`. -/
theorem IsPSDKernel.isSymm {k : 𝒳 → 𝒳 → ℝ} (hk : IsPSDKernel k) :
    IsSymmKernel k := by
  intro x y
  -- Use the 2-point sample (x, y); the resulting 2×2 Gram matrix is
  -- Hermitian, hence symmetric over ℝ.
  let xs : Fin 2 → 𝒳 := ![x, y]
  have hG := hk xs
  have hHerm := hG.isHermitian
  -- Hermitian over ℝ: M i j = star (M j i) = M j i.
  have h := hHerm.apply (1 : Fin 2) (0 : Fin 2)
  -- M 1 0 = star (M 0 1); over ℝ, star = id.
  -- (Matrix.of f) i j = f i j.
  simp [Matrix.of_apply, xs, Matrix.cons_val_zero, Matrix.cons_val_one,
        star_trivial] at h
  exact h

/-- §7.4 — For any symmetric kernel `k`, the Gram matrix on a sample
    `xs : Fin n → 𝒳` coincides with its own transpose. This is the
    matrix form of `gramMatrix_symm_of_symm_kernel` and is the entry
    point for invoking Mathlib's Hermitian-matrix infrastructure. -/
theorem gramMatrix_transpose_of_symm
    (k : 𝒳 → 𝒳 → ℝ) (hk : IsSymmKernel k) (xs : Fin n → 𝒳) :
    Matrix.transpose (gramMatrix k xs) = gramMatrix k xs := by
  ext i j
  simp [gramMatrix, Matrix.transpose_apply, Matrix.of_apply, hk (xs j) (xs i)]

/-! ### Bridge to Mathlib's `Matrix.PosSemidef` on Gram matrices

The `IsPSDKernel` predicate unfolds to: the matrix
`Matrix.of fun i j => k (xs i) (xs j)` is positive semidefinite for
every finite sample. Since this matrix is by definition `gramMatrix k xs`,
we record a named bridge that turns the PSD-kernel hypothesis directly
into a `Matrix.PosSemidef` fact on the Gram matrix, ready for use with
Mathlib's PSD-matrix infrastructure. -/

/-- §7.1 — **Gram matrix of a PSD kernel is PSD.**

If `k` is a positive-semidefinite kernel and `xs : Fin n → 𝒳` is any
sample, then the Gram matrix `gramMatrix k xs` is a positive
semidefinite matrix in the sense of `Matrix.PosSemidef`. This is the
named bridge from the LTFP `IsPSDKernel` predicate to Mathlib's
PSD-matrix API. -/
theorem gramMatrix_posSemidef_of_psdKernel {k : 𝒳 → 𝒳 → ℝ}
    (hk : IsPSDKernel k) (xs : Fin n → 𝒳) :
    (gramMatrix k xs).PosSemidef := by
  -- `gramMatrix k xs` is by definition the matrix `Matrix.of …` that
  -- `IsPSDKernel` asserts is PSD.
  exact hk xs

/-! ### Finite nonneg-weighted combinations of PSD kernels

Bach (2024) §7.1, pp. 184-185 states that the set of PSD kernels is a
convex cone: closed under addition and nonnegative scalar multiplication,
and therefore under arbitrary finite nonnegative linear combinations.
The binary statements `IsPSDKernel.add` and `IsPSDKernel.smul_nonneg`
above give the convex-cone generators; the lemma below packages the
arbitrary finite case directly, which is the reusable form for kernel
algebra in the rest of Chapter 7. -/

/-- §7.1 (Bach 2024, p. 184) — **Finite nonneg-weighted sum of PSD
    kernels is PSD.**

Given a finite index set `s : Finset ι`, a family of PSD kernels
`k : ι → 𝒳 → 𝒳 → ℝ` (with `k i` PSD for each `i ∈ s`), and
nonnegative weights `w i ≥ 0` on `s`, the pointwise nonneg-weighted
combination `(x, y) ↦ ∑ i ∈ s, w i * k i x y` is again PSD.

Proof: induction on `s`. The empty sum is the zero kernel
(`isPSDKernel_zero`); the inductive step combines `IsPSDKernel.add`
with `IsPSDKernel.smul_nonneg`. -/
theorem IsPSDKernel.finset_weighted_sum {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (k : ι → 𝒳 → 𝒳 → ℝ) (hk : ∀ i ∈ s, IsPSDKernel (k i)) :
    IsPSDKernel (fun x y => ∑ i ∈ s, w i * k i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      -- Empty sum is the zero kernel, which is PSD.
      intro n xs
      show (Matrix.of fun p q : Fin n =>
              ∑ idx ∈ (∅ : Finset ι),
                w idx * k idx (xs p) (xs q)).PosSemidef
      have hzero :
          (Matrix.of fun p q : Fin n =>
              ∑ idx ∈ (∅ : Finset ι),
                w idx * k idx (xs p) (xs q)) =
            (0 : Matrix (Fin n) (Fin n) ℝ) := by
        ext p q; simp
      rw [hzero]
      exact Matrix.PosSemidef.zero
  | @insert a t ha ih =>
      -- Split off the new term.
      have hw_a : 0 ≤ w a := hw a (Finset.mem_insert_self a t)
      have hk_a : IsPSDKernel (k a) := hk a (Finset.mem_insert_self a t)
      have hw_t : ∀ i ∈ t, 0 ≤ w i := fun i hi =>
        hw i (Finset.mem_insert_of_mem hi)
      have hk_t : ∀ i ∈ t, IsPSDKernel (k i) := fun i hi =>
        hk i (Finset.mem_insert_of_mem hi)
      -- Inductive hypothesis on `t`: PSD of the kernel `∑_{i∈t} w i * k i`.
      have h_tail :
          IsPSDKernel (fun x y => ∑ i ∈ t, w i * k i x y) := ih hw_t hk_t
      -- Head term `w a * k a x y` is PSD by nonneg scaling.
      have h_head : IsPSDKernel (fun x y => w a * k a x y) :=
        hk_a.smul_nonneg hw_a
      -- Combine head + tail by binary additivity.
      have h_sum :
          IsPSDKernel
            (fun x y : 𝒳 =>
              w a * k a x y + ∑ i ∈ t, w i * k i x y) :=
        IsPSDKernel.add
          (k₁ := fun x y => w a * k a x y)
          (k₂ := fun x y => ∑ i ∈ t, w i * k i x y)
          h_head h_tail
      -- Reduce the goal pointwise to `head + tail`.
      intro n xs
      show (Matrix.of fun p q : Fin n =>
              ∑ idx ∈ insert a t,
                w idx * k idx (xs p) (xs q)).PosSemidef
      have h_sum_app := h_sum xs
      -- `h_sum_app` already has the right shape modulo beta-reduction;
      -- convert via matrix equality.
      have hrw :
          (Matrix.of fun p q : Fin n =>
              ∑ idx ∈ insert a t,
                w idx * k idx (xs p) (xs q)) =
            (Matrix.of fun p q : Fin n =>
              w a * k a (xs p) (xs q) +
                ∑ i ∈ t, w i * k i (xs p) (xs q)) := by
        ext p q
        simp [Finset.sum_insert ha]
      rw [hrw]
      exact h_sum_app

end LTFP
