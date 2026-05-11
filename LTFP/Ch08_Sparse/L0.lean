/-
LTFP §8.2 — Variable selection by ℓ₀-penalty.

Bach (2024) §8.2, pp. 226-231. The ℓ₀-norm `‖θ‖₀` counts the
number of non-zero coordinates of `θ ∈ ℝᵈ`. Subset selection minimizes
empirical risk subject to `‖θ‖₀ ≤ k` for a target sparsity `k`. This
is NP-hard in general; ℓ₁-regularization (Lasso, §8.3, vendored)
is the convex relaxation.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators

namespace LTFP

variable {d : ℕ}

/-- §8.2 — The ℓ₀ "norm": number of non-zero coordinates of `θ`.
    Not a true norm (fails homogeneity), but standard notation. -/
noncomputable def l0Norm (θ : Fin d → ℝ) : ℕ :=
  (Finset.univ.filter fun i => θ i ≠ 0).card

/-- §8.2 sanity lemma: the ℓ₀-norm of the zero vector is zero. -/
theorem l0Norm_zero : l0Norm (0 : Fin d → ℝ) = 0 := by
  unfold l0Norm
  simp

/-- §8.2 sanity lemma: the ℓ₀-norm is bounded by the dimension. -/
theorem l0Norm_le_dim (θ : Fin d → ℝ) : l0Norm θ ≤ d := by
  unfold l0Norm
  exact (Finset.univ.filter _).card_le_card (Finset.subset_univ _)
    |>.trans_eq (by simp)

/-- §8.2 — k-sparsity predicate: `θ` has at most `k` non-zero entries. -/
def IsKSparse (k : ℕ) (θ : Fin d → ℝ) : Prop := l0Norm θ ≤ k

/-- §8.2 — The zero vector is `0`-sparse. -/
theorem isKSparse_zero : IsKSparse 0 (0 : Fin d → ℝ) := by
  unfold IsKSparse
  rw [l0Norm_zero]

/-- §8.2 — k-sparsity is monotone in `k`. -/
theorem IsKSparse.mono {k k' : ℕ} {θ : Fin d → ℝ}
    (h : IsKSparse k θ) (hkk' : k ≤ k') : IsKSparse k' θ :=
  h.trans hkk'

/-- §8.2 — Every vector is `d`-sparse (the trivial upper bound). -/
theorem isKSparse_dim (θ : Fin d → ℝ) : IsKSparse d θ := l0Norm_le_dim θ

/-- §8.2 — Zero vector is k-sparse for any k. -/
theorem isKSparse_zero_any (k : ℕ) : IsKSparse k (0 : Fin d → ℝ) := by
  unfold IsKSparse
  rw [l0Norm_zero]
  exact Nat.zero_le k

/-- §8.2 — k-sparsity is upward-closed (mono in k). -/
theorem isKSparse_succ_of_kSparse {k : ℕ} {θ : Fin d → ℝ}
    (h : IsKSparse k θ) : IsKSparse (k + 1) θ :=
  h.mono (Nat.le_succ k)

end LTFP
