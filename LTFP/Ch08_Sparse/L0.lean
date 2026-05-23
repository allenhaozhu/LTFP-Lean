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

/-! ### §8.2 — Support calculus for the ℓ₀-norm.

Sub-additivity, scalar-multiplication behavior, and corresponding
closure properties of `IsKSparse`. These are basic support-set
inclusions plus `Finset.card_union_le`; together they make the
sparse-model algebra (e.g. composing two sparse vectors) usable. -/

/-- §8.2 — Subadditivity of the ℓ₀ "norm": the support of `x + y`
    is contained in the union of supports, so its cardinality is at
    most the sum. -/
theorem l0Norm_add_le (x y : Fin d → ℝ) :
    l0Norm (x + y) ≤ l0Norm x + l0Norm y := by
  unfold l0Norm
  -- support(x + y) ⊆ support x ∪ support y
  have hsub :
      (Finset.univ.filter fun i => (x + y) i ≠ 0) ⊆
        (Finset.univ.filter fun i => x i ≠ 0) ∪
          (Finset.univ.filter fun i => y i ≠ 0) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      Pi.add_apply] at *
    by_contra hcontra
    push_neg at hcontra
    obtain ⟨hx, hy⟩ := hcontra
    exact hi (by rw [hx, hy, add_zero])
  exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)

/-- §8.2 — Scalar multiplication can only shrink the ℓ₀ support
    (it kills it entirely when `c = 0`). -/
theorem l0Norm_smul_le (c : ℝ) (x : Fin d → ℝ) :
    l0Norm (c • x) ≤ l0Norm x := by
  unfold l0Norm
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.smul_apply,
    smul_eq_mul] at *
  intro hxi
  exact hi (by rw [hxi, mul_zero])

/-- §8.2 — Nonzero scalar multiplication preserves the ℓ₀-norm. -/
theorem l0Norm_smul_eq_of_ne_zero {c : ℝ} (hc : c ≠ 0) (x : Fin d → ℝ) :
    l0Norm (c • x) = l0Norm x := by
  unfold l0Norm
  congr 1
  apply Finset.filter_congr
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, hc, false_or]

/-- §8.2 — Sum of a `k₁`-sparse and a `k₂`-sparse vector is `(k₁+k₂)`-sparse. -/
theorem IsKSparse.add {k₁ k₂ : ℕ} {x y : Fin d → ℝ}
    (hx : IsKSparse k₁ x) (hy : IsKSparse k₂ y) :
    IsKSparse (k₁ + k₂) (x + y) :=
  (l0Norm_add_le x y).trans (Nat.add_le_add hx hy)

/-- §8.2 — Scalar multiplication preserves k-sparsity. -/
theorem IsKSparse.smul {k : ℕ} {x : Fin d → ℝ}
    (hx : IsKSparse k x) (c : ℝ) : IsKSparse k (c • x) :=
  (l0Norm_smul_le c x).trans hx

end LTFP
