/-
LTFP foundation: random projections / Johnson–Lindenstrauss.

Phase-3a anchor for Ch 10 (ensemble learning via random projections)
and Ch 12 (overparameterized random feature models). A Gaussian
sketch `Φ ∈ ℝᵏˣᵈ` with iid `N(0, 1/k)` entries approximately preserves
norms: `‖Φx‖² ≈ ‖x‖²`. The full JL bound is deferred to Ch 10.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace LTFP

variable {n d : ℕ}

/-- §F7 — Apply a sketch matrix `Φ : ℝᵏˣᵈ` to a vector `x : ℝᵈ`,
    yielding a vector in `ℝᵏ`. (Wraps `Matrix.mulVec`.) -/
def sketch (Φ : Matrix (Fin n) (Fin d) ℝ) (x : Fin d → ℝ) : Fin n → ℝ :=
  Φ.mulVec x

/-- §F7 sanity lemma: sketching the zero vector yields zero. -/
theorem sketch_zero (Φ : Matrix (Fin n) (Fin d) ℝ) :
    sketch Φ (0 : Fin d → ℝ) = 0 := by
  unfold sketch
  exact Matrix.mulVec_zero Φ

/-- §F7 — Sketching the zero matrix sends every vector to zero. -/
theorem sketch_zero_matrix (x : Fin d → ℝ) :
    sketch (0 : Matrix (Fin n) (Fin d) ℝ) x = 0 := by
  unfold sketch
  exact Matrix.zero_mulVec x

/-- §F7 — Sketching by `1` (identity matrix) preserves the input on its
    image: `sketch I x = x` (when dimensions match). -/
theorem sketch_one (x : Fin n → ℝ) :
    sketch (1 : Matrix (Fin n) (Fin n) ℝ) x = x := by
  unfold sketch
  exact Matrix.one_mulVec x

/-- §F7 — Sketching is linear in the matrix as well. -/
theorem sketch_add_matrix (Φ Ψ : Matrix (Fin n) (Fin d) ℝ) (x : Fin d → ℝ) :
    sketch (Φ + Ψ) x = sketch Φ x + sketch Ψ x := by
  unfold sketch
  exact Matrix.add_mulVec Φ Ψ x

/-- §F7 — Sketching is monotone in linear combinations: a positive
    multiple of a sketch is a sketch of the scaled matrix. -/
theorem sketch_smul_matrix (c : ℝ) (Φ : Matrix (Fin n) (Fin d) ℝ)
    (x : Fin d → ℝ) :
    sketch (c • Φ) x = c • sketch Φ x := by
  unfold sketch
  exact Matrix.smul_mulVec_assoc c Φ x

end LTFP
