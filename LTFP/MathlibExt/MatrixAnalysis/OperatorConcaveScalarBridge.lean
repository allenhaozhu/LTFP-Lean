/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.MatrixAnalysis.OperatorMonotone
import Mathlib.Analysis.Convex.Function

/-!
# Scalar bridge from `OperatorConcave` to `ConcaveOn`

If `f : ℝ → ℝ` is operator-concave in the matrix sense (`OperatorConcave f`,
defined in `OperatorMonotone.lean`), then `f` is concave in the usual scalar
sense on the whole real line. This is the universe-`(0, 0)`-instantiated
scalar bridge: feed `1×1` matrices `algebraMap ℝ (Matrix Unit Unit ℝ)` into
the predicate to extract scalar concavity.
-/

open scoped MatrixOrder

namespace LTFP.MathlibExt.MatrixAnalysis

private lemma real_le_of_algebraMap_matrix_le_oc {x y : ℝ}
    (hxy : (algebraMap ℝ (Matrix Unit Unit ℝ) x) ≤
      algebraMap ℝ (Matrix Unit Unit ℝ) y) : x ≤ y := by
  rw [Matrix.le_iff] at hxy
  have hdiag : 0 ≤ y - x := by
    simpa [sub_eq_add_neg, Matrix.algebraMap_eq_diagonal, Pi.algebraMap_def] using
      (Matrix.posSemidef_diagonal_iff
        (n := Unit) (d := fun _ : Unit => y - x)).1 hxy ()
  exact sub_nonneg.mp hdiag

private lemma algebraMap_matrix_affine_unit
    (a b x y : ℝ) (hab : a + b = 1) :
    a • (algebraMap ℝ (Matrix Unit Unit ℝ) x) +
        (1 - a) • (algebraMap ℝ (Matrix Unit Unit ℝ) y)
      = algebraMap ℝ (Matrix Unit Unit ℝ) (a • x + b • y) := by
  ext i j
  cases i
  cases j
  have hb : 1 - a = b := by linarith
  subst b
  simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal, smul_eq_mul]

theorem OperatorConcave.concaveOn_univ {f : ℝ → ℝ}
    (hf : OperatorConcave.{0, 0} f) : ConcaveOn ℝ Set.univ f := by
  constructor
  · exact convex_univ
  · intro x _ y _ a b ha hb hab
    have ht : a ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact ha
      · nlinarith [hb, hab]
    have hraw := hf
      (algebraMap ℝ (Matrix Unit Unit ℝ) x)
      (algebraMap ℝ (Matrix Unit Unit ℝ) y)
      (cfc_predicate_algebraMap (R := ℝ)
        (A := Matrix Unit Unit ℝ) (p := IsSelfAdjoint) x)
      (cfc_predicate_algebraMap (R := ℝ)
        (A := Matrix Unit Unit ℝ) (p := IsSelfAdjoint) y)
      a ht
    rw [algebraMap_matrix_affine_unit a b x y hab] at hraw
    have hleft := algebraMap_matrix_affine_unit a b (f x) (f y) hab
    have hmat :
        (algebraMap ℝ (Matrix Unit Unit ℝ) (a • f x + b • f y)) ≤
          algebraMap ℝ (Matrix Unit Unit ℝ) (f (a • x + b • y)) := by
      simpa only [cfc_algebraMap, ← hleft] using hraw
    exact real_le_of_algebraMap_matrix_le_oc hmat

end LTFP.MathlibExt.MatrixAnalysis
