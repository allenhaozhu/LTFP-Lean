/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Data.Real.Sign

/-!
# Subgradients of the absolute value and the `ℓ¹` norm

This file develops the elementary subgradient calculus for the real
absolute-value function `|·| : ℝ → ℝ` and its componentwise lift to the
`ℓ¹` norm `‖v‖₁ = ∑ᵢ |vᵢ|` on `Fin n → ℝ`.

A real number `g` is a subgradient of `|·|` at `x` when
`|y| ≥ |x| + g * (y - x)` holds for every `y : ℝ`. The classical
characterization (Boyd–Vandenberghe, §3.1.5; Hiriart-Urruty–Lemaréchal,
Vol. I, §VI.3) states that the subdifferential `∂|·|(x)` equals

* `{1}` if `x > 0`,
* `{-1}` if `x < 0`,
* `[-1, 1]` if `x = 0`.

These three cases unify via `Real.sign` away from `0`. Lifting
coordinate-by-coordinate yields the `ℓ¹` subdifferential, which is the
algebraic backbone of the Lasso KKT optimality system.

## Main definitions

* `IsAbsSubgradient`: predicate stating that a real `g` is a subgradient
  of `|·|` at `x`.
* `IsL1Subgradient`: componentwise lift of `IsAbsSubgradient` to
  `Fin n → ℝ`.

## Main results

* `isAbsSubgradient_of_pos`, `isAbsSubgradient_of_neg`: the constants
  `1` and `-1` are subgradients at strictly positive and strictly
  negative inputs, respectively.
* `isAbsSubgradient_zero_iff`: the subdifferential at `0` is exactly the
  closed interval `[-1, 1]`.
* `isAbsSubgradient_sign`: `Real.sign x` is a subgradient at every
  nonzero `x` (it is in fact the unique one).
* `abs_subgradient_mem_interval`: every subgradient `g` of `|·|` at any
  point satisfies `|g| ≤ 1`.
* `isL1Subgradient_componentwise`: a componentwise characterization of
  `ℓ¹` subgradients via `IsAbsSubgradient` per coordinate.

## Implementation notes

`IsAbsSubgradient` is *not* a typeclass-style predicate: whether `g`
witnesses the subgradient inequality depends on the *value* of `g`, so
making it an `instance` would not be useful (Lean cannot synthesize a
witness without the value). For the same reason `IsL1Subgradient` is a
plain definition.

Proposed Mathlib path: `Mathlib/Analysis/Convex/Subgradient/Abs.lean`.
Proposed Mathlib namespace: `Convex.IsAbsSubgradient` (or the future
`Subgradient` namespace established by the upstream review).

## References

* Stephen Boyd and Lieven Vandenberghe, *Convex Optimization*,
  Cambridge University Press, 2004, §3.1.5 and §A.5.
* Jean-Baptiste Hiriart-Urruty and Claude Lemaréchal,
  *Convex Analysis and Minimization Algorithms I*, Springer, 1993,
  Chapter VI.
* Francis Bach, *Learning Theory from First Principles*, MIT Press,
  2024, §8.2 (Lasso optimality).

## Tags

subgradient, subdifferential, convex, lasso, absolute value, l1 norm
-/

namespace LTFP.MathlibExt.Analysis

/-- A real number `g` is a *subgradient* of `|·| : ℝ → ℝ` at `x` if
the subgradient inequality `|y| ≥ |x| + g * (y - x)` holds for every
`y : ℝ`. -/
def IsAbsSubgradient (x g : ℝ) : Prop :=
  ∀ y : ℝ, |y| ≥ |x| + g * (y - x)

/-- At any strictly positive point, the constant `1` is a subgradient of
the absolute-value function. -/
theorem isAbsSubgradient_of_pos {x : ℝ} (hx : 0 < x) : IsAbsSubgradient x 1 := by
  intro y
  have hx_abs : |x| = x := abs_of_pos hx
  have hy_abs : |y| ≥ y := le_abs_self y
  rw [hx_abs, one_mul]
  linarith [hy_abs]

/-- At any strictly negative point, the constant `-1` is a subgradient
of the absolute-value function. -/
theorem isAbsSubgradient_of_neg {x : ℝ} (hx : x < 0) : IsAbsSubgradient x (-1) := by
  intro y
  have hx_abs : |x| = -x := abs_of_neg hx
  have hy_abs : |y| ≥ -y := neg_le_abs y
  rw [hx_abs]
  linarith [hy_abs]

/-- The subdifferential of `|·|` at `0` is exactly the closed interval
`[-1, 1]`: a real `g` is a subgradient at `0` if and only if
`|g| ≤ 1`. -/
theorem isAbsSubgradient_zero_iff {g : ℝ} : IsAbsSubgradient 0 g ↔ |g| ≤ 1 := by
  constructor
  · intro h
    -- Probe the subgradient inequality at `y = 1` and `y = -1`.
    have h1 : |(1 : ℝ)| ≥ |(0 : ℝ)| + g * (1 - 0) := h 1
    have h2 : |(-1 : ℝ)| ≥ |(0 : ℝ)| + g * (-1 - 0) := h (-1)
    rw [abs_zero, abs_one] at h1
    rw [abs_zero, abs_neg, abs_one] at h2
    have hg_le : g ≤ 1 := by linarith
    have hg_ge : -1 ≤ g := by linarith
    exact abs_le.mpr ⟨hg_ge, hg_le⟩
  · intro h y
    rw [abs_zero, zero_add]
    rcases abs_le.mp h with ⟨hg_lb, hg_ub⟩
    rcases le_or_gt 0 y with hy | hy
    · have hy_abs : |y| = y := abs_of_nonneg hy
      rw [hy_abs]
      nlinarith
    · have hy_abs : |y| = -y := abs_of_neg hy
      rw [hy_abs]
      nlinarith

/-- At every nonzero point, `Real.sign x` is a subgradient of `|·|` at
`x`. (It is the unique one, by `isAbsSubgradient_zero_iff` paired with
`abs_subgradient_mem_interval`.) -/
theorem isAbsSubgradient_sign {x : ℝ} (hx : x ≠ 0) :
    IsAbsSubgradient x (Real.sign x) := by
  rcases lt_or_gt_of_ne hx with hx_neg | hx_pos
  · rw [Real.sign_of_neg hx_neg]
    exact isAbsSubgradient_of_neg hx_neg
  · rw [Real.sign_of_pos hx_pos]
    exact isAbsSubgradient_of_pos hx_pos

/-- Every subgradient `g` of `|·|` at any point `x` satisfies
`|g| ≤ 1`. This is the standard a-priori bound on the subdifferential
of a `1`-Lipschitz convex function. -/
theorem abs_subgradient_mem_interval {x g : ℝ} (h : IsAbsSubgradient x g) :
    |g| ≤ 1 := by
  -- Probe the subgradient inequality at `y = x + 1` and `y = x - 1`.
  have h1 : |x + 1| ≥ |x| + g * ((x + 1) - x) := h (x + 1)
  have h2 : |x - 1| ≥ |x| + g * ((x - 1) - x) := h (x - 1)
  have h1' : |x + 1| ≥ |x| + g := by simpa using h1
  have h2' : |x - 1| ≥ |x| - g := by
    have := h2
    simp only [sub_sub_cancel_left] at this
    linarith
  -- Combine with the triangle-inequality bounds `|x ± 1| ≤ |x| + 1`.
  have hub1 : |x + 1| ≤ |x| + 1 := by
    have := abs_add_le x 1
    simpa using this
  have hub2 : |x - 1| ≤ |x| + 1 := by
    have := abs_sub x 1
    simpa using this
  have hg_le : g ≤ 1 := by linarith
  have hg_ge : -1 ≤ g := by linarith
  exact abs_le.mpr ⟨hg_ge, hg_le⟩

/-- A function `g : Fin n → ℝ` is an *`ℓ¹` subgradient* of
`v : Fin n → ℝ` if every component `g i` is a scalar subgradient of
`|·|` at `v i`. -/
def IsL1Subgradient {n : ℕ} (v g : Fin n → ℝ) : Prop :=
  ∀ i : Fin n, IsAbsSubgradient (v i) (g i)

/-- Componentwise characterization of `ℓ¹` subgradients: a vector `g` is
an `ℓ¹` subgradient of `v` if and only if, for every coordinate `i`,
either `v i ≠ 0` and `g i = Real.sign (v i)`, or `v i = 0` and
`|g i| ≤ 1`. -/
theorem isL1Subgradient_componentwise {n : ℕ} {v g : Fin n → ℝ} :
    IsL1Subgradient v g ↔
      ∀ i : Fin n,
        (v i ≠ 0 ∧ g i = Real.sign (v i)) ∨ (v i = 0 ∧ |g i| ≤ 1) := by
  constructor
  · intro h i
    by_cases hvi : v i = 0
    · refine Or.inr ⟨hvi, ?_⟩
      have hgi : IsAbsSubgradient 0 (g i) := hvi ▸ h i
      exact (isAbsSubgradient_zero_iff).mp hgi
    · refine Or.inl ⟨hvi, ?_⟩
      have hgi : IsAbsSubgradient (v i) (g i) := h i
      have habs : |g i| ≤ 1 := abs_subgradient_mem_interval hgi
      rcases lt_or_gt_of_ne hvi with hneg | hpos
      · -- `v i < 0`: the subgradient inequality at `y = 0` forces `g i = -1`.
        rw [Real.sign_of_neg hneg]
        have h0 : |(0 : ℝ)| ≥ |v i| + g i * (0 - v i) := hgi 0
        rw [abs_zero, abs_of_neg hneg] at h0
        have hge : -1 ≤ g i := (abs_le.mp habs).1
        have hle : g i ≤ -1 := by nlinarith
        linarith
      · -- `v i > 0`: the subgradient inequality at `y = 0` forces `g i = 1`.
        rw [Real.sign_of_pos hpos]
        have h0 : |(0 : ℝ)| ≥ |v i| + g i * (0 - v i) := hgi 0
        rw [abs_zero, abs_of_pos hpos] at h0
        have hle : g i ≤ 1 := (abs_le.mp habs).2
        have hge : 1 ≤ g i := by nlinarith
        linarith
  · intro h i
    rcases h i with ⟨hvi, hgi⟩ | ⟨hvi, hgi⟩
    · rw [hgi]
      exact isAbsSubgradient_sign hvi
    · rw [hvi]
      exact (isAbsSubgradient_zero_iff).mpr hgi

/-! ### Multidimensional ℓ¹ subdifferential

The coordinate-wise predicate `IsL1Subgradient` matches the *global*
subgradient of the ℓ¹ norm `‖β‖₁ = ∑ᵢ |βᵢ|` on `Fin d → ℝ`. We package
this characterization under a swapped-argument alias
`IsL1SubgradientFin v β` (subgradient-then-point ordering, matching the
convex-analysis convention `v ∈ ∂‖·‖₁(β)`) and supply the equivalence
with the global definition `∀ y, ‖y‖₁ ≥ ‖β‖₁ + ⟨v, y − β⟩`. -/

/-- A vector `v : Fin d → ℝ` is an *`ℓ¹` subgradient* of `β : Fin d → ℝ`
in the coordinate-wise sense: `v i ∈ ∂|·|(β i)` for every `i`. This is
the textbook subdifferential of `‖·‖₁` (Boyd–Vandenberghe §3.1.5;
Hiriart-Urruty–Lemaréchal Vol. I, §VI.3). Argument order mirrors the
convex-analysis convention `v ∈ ∂‖·‖₁(β)`. -/
def IsL1SubgradientFin {d : ℕ} (v β : Fin d → ℝ) : Prop :=
  ∀ i : Fin d, IsAbsSubgradient (β i) (v i)

/-- Coordinate-wise characterization of multidim ℓ¹ subgradients:
`v ∈ ∂‖·‖₁(β)` iff each `v i` is a scalar subgradient of `|·|` at
`β i`. This is definitional by `IsL1SubgradientFin`; we record the
restatement for clarity at the call site. -/
theorem isL1SubgradientFin_iff_coords {d : ℕ} {v β : Fin d → ℝ} :
    IsL1SubgradientFin v β ↔ ∀ i : Fin d, IsAbsSubgradient (β i) (v i) :=
  Iff.rfl

/-- Bridge between the coordinate-wise predicate and the existing
`IsL1Subgradient` (point-then-subgradient ordering): the two predicates
are equivalent up to argument swap. -/
theorem isL1SubgradientFin_iff_isL1Subgradient
    {d : ℕ} {v β : Fin d → ℝ} :
    IsL1SubgradientFin v β ↔ IsL1Subgradient β v :=
  Iff.rfl

/-- **Global ℓ¹ subdifferential characterization.** A vector `v` is an
`ℓ¹` subgradient of `β` (in the coordinate-wise sense
`IsL1SubgradientFin v β`) if and only if it witnesses the global
subgradient inequality for the ℓ¹ norm:
`∑ᵢ |yᵢ| ≥ ∑ᵢ |βᵢ| + ⟨v, y − β⟩` for every `y : Fin d → ℝ`. -/
theorem isL1SubgradientFin_l1Norm {d : ℕ} {v β : Fin d → ℝ} :
    IsL1SubgradientFin v β ↔
      ∀ y : Fin d → ℝ,
        (∑ i, |y i|) ≥ (∑ i, |β i|) + ∑ i, v i * (y i - β i) := by
  constructor
  · intro h y
    -- Sum the coordinate-wise subgradient inequalities.
    have hcoord : ∀ i ∈ (Finset.univ : Finset (Fin d)),
        |β i| + v i * (y i - β i) ≤ |y i| := by
      intro i _
      have hi : IsAbsSubgradient (β i) (v i) := h i
      exact hi (y i)
    have hsum :
        ∑ i, (|β i| + v i * (y i - β i)) ≤ ∑ i, |y i| :=
      Finset.sum_le_sum hcoord
    have hsplit :
        ∑ i, (|β i| + v i * (y i - β i))
          = (∑ i, |β i|) + ∑ i, v i * (y i - β i) :=
      Finset.sum_add_distrib
    linarith
  · intro h i y
    -- Probe the global inequality at the canonical "single-coordinate
    -- perturbation" `y i := y, y j := β j` for `j ≠ i`. The sums
    -- collapse and leave precisely the scalar subgradient inequality at
    -- coordinate `i`.
    classical
    set z : Fin d → ℝ := Function.update β i y with hz_def
    have hglob := h z
    -- All coordinates except `i` cancel pairwise; coordinate `i`
    -- carries `|y|` on the LHS and `|β i| + v i * (y - β i)` on the RHS.
    have hsum_abs : ∑ j, |z j| = |y| + ∑ j ∈ Finset.univ.erase i, |β j| := by
      have hi_mem : i ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ i
      rw [← Finset.sum_erase_add _ _ hi_mem]
      have hzi : z i = y := by simp [hz_def, Function.update_self]
      rw [hzi]
      have hzj : ∀ j ∈ Finset.univ.erase i, |z j| = |β j| := by
        intro j hj
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        simp [hz_def, Function.update_of_ne hji]
      rw [Finset.sum_congr rfl hzj]
      ring
    have hsum_abs_beta :
        ∑ j, |β j| = |β i| + ∑ j ∈ Finset.univ.erase i, |β j| := by
      have hi_mem : i ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ i
      rw [← Finset.sum_erase_add _ _ hi_mem]
      ring
    have hsum_lin :
        ∑ j, v j * (z j - β j) = v i * (y - β i) := by
      have hi_mem : i ∈ (Finset.univ : Finset (Fin d)) := Finset.mem_univ i
      rw [← Finset.sum_erase_add _ _ hi_mem]
      have hzi : z i = y := by simp [hz_def, Function.update_self]
      have hzj : ∀ j ∈ Finset.univ.erase i, v j * (z j - β j) = 0 := by
        intro j hj
        have hji : j ≠ i := (Finset.mem_erase.mp hj).1
        have hzj_eq : z j = β j := by
          simp [hz_def, Function.update_of_ne hji]
        rw [hzj_eq, sub_self, mul_zero]
      rw [Finset.sum_congr rfl hzj, Finset.sum_const_zero, zero_add, hzi]
    rw [hsum_abs, hsum_abs_beta, hsum_lin] at hglob
    -- After cancellation the constant tail `∑_{j≠i} |β j|` drops out.
    linarith

/-! ### Examples

The following examples demonstrate the three regimes of the scalar
subdifferential of `|·|`. -/

/-- At any strictly positive point, the value `1` witnesses the
subgradient inequality. -/
example : IsAbsSubgradient (2 : ℝ) 1 := isAbsSubgradient_of_pos (by norm_num)

/-- At `0`, every value in `[-1, 1]` is a subgradient — for instance
`1/2`. -/
example : IsAbsSubgradient (0 : ℝ) (1 / 2) :=
  isAbsSubgradient_zero_iff.mpr (by rw [abs_of_pos]; norm_num; norm_num)

/-- At any nonzero point, `Real.sign x` is a subgradient. -/
example : IsAbsSubgradient (-3 : ℝ) (Real.sign (-3)) :=
  isAbsSubgradient_sign (by norm_num)

end LTFP.MathlibExt.Analysis
