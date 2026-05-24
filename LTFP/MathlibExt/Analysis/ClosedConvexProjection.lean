/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

/-!
# Projection onto a nonempty closed convex set in a real Hilbert space

Mathlib's `Mathlib/Analysis/InnerProductSpace/Projection/Minimal.lean`
provides the **Hilbert projection theorem**
(`exists_norm_eq_iInf_of_complete_convex`) and the variational
characterization of the minimizer
(`norm_eq_iInf_iff_real_inner_le_zero`).  However, the bundled
projection map exposed by Mathlib (`Submodule.starProjection`) is
defined only on **submodules**, not on arbitrary nonempty closed
convex constraint sets.

This file adds a small reusable API for the projection onto an
arbitrary nonempty closed convex subset of a real Hilbert space:

* `closedConvexProj C hne hclosed hconv x` — the projection of `x`
  onto `C`, chosen by `Classical.choose` from the Hilbert projection
  existence theorem.
* `closedConvexProj_mem` — the projection lies in `C`.
* `closedConvexProj_minimal` — the projection minimizes
  `‖x - y‖` over `y ∈ C`.
* `closedConvexProj_variational` — the first-order variational
  inequality `⟨x - p, y - p⟩_ℝ ≤ 0` for all `y ∈ C`, which is the
  defining property of the metric projection on a convex set.
* `closedConvexProj_nonexpansive` — the projection is
  `LipschitzWith 1`, i.e. `‖P_C(x) - P_C(y)‖ ≤ ‖x - y‖`.  This is
  proved by summing the two variational inequalities at `x` and `y`
  and applying Cauchy-Schwarz.

The hypotheses are deliberately kept **explicit** (a `Set E` plus
`Nonempty`, `IsClosed`, `Convex ℝ` proofs) rather than bundled into a
structure carrying the constraint set.  This matches the style of
Mathlib's bare existence theorems and keeps elaboration costs low for
downstream call sites.

Sub-step 1 of strategic milestone 2 landed the def + `_mem` /
`_minimal` / `_variational`.  Sub-step 2 (this file) closes the
milestone by adding nonexpansivity here and the matching concrete
`pgdStep_closedConvex` wrapper in `LTFP/Ch05_Optimization/GD.lean`.
-/

namespace LTFP.MathlibExt.Analysis

open Set

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Projection of a point `x` onto a nonempty closed convex subset `C`
of a real Hilbert space `E`, selected via the Hilbert projection
theorem (`exists_norm_eq_iInf_of_complete_convex`).

The choice is made by `Classical.choose`; while the minimizer is
unique (a consequence of strict convexity of the squared norm), this
uniqueness is not needed for the variational characterization below
and is therefore not bundled into the definition. -/
noncomputable def closedConvexProj
    (C : Set E) (hne : C.Nonempty) (hclosed : IsClosed C)
    (hconv : Convex ℝ C) (x : E) : E :=
  Classical.choose
    (exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hconv x)

/-- The projection of `x` onto a nonempty closed convex set `C` lies
in `C`. -/
theorem closedConvexProj_mem
    (C : Set E) (hne : C.Nonempty) (hclosed : IsClosed C)
    (hconv : Convex ℝ C) (x : E) :
    closedConvexProj C hne hclosed hconv x ∈ C := by
  have h := Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hconv x)
  exact h.1

/-- The projection of `x` onto a nonempty closed convex set `C`
minimizes the distance `‖x - y‖` over `y ∈ C`. -/
theorem closedConvexProj_minimal
    (C : Set E) (hne : C.Nonempty) (hclosed : IsClosed C)
    (hconv : Convex ℝ C) (x : E) :
    ‖x - closedConvexProj C hne hclosed hconv x‖ = ⨅ y : C, ‖x - y‖ := by
  have h := Classical.choose_spec
    (exists_norm_eq_iInf_of_complete_convex hne hclosed.isComplete hconv x)
  exact h.2

/-- **First-order variational characterization of the metric
projection on a convex set.**

For any `y ∈ C`, the inner product `⟨x - p, y - p⟩_ℝ` is
nonpositive, where `p = closedConvexProj C hne hclosed hconv x`. This
is the defining property of the metric projection in a real Hilbert
space and is the workhorse inequality for proving nonexpansivity and
for analyzing projected gradient descent. -/
theorem closedConvexProj_variational
    (C : Set E) (hne : C.Nonempty) (hclosed : IsClosed C)
    (hconv : Convex ℝ C) (x : E) :
    ∀ y ∈ C,
      inner ℝ
        (x - closedConvexProj C hne hclosed hconv x)
        (y - closedConvexProj C hne hclosed hconv x) ≤ 0 := by
  have hmem := closedConvexProj_mem C hne hclosed hconv x
  have hmin := closedConvexProj_minimal C hne hclosed hconv x
  exact (norm_eq_iInf_iff_real_inner_le_zero hconv hmem).mp hmin

/-- **Nonexpansivity of the metric projection.**  The projection map
`closedConvexProj C hne hclosed hconv` onto a nonempty closed convex
subset `C` of a real Hilbert space is 1-Lipschitz:
`‖P_C(x) - P_C(y)‖ ≤ ‖x - y‖` for all `x, y`.

The proof applies `closedConvexProj_variational` twice (once at each
projected point) to get
  `⟨x - P_C x, P_C y - P_C x⟩_ℝ ≤ 0`,
  `⟨y - P_C y, P_C x - P_C y⟩_ℝ ≤ 0`.
Summing yields `‖P_C x - P_C y‖² ≤ ⟪x - y, P_C x - P_C y⟫_ℝ`, which
combined with Cauchy-Schwarz (`real_inner_le_norm`) gives the bound.
-/
theorem closedConvexProj_nonexpansive
    (C : Set E) (hne : C.Nonempty) (hclosed : IsClosed C)
    (hconv : Convex ℝ C) :
    LipschitzWith 1 (closedConvexProj C hne hclosed hconv) := by
  -- Reduce `LipschitzWith 1 f` to `∀ x y, dist (f x) (f y) ≤ dist x y`.
  refine LipschitzWith.mk_one ?_
  intro x y
  -- Switch from `dist` to `‖·‖` on both sides.
  simp only [dist_eq_norm]
  -- Notation for the two projections and their difference `d := p_x - p_y`.
  set p_x : E := closedConvexProj C hne hclosed hconv x with hpx_def
  set p_y : E := closedConvexProj C hne hclosed hconv y with hpy_def
  have hpx_mem : p_x ∈ C := closedConvexProj_mem C hne hclosed hconv x
  have hpy_mem : p_y ∈ C := closedConvexProj_mem C hne hclosed hconv y
  -- Variational inequality at `x`, tested against `p_y ∈ C`:
  --   ⟨x - p_x, p_y - p_x⟩_ℝ ≤ 0.
  have h₁ : inner ℝ (x - p_x) (p_y - p_x) ≤ 0 :=
    closedConvexProj_variational C hne hclosed hconv x p_y hpy_mem
  -- Variational inequality at `y`, tested against `p_x ∈ C`:
  --   ⟨y - p_y, p_x - p_y⟩_ℝ ≤ 0.
  have h₂ : inner ℝ (y - p_y) (p_x - p_y) ≤ 0 :=
    closedConvexProj_variational C hne hclosed hconv y p_x hpx_mem
  -- Algebraic manipulation: ⟨x - p_x, p_y - p_x⟩ + ⟨y - p_y, p_x - p_y⟩
  -- ≤ 0 expands to ‖p_x - p_y‖² ≤ ⟨x - y, p_x - p_y⟩_ℝ.
  have hsum : inner ℝ (x - p_x) (p_y - p_x) +
              inner ℝ (y - p_y) (p_x - p_y) ≤ 0 := by linarith
  -- Rewrite the LHS of `hsum` as `⟨p_x - p_y, p_x - p_y⟩ - ⟨x - y, p_x - p_y⟩`
  -- using bilinearity of the inner product, then `hsum ≤ 0` gives
  -- `‖p_x - p_y‖² ≤ ⟨x - y, p_x - p_y⟩`.
  have hkey : ‖p_x - p_y‖ ^ 2 ≤ inner ℝ (x - y) (p_x - p_y) := by
    have hinner_self : inner ℝ (p_x - p_y) (p_x - p_y) = ‖p_x - p_y‖ ^ 2 :=
      real_inner_self_eq_norm_sq (p_x - p_y)
    -- Flip the first inner product: `p_y - p_x = -(p_x - p_y)`.
    have hflip : inner ℝ (x - p_x) (p_y - p_x) =
        -inner ℝ (x - p_x) (p_x - p_y) := by
      have hneg : p_y - p_x = -(p_x - p_y) := by rw [neg_sub]
      rw [hneg, inner_neg_right]
    -- After the flip,
    -- ⟨x-p_x, p_y-p_x⟩ + ⟨y-p_y, p_x-p_y⟩
    --   = -⟨x-p_x, p_x-p_y⟩ + ⟨y-p_y, p_x-p_y⟩
    --   = -⟨(x-p_x) - (y-p_y), p_x-p_y⟩
    --   = ⟨p_x - p_y, p_x - p_y⟩ - ⟨x - y, p_x - p_y⟩.
    have hexpand :
        inner ℝ (x - p_x) (p_y - p_x) + inner ℝ (y - p_y) (p_x - p_y) =
          inner ℝ (p_x - p_y) (p_x - p_y) - inner ℝ (x - y) (p_x - p_y) := by
      rw [hflip]
      simp only [inner_sub_left]
      ring
    linarith [hexpand ▸ hsum, hinner_self]
  -- Cauchy-Schwarz: ⟨x - y, p_x - p_y⟩_ℝ ≤ ‖x - y‖ · ‖p_x - p_y‖.
  have hCS : inner ℝ (x - y) (p_x - p_y) ≤ ‖x - y‖ * ‖p_x - p_y‖ :=
    real_inner_le_norm (x - y) (p_x - p_y)
  -- Combine: ‖p_x - p_y‖² ≤ ‖x - y‖ · ‖p_x - p_y‖.
  have hsq : ‖p_x - p_y‖ ^ 2 ≤ ‖x - y‖ * ‖p_x - p_y‖ := le_trans hkey hCS
  -- Case split on whether `p_x - p_y` is zero.
  by_cases hd : ‖p_x - p_y‖ = 0
  · -- `‖p_x - p_y‖ = 0 ≤ ‖x - y‖`.
    rw [hd]; exact norm_nonneg _
  · -- `‖p_x - p_y‖ > 0`, so divide both sides of `hsq`.
    have hpos : 0 < ‖p_x - p_y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
    have hsq' : ‖p_x - p_y‖ * ‖p_x - p_y‖ ≤ ‖x - y‖ * ‖p_x - p_y‖ := by
      have : ‖p_x - p_y‖ ^ 2 = ‖p_x - p_y‖ * ‖p_x - p_y‖ := sq (‖p_x - p_y‖)
      linarith [hsq, this]
    exact le_of_mul_le_mul_right hsq' hpos

end LTFP.MathlibExt.Analysis
