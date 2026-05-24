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

The hypotheses are deliberately kept **explicit** (a `Set E` plus
`Nonempty`, `IsClosed`, `Convex ℝ` proofs) rather than bundled into a
structure carrying the constraint set.  This matches the style of
Mathlib's bare existence theorems and keeps elaboration costs low for
downstream call sites.

This is sub-step 1 of strategic milestone 2 (constrained / projected
gradient descent).  Sub-step 2 will use this projection map to refine
`pgdStep` in `LTFP/Ch05_Optimization/GD.lean`.
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

end LTFP.MathlibExt.Analysis
