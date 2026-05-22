/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Calculus.GradientFlow

/-!
# Gradient flow at random initialization: interface specialization

The random-initialization parameterization specializes the local-existence
result from `GradientFlow.lean` to the setting needed by B8 N5
(lazy-training linearization). The ω-indexed family of losses `L ω` yields
an ω-indexed family of local gradient flows starting at `θ₀ ω`.

This is an interface step: it states the per-ω existence of a local
gradient flow given a C² loss and an initial point, without yet
introducing any probabilistic structure on ω.
-/

namespace LTFP.MathlibExt.Calculus

theorem gradientFlow_random_init_interface
    {Ω : Type*} (L : Ω → ℝ → ℝ) (θ₀ : Ω → ℝ) (t₀ : ℝ)
    (hL : ∀ ω : Ω, ContDiff ℝ 2 (L ω)) :
    ∀ ω : Ω, ∃ α : ℝ → ℝ, α t₀ = θ₀ ω ∧ ∃ ε > (0 : ℝ),
      ∀ t ∈ Set.Ioo (t₀ - ε) (t₀ + ε),
        HasDerivAt α (-(deriv (L ω)) (α t)) t := by
  intro ω
  exact LTFP.MathlibExt.Calculus.exists_local_gradient_flow_of_contDiff_two
    (L ω) (hL ω) (θ₀ ω) t₀

end LTFP.MathlibExt.Calculus
