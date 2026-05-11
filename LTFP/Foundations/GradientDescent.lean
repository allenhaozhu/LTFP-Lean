/-
LTFP foundation: gradient descent.

Phase-3a anchor for Ch 5 (optimization), Ch 9 (NN training), Ch 12
(implicit bias of GD). The gradient-descent update with step `γ` is
`xₜ₊₁ = xₜ − γ · ∇f(xₜ)`. We define the update map and a one-step
identity; full convergence theorems are deferred to Ch 5 itself.
-/
import Mathlib.Analysis.Calculus.Gradient.Basic

namespace LTFP

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- §F2 — Gradient-descent update with step size `γ ≥ 0`. -/
noncomputable def gdStep (γ : ℝ) (f : E → ℝ) (x : E) : E :=
  x - γ • gradient f x

/-- §F2 sanity lemma: GD on a constant function is a no-op
    (the gradient is zero). -/
theorem gdStep_const (γ : ℝ) (c : ℝ) (x : E) :
    gdStep γ (fun _ : E => c) x = x := by
  unfold gdStep
  rw [gradient_fun_const]
  simp

/-- §F2 — GD step with zero step size is a no-op (any function). -/
theorem gdStep_zero_step (f : E → ℝ) (x : E) :
    gdStep (0 : ℝ) f x = x := by
  unfold gdStep
  simp

/-- §F2 — GD update increment formula. -/
theorem gdStep_eq (γ : ℝ) (f : E → ℝ) (x : E) :
    gdStep γ f x = x - γ • gradient f x := rfl

end LTFP
