/-
LTFP foundation: stochastic gradient descent.

Phase-3a anchor for Ch 5 (SGD analysis), Ch 11 (online learning), Ch 12
(NN training). The SGD update with step `γ` and stochastic gradient
estimator `g` is `xₜ₊₁ = xₜ − γ · g(xₜ)`. The full expectation analysis
is deferred to Ch 5 itself.
-/
import Mathlib.Analysis.InnerProductSpace.Basic

namespace LTFP

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- §F3 — One step of stochastic gradient descent with stochastic
    gradient estimator `g : E → E`. -/
def sgdStep (γ : ℝ) (g : E → E) (x : E) : E :=
  x - γ • g x

/-- §F3 sanity lemma: SGD with the zero gradient estimator is a no-op. -/
theorem sgdStep_zero (γ : ℝ) (x : E) :
    sgdStep γ (fun _ : E => (0 : E)) x = x := by
  unfold sgdStep
  simp

/-- §F3 — SGD step with zero step size is a no-op (any estimator). -/
theorem sgdStep_zero_step (g : E → E) (x : E) :
    sgdStep (0 : ℝ) g x = x := by
  unfold sgdStep
  simp

/-- §F3 — Linearity in the gradient estimator. -/
theorem sgdStep_add_g (γ : ℝ) (g₁ g₂ : E → E) (x : E) :
    sgdStep γ (g₁ + g₂) x = sgdStep γ g₁ x - γ • g₂ x := by
  unfold sgdStep
  simp [Pi.add_apply, smul_add]
  abel

/-- §F3 — SGD update increment formula. -/
theorem sgdStep_eq (γ : ℝ) (g : E → E) (x : E) :
    sgdStep γ g x = x - γ • g x := rfl

end LTFP
