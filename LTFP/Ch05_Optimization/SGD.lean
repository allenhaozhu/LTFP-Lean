/-
LTFP §5.4 — Stochastic gradient descent.

Bach (2024) §5.4, pp. 134-150. SGD replaces the full gradient
`∇f(xₜ)` with a stochastic estimator `gₜ` (typically the gradient
on a single sample `iₜ`). The expected update equals the true GD
update when `E[gₜ | xₜ] = ∇f(xₜ)` (unbiasedness).

We extend `LTFP.Foundations.StochasticGD`'s `sgdStep` with a
multi-step iterate and prove SGD with the zero estimator is a no-op.
-/
import LTFP.Foundations.StochasticGD

namespace LTFP

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- §5.4 — `T`-step iterate of SGD with stochastic gradient `g : E → E`. -/
def sgdIterate (γ : ℝ) (g : E → E) (x0 : E) : ℕ → E
  | 0 => x0
  | t + 1 => sgdStep γ g (sgdIterate γ g x0 t)

/-- §5.4 sanity lemma: SGD with the zero estimator leaves every iterate
    equal to `x₀`. -/
theorem sgdIterate_zero (γ : ℝ) (x0 : E) (t : ℕ) :
    sgdIterate γ (fun _ : E => (0 : E)) x0 t = x0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp [sgdIterate, ih, sgdStep_zero]

/-- §5.4 — SGD with zero step size is a no-op (any estimator). -/
theorem sgdIterate_zero_step (g : E → E) (x0 : E) (t : ℕ) :
    sgdIterate (0 : ℝ) g x0 t = x0 := by
  induction t with
  | zero => rfl
  | succ t ih =>
    simp [sgdIterate, sgdStep, ih]

end LTFP
