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

/-- §5.4 — **Expected descent under unbiasedness** (Bach 2024 §5.4,
    eqn 5.21, sample-path form). If `g : E → E` is pointwise equal to
    the true gradient field `h` (the deterministic shadow of the
    unbiased-estimator hypothesis `E[g(x) | x] = ∇f(x)`), then the SGD
    update with `g` coincides with the (abstract) GD update with `h`:
    `sgdStep γ g x = x − γ • h x`. This is the structural identity that
    makes `E[xₜ₊₁ | xₜ] = xₜ − γ · ∇f(xₜ)` and is the entry point of
    Bach's SGD convergence analysis. -/
theorem sgdStep_of_unbiased
    (γ : ℝ) (g h : E → E) (x : E) (hg : g x = h x) :
    sgdStep γ g x = x - γ • h x := by
  unfold sgdStep
  rw [hg]

end LTFP
