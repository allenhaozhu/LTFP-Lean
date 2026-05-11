/-
LTFP foundation: convex analysis (re-exports Mathlib).

Phase-3a anchor for chapters that need convex sets, convex /
strongly-convex / smooth functions, and the gradient calculus on
them: Ch 4 (surrogates), Ch 5 (gradient methods), Ch 7 (KRR),
Ch 8 (Lasso), Ch 11 (OGD), Ch 13 (structured prediction).

Most content here is a thin LTFP-namespace alias over Mathlib's
`Analysis.Convex` and `Analysis.Calculus.Gradient` modules — we
**reuse, do not reinvent**.
-/
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Calculus.Gradient.Basic

namespace LTFP

open scoped Convex

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

/-- LTFP alias: a function `f : E → ℝ` is **`L`-smooth** when its
    gradient is `L`-Lipschitz. We do not unfold the Mathlib
    `LipschitzWith` machinery here; downstream chapters refer to
    `IsLSmooth` and discharge it via Mathlib lemmas as needed. -/
def IsLSmooth (L : NNReal) (f : E → ℝ) : Prop :=
  LipschitzWith L (gradient f)

/-- §F1 sanity lemma: a constant function is `0`-smooth.
    The gradient of a constant is `0`, which is `0`-Lipschitz. -/
theorem isLSmooth_const (c : ℝ) : IsLSmooth (0 : NNReal) (fun _ : E => c) := by
  unfold IsLSmooth
  have hgrad : gradient (fun _ : E => c) = 0 := by
    funext x
    exact gradient_fun_const x c
  rw [hgrad]
  exact LipschitzWith.const' 0

/-- §F1 — μ-strong convexity predicate.  We say `f` is `μ`-strongly
    convex if `f y ≥ f x + ⟨∇f(x), y-x⟩ + (μ/2) ‖y-x‖²` for all `x, y`. -/
def IsMuStronglyConvex (μ : ℝ) (f : E → ℝ) : Prop :=
  ∀ x y, f x + inner ℝ (gradient f x) (y - x) + (μ / 2) * ‖y - x‖^2 ≤ f y

/-- §F1 sanity lemma: every function is 0-strongly convex iff it
    satisfies the (degenerate) inequality `f x + ⟨∇f(x), y-x⟩ ≤ f y`,
    which is just convexity in the gradient sense. We illustrate with
    the trivial case μ = 0 for constant functions. -/
theorem isMuStronglyConvex_zero_of_const (c : ℝ) :
    IsMuStronglyConvex 0 (fun _ : E => c) := by
  intro x y
  have hgrad : gradient (fun _ : E => c) x = 0 := gradient_fun_const x c
  rw [hgrad]
  simp

/-- §F1 — Constant functions are 0-smooth via direct LipschitzWith. -/
theorem isLSmooth_zero (f : E → ℝ) (hgrad : gradient f = 0) :
    IsLSmooth (0 : NNReal) f := by
  unfold IsLSmooth
  rw [hgrad]
  exact LipschitzWith.const' 0

/-- §F1 — L-smoothness is monotone in `L`: if `f` is `L`-smooth and
    `L ≤ L'`, then `f` is `L'`-smooth. -/
theorem IsLSmooth.mono {L L' : NNReal} {f : E → ℝ}
    (hf : IsLSmooth L f) (hLL' : L ≤ L') : IsLSmooth L' f :=
  hf.weaken hLL'

/-- §F1 — A constant function is `L`-smooth for every nonneg `L`. -/
theorem isLSmooth_const_any (c : ℝ) (L : NNReal) :
    IsLSmooth L (fun _ : E => c) :=
  (isLSmooth_const c).mono (zero_le _)

end LTFP
