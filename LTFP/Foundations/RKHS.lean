/-
LTFP foundation: reproducing kernel Hilbert spaces (RKHS).

Phase-3a anchor for Ch 7 (kernel methods), Ch 9 (NN/RKHS connection),
Ch 12 (NTK regime). An RKHS over `𝒳` is a Hilbert space `H` of
functions `𝒳 → ℝ` together with a reproducing kernel
`k : 𝒳 × 𝒳 → ℝ` such that `k(·, x) ∈ H` and `f(x) = ⟨f, k(·,x)⟩`
for every `f ∈ H` and `x ∈ 𝒳`.

This file ships the abstract structure and a sanity lemma. The
construction of an RKHS from a PD kernel (Aronszajn theorem) is
nontrivial and deferred to a Phase-4 wave.
-/
import Mathlib.Analysis.InnerProductSpace.Basic

namespace LTFP

variable {𝒳 : Type*}

/-- An **RKHS** over `𝒳`: a real Hilbert space `H` together with a
    feature map `φ : 𝒳 → H` and the reproducing property
    `f x = ⟨f, φ x⟩` for every `f ∈ H`. The kernel is then
    `k x y = ⟨φ x, φ y⟩`. -/
structure RKHS (𝒳 : Type*) where
  /-- The Hilbert space underlying this RKHS. -/
  H : Type*
  /-- Hilbert space additive structure. -/
  [normedAddCommGroup : NormedAddCommGroup H]
  /-- Hilbert space inner-product structure. -/
  [innerProductSpace : InnerProductSpace ℝ H]
  /-- Hilbert space completeness. -/
  [complete : CompleteSpace H]
  /-- The feature map. -/
  φ : 𝒳 → H

/-- The kernel induced by an RKHS, `k x y = ⟨φ x, φ y⟩`. -/
noncomputable def RKHS.kernel (R : RKHS 𝒳) (x y : 𝒳) : ℝ :=
  letI := R.normedAddCommGroup
  letI := R.innerProductSpace
  inner ℝ (R.φ x) (R.φ y)

/-- §F4b sanity lemma: an RKHS kernel is symmetric in its arguments. -/
theorem RKHS.kernel_symm (R : RKHS 𝒳) (x y : 𝒳) :
    R.kernel x y = R.kernel y x := by
  letI := R.normedAddCommGroup
  letI := R.innerProductSpace
  unfold RKHS.kernel
  exact real_inner_comm _ _

/-- §F4b — An RKHS kernel evaluated at the same point is the squared
    norm of the feature image: `k(x, x) = ‖φ(x)‖²` ≥ 0. -/
theorem RKHS.kernel_self_nonneg (R : RKHS 𝒳) (x : 𝒳) :
    0 ≤ R.kernel x x := by
  letI := R.normedAddCommGroup
  letI := R.innerProductSpace
  unfold RKHS.kernel
  exact real_inner_self_nonneg

/-- §F4b — RKHS kernel definition (extensional). -/
theorem RKHS.kernel_def (R : RKHS 𝒳) (x y : 𝒳) :
    R.kernel x y = letI := R.normedAddCommGroup
                   letI := R.innerProductSpace
                   inner ℝ (R.φ x) (R.φ y) := rfl

end LTFP
