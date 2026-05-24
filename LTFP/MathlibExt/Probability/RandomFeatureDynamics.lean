/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import LTFP.MathlibExt.Probability.NTKConcentration

/-!
# Random-feature network model (B8 N5 / N6 shared dynamics, I1)

Shared primitive definitions for the **random-feature regime** of a
one-hidden-layer neural network, used as common substrate by both B8
N5 (lazy-training NTK analysis) and B8 N6 (sample-complexity analysis).

## What this file is — and what it is NOT

This file defines the **output-layer-only random-feature model**:
hidden weights `ω = (w_j, b_j)` are drawn i.i.d. from some
initialization measure and held fixed; only the output-layer weights
`a ∈ ℝᵐ` participate as a *parameter*. The map is

  `lazyNet σ ω a x = ⟨a, rfFeature σ ω x⟩`,
  `rfFeature σ ω x = (1 / √m) · (σ(⟨w_j, x⟩ + b_j))_{j=1..m}`.

This is **NOT** the full Bach lazy-NTK model, which freezes hidden
weights only at first order and tracks `θt = θ₀ + (θt − θ₀)`. The
random-feature model is the cleaner cousin: it is the first-order
linearization of the full network where the hidden-layer Jacobian is
not used. The label `RandomFeatureDynamics` is chosen for honesty —
downstream files that need the *full* lazy-NTK model must build on
top of `LTFP/MathlibExt/Probability/NTKLazyCarrier.lean`, not on this
file.

## Main definitions

* `rfFeature σ ω x : EuclideanSpace ℝ (Fin m)` — the
  `(1/√m)`-rescaled random-feature vector at input `x`.
* `lazyNet σ ω a x : ℝ` — the output-layer-only random-feature
  network, defined as the inner product `⟨a, rfFeature σ ω x⟩` in
  `EuclideanSpace ℝ (Fin m)`.

## Encoding choices

We construct the random-feature vector with `WithLp.toLp 2 (fun j => ...)`,
matching the existing pattern in `LTFP/Foundations/PseudoMetric.lean`,
`LTFP/MathlibExt/Probability/CoveringNumberEuclidean.lean`, etc.
`EuclideanSpace ℝ (Fin m)` is definitionally `PiLp 2 (fun _ : Fin m => ℝ)`,
so we use `WithLp.toLp` as the constructor.

The case `m = 0` is mathematically harmless in the raw definition
because `Real.sqrt 0 = 0` and Lean totalizes division; no conditional
guard is needed.

## Status

Primitive layer. Downstream carrier files (B8 N5/N6) import this file
rather than redefining the random-feature map.
-/

namespace ProbabilityTheory

open scoped RealInnerProductSpace

/-- **Random-feature map** at input `x`.

Given a bounded activation `σ : ℝ → ℝ` and a hidden-weight sample
`ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ` (each entry encoding a
weight-bias pair `(w_j, b_j)`), the random-feature vector at `x` is

  `(1 / √m) · (σ(⟨w_j, x⟩ + b_j))_{j=1..m} ∈ EuclideanSpace ℝ (Fin m)`.

This is the output of the (frozen) hidden layer, rescaled to keep the
output magnitude bounded as `m → ∞`. -/
noncomputable def rfFeature
    {d m : ℕ} (σ : ℝ → ℝ)
    (ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2
    (fun j : Fin m => (1 / Real.sqrt (m : ℝ)) *
      σ (inner ℝ (ω j).1 x + (ω j).2))

/-- **Output-layer-only random-feature network**.

Given hidden-weight sample `ω`, output-layer weights `a ∈ ℝᵐ`, and an
input `x`, the random-feature network output is the inner product of
`a` with the random-feature vector at `x`:

  `lazyNet σ ω a x = ⟨a, rfFeature σ ω x⟩
                   = (1/√m) · Σⱼ aⱼ · σ(⟨w_j, x⟩ + b_j)`.

This is the *random-feature regime* prediction; only `a` participates
as a tunable parameter. Cf. the *full* lazy-NTK model where hidden
weights are also (first-order) trainable, which is treated separately
in `LTFP/MathlibExt/Probability/NTKLazyCarrier.lean`. -/
noncomputable def lazyNet
    {d m : ℕ} (σ : ℝ → ℝ)
    (ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ)
    (a : EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  inner ℝ a (rfFeature σ ω x)

/-- **Coordinate-wise form of `rfFeature`.**

The `j`-th coordinate of the random-feature vector is
`(1/√m) · σ(⟨w_j, x⟩ + b_j)`. This is the canonical reduction back to
function form, useful for coordinate-wise arguments. -/
@[simp]
lemma rfFeature_apply
    {d m : ℕ} (σ : ℝ → ℝ)
    (ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (j : Fin m) :
    rfFeature σ ω x j
      = (1 / Real.sqrt (m : ℝ)) * σ (inner ℝ (ω j).1 x + (ω j).2) := rfl

/-- **Unfolded form of `lazyNet`.**

The lazy-network output equals the inner product of the output-layer
weights with the random-feature vector. This is definitionally the
defining equation; it is exposed as a lemma for downstream rewriting. -/
lemma lazyNet_apply
    {d m : ℕ} (σ : ℝ → ℝ)
    (ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ)
    (a : EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin d)) :
    lazyNet σ ω a x = inner ℝ a (rfFeature σ ω x) := rfl

/-! ### Shared dynamics (B8 N5 / N6, I2): differentiability and gradient

The output-layer-only random-feature network is **linear** in its
parameter `a`, hence smooth of every order; its gradient w.r.t. `a` is
the random-feature vector itself, independent of `a`. Stitching the
inner-product gradient against itself over a data tuple recovers the
empirical NTK matrix entry — this is the "Jacobian-to-empirical-NTK"
identity used by both the lazy-training (N5) and sample-complexity
(N6) analyses.
-/

section SharedDynamics

variable {d m : ℕ} (σ : ℝ → ℝ)
    (ω : Fin m → EuclideanSpace ℝ (Fin d) × ℝ)

/-- The parameter map `a ↦ lazyNet σ ω a x` agrees, as a function, with
the continuous linear map `innerSL ℝ (rfFeature σ ω x)`. Over `ℝ` the
inner product is symmetric, so `⟨a, v⟩ = ⟨v, a⟩` and the two presentations
coincide pointwise. -/
private lemma lazyNet_eq_innerSL_apply
    (x : EuclideanSpace ℝ (Fin d)) :
    (fun a : EuclideanSpace ℝ (Fin m) => lazyNet σ ω a x)
      = fun a => innerSL ℝ (rfFeature σ ω x) a := by
  funext a
  simp [lazyNet_apply, innerSL_apply_apply, real_inner_comm]

/-- **Smoothness in the parameter.** For any input `x`, the map
`a ↦ lazyNet σ ω a x` is `C²` (in fact `C^∞`) on the parameter space.
This is immediate from linearity: the lazy-network output is a continuous
linear functional in `a`. -/
theorem contDiff_lazyNet_param
    (x : EuclideanSpace ℝ (Fin d)) :
    ContDiff ℝ 2 (fun a : EuclideanSpace ℝ (Fin m) => lazyNet σ ω a x) := by
  rw [lazyNet_eq_innerSL_apply]
  exact (innerSL ℝ (rfFeature σ ω x)).contDiff

/-- **Gradient identity.** The gradient of `a ↦ lazyNet σ ω a x` at any
point `a` equals the random-feature vector `rfFeature σ ω x`. This is
the parameter-space Jacobian of the random-feature predictor. -/
theorem gradient_lazyNet_param
    (a : EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin d)) :
    gradient (fun a : EuclideanSpace ℝ (Fin m) => lazyNet σ ω a x) a
      = rfFeature σ ω x := by
  -- The lazy-network parameter map is, pointwise, the CLM
  -- `innerSL ℝ (rfFeature σ ω x)`, so it has Fréchet derivative equal
  -- to itself at every `a`.
  have hf : HasFDerivAt (fun a : EuclideanSpace ℝ (Fin m) => lazyNet σ ω a x)
      (innerSL ℝ (rfFeature σ ω x)) a := by
    rw [lazyNet_eq_innerSL_apply]
    exact (innerSL ℝ (rfFeature σ ω x)).hasFDerivAt
  -- Identify the CLM `innerSL ℝ v` with `toDual ℝ _ v` (these agree on
  -- the nose: both are `fun w => ⟪v, w⟫`).
  have hto : (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin m)))
      (rfFeature σ ω x) = innerSL ℝ (rfFeature σ ω x) := by
    apply ContinuousLinearMap.ext
    intro w
    simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]
  -- Convert to `HasGradientAt` and extract the gradient.
  have hg : HasGradientAt (fun a : EuclideanSpace ℝ (Fin m) => lazyNet σ ω a x)
      (rfFeature σ ω x) a := by
    rw [hasGradientAt_iff_hasFDerivAt, hto]
    exact hf
  exact hg.gradient

/-! ### Shared dynamics (B8 N5 / N6, I3): exact linearization and zero Hessian

Because the output-layer-only random-feature network is **linear** in
the parameter `a`, its first-order Taylor expansion at any base point
is *exact* (no remainder), and all higher-order Fréchet derivatives
vanish identically. These two facts — exact linearization and zero
Hessian — are the algebraic backbone of the lazy-training regime: in
the random-feature parametrization there is no nonlinearity in `a` to
control. -/

/-- **Exact linearization.** For the output-layer-only random-feature
network, the first-order Taylor expansion at any base point `a₀` is
*exact*:

  `lazyNet σ ω a₁ x = lazyNet σ ω a₀ x + ⟨∇_a (lazyNet σ ω · x) a₀, a₁ - a₀⟩`.

This holds because `a ↦ lazyNet σ ω a x` is a continuous linear
functional in `a`, so the Taylor remainder vanishes identically. -/
theorem lazyNet_exact_linearization
    (a₀ a₁ : EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin d)) :
    lazyNet σ ω a₁ x =
      lazyNet σ ω a₀ x +
        inner ℝ (gradient (fun a => lazyNet σ ω a x) a₀) (a₁ - a₀) := by
  -- Unfold both sides to inner products against `rfFeature σ ω x`.
  rw [lazyNet_apply, lazyNet_apply, gradient_lazyNet_param]
  -- Goal: ⟨a₁, rf⟩ = ⟨a₀, rf⟩ + ⟨rf, a₁ - a₀⟩.
  -- Use symmetry of the real inner product on the correction term,
  -- then distribute over subtraction.
  -- `real_inner_comm x y : ⟨y, x⟩ = ⟨x, y⟩`.
  have hcomm : inner ℝ (rfFeature σ ω x) (a₁ - a₀)
      = inner ℝ (a₁ - a₀) (rfFeature σ ω x) := real_inner_comm _ _
  rw [hcomm, inner_sub_left]
  ring

/-- **Zero Hessian.** The second Fréchet derivative of the output-layer-
only random-feature network with respect to its parameter is
identically zero, at every point and against every test pair. Combined
with `lazyNet_exact_linearization` this is the rigorous statement of
"the random-feature parametrization is exactly linear in `a`". -/
theorem lazyNet_hessian_zero
    (a : EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin d)) :
    iteratedFDeriv ℝ 2 (fun b => lazyNet σ ω b x) a = 0 := by
  -- Rewrite the parameter map as the CLM `innerSL ℝ (rfFeature σ ω x)`.
  rw [lazyNet_eq_innerSL_apply]
  -- The first Fréchet derivative of a CLM is the CLM itself — hence a
  -- constant function in `a`. Its second Fréchet derivative is therefore
  -- the iteratedFDeriv of a constant, which vanishes at any positive order.
  -- First, observe that `fun a => innerSL ℝ rf a` is the CLM `innerSL ℝ rf`
  -- itself (eta-expansion), so its fderiv is the CLM (a constant function
  -- of the base point).
  have hfderiv : ∀ b : EuclideanSpace ℝ (Fin m),
      fderiv ℝ (fun a : EuclideanSpace ℝ (Fin m) => innerSL ℝ (rfFeature σ ω x) a) b
        = innerSL ℝ (rfFeature σ ω x) := fun b =>
    (innerSL ℝ (rfFeature σ ω x)).fderiv
  -- Expand `iteratedFDeriv 2` as `fderiv (fderiv ...)` evaluated, and use
  -- the constancy of the inner `fderiv`.
  ext m₂
  rw [iteratedFDeriv_two_apply]
  -- The outer `fderiv` is applied to a function that is constantly equal
  -- to the CLM `innerSL ℝ rf`, so it vanishes by `fderiv_const`.
  have hconst :
      (fderiv ℝ (fun a : EuclideanSpace ℝ (Fin m) =>
          fderiv ℝ (fun a' : EuclideanSpace ℝ (Fin m) =>
              innerSL ℝ (rfFeature σ ω x) a') a) a)
        = 0 := by
    have hfun : (fun a : EuclideanSpace ℝ (Fin m) =>
          fderiv ℝ (fun a' : EuclideanSpace ℝ (Fin m) =>
              innerSL ℝ (rfFeature σ ω x) a') a)
        = fun _ : EuclideanSpace ℝ (Fin m) =>
            (innerSL ℝ (rfFeature σ ω x) :
              EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) := by
      funext b; exact hfderiv b
    rw [hfun]
    exact fderiv_const_apply _
  rw [hconst]
  simp

/-- **Jacobian-to-empirical-NTK identity.** Stitching the
parameter-space gradient against itself across a pair of inputs
`(xs r, xs s)` reconstructs the empirical NTK matrix entry:

  `⟨∇_a f(a, xs r), ∇_a f(a, xs s)⟩ = K̂(r, s)`.

This is the cleaner-than-full-NTK random-feature analogue of the
Neural Tangent Kernel: the matrix `(⟨∇f_r, ∇f_s⟩)_{r,s}` equals the
width-`m` empirical NTK with `(1/m)` normalization, where the
hidden-Jacobian contribution is collapsed to the identity (since only
the output layer is trainable).

The `0 < m` hypothesis is used to convert the per-coordinate `(1/√m)`
prefactor into the `(1/m)` prefactor of `empiricalNTK` via
`Real.mul_self_sqrt`. -/
theorem lazyNet_jacobian_gram_eq_empiricalNTK
    {n : ℕ} (xs : Fin n → EuclideanSpace ℝ (Fin d)) (hm : 0 < m)
    (r s : Fin n) :
    inner ℝ (rfFeature σ ω (xs r)) (rfFeature σ ω (xs s))
      = empiricalNTK σ xs ω r s := by
  -- Unpack inner product on `EuclideanSpace` to a coordinate sum, then
  -- unfold each side to a Σⱼ form.
  have h_sqrt_pos : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm.le
  have h_sq : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) :=
    Real.mul_self_sqrt h_sqrt_pos
  have hm_ne : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  -- The outer inner product on `EuclideanSpace ℝ (Fin m)` is a sum of
  -- products of real coordinates (since `⟪a, b⟫ = ∑ j, a j * b j` over `ℝ`).
  -- The RHS `empiricalNTK` is `(1/m) * Σⱼ σ(...) * σ(...)`.
  rw [PiLp.inner_apply,
      show empiricalNTK σ xs ω r s
        = (1 / (m : ℝ)) * ∑ j, neuronNTK σ (xs r) (xs s) (ω j) from rfl,
      Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  -- LHS coord: ⟪(1/√m) σ(⟨w_j, xs r⟩+b_j), (1/√m) σ(⟨w_j, xs s⟩+b_j)⟫ in ℝ
  -- RHS coord: (1/m) * (σ(⟨w_j, xs r⟩+b_j) * σ(⟨w_j, xs s⟩+b_j))
  simp only [rfFeature_apply, RCLike.inner_apply, conj_trivial]
  unfold neuronNTK
  -- Both sides are polynomial in (1/√m), σ-values, and m. Use h_sq to
  -- collapse (1/√m)² to 1/m. The σ-values may appear in either order.
  have h_inv_sq : (1 / Real.sqrt (m : ℝ)) * (1 / Real.sqrt (m : ℝ))
      = 1 / (m : ℝ) := by
    rw [one_div, one_div, ← mul_inv, h_sq, ← one_div]
  have key : ∀ A B : ℝ,
      (1 / Real.sqrt (m : ℝ) * A) * (1 / Real.sqrt (m : ℝ) * B)
        = 1 / (m : ℝ) * (B * A) := by
    intro A B
    calc (1 / Real.sqrt (m : ℝ) * A) * (1 / Real.sqrt (m : ℝ) * B)
        = (1 / Real.sqrt (m : ℝ) * (1 / Real.sqrt (m : ℝ))) * (B * A) := by ring
      _ = 1 / (m : ℝ) * (B * A) := by rw [h_inv_sq]
  exact key _ _

/-! ### Shared dynamics (B8 N5 / N6, I4): frozen-kernel dynamics interface

The output-layer-only random-feature network has a **frozen training
kernel**: the matrix of gradient inner products

  `(K_a)_{r,s} = ⟨∇_a f(a, xs r), ∇_a f(a, xs s)⟩`

is independent of `a` (since the gradient `∇_a f(a, x) = rfFeature σ ω x`
doesn't depend on `a`), and coincides exactly with the empirical NTK
matrix. This is the rigorous "lazy training" statement: the kernel
governing the dynamics is frozen at any reference point and equals the
canonical empirical NTK. -/

/-- **Training kernel.** The Gram matrix of gradients of the lazy network
with respect to the parameter `a`, evaluated at a tuple `xs` of inputs:

  `trainingKernel σ ω a xs (r, s) = ⟨∇_a (lazyNet σ ω · (xs r)) a,
                                     ∇_a (lazyNet σ ω · (xs s)) a⟩`.

This is the parameter-space kernel that governs first-order training
dynamics of the random-feature network. -/
noncomputable def trainingKernel
    {n : ℕ} (a : EuclideanSpace ℝ (Fin m))
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun r s =>
    inner ℝ
      (gradient (fun b : EuclideanSpace ℝ (Fin m) => lazyNet σ ω b (xs r)) a)
      (gradient (fun b : EuclideanSpace ℝ (Fin m) => lazyNet σ ω b (xs s)) a)

/-- **Training kernel equals empirical NTK.** For any reference point
`a` and any positive width `m`, the gradient Gram matrix coincides
exactly with the empirical NTK matrix. This identifies the canonical
kernel governing random-feature training dynamics with the standard
empirical NTK object. -/
theorem trainingKernel_eq_empiricalNTK
    {n : ℕ} (a : EuclideanSpace ℝ (Fin m))
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) (hm : 0 < m) :
    trainingKernel σ ω a xs = empiricalNTK σ xs ω := by
  apply Matrix.ext
  intro r s
  unfold trainingKernel
  rw [gradient_lazyNet_param, gradient_lazyNet_param]
  exact lazyNet_jacobian_gram_eq_empiricalNTK σ ω xs hm r s

/-- **Frozen kernel: stability across reference points.** The training
kernel is independent of the reference parameter `a`. In particular,
for any two reference points `a₀, aₜ` (e.g., initial and time-`t`
parameters), the kernel evaluated at `aₜ` equals the kernel evaluated
at `a₀`. This is the algebraic essence of "lazy training": the kernel
driving the dynamics never updates. No positivity hypothesis on `m` is
required — the result holds for `m = 0` as well, since the gradient
itself is independent of `a`. -/
theorem trainingKernel_stable
    {n : ℕ} (a₀ aₜ : EuclideanSpace ℝ (Fin m))
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) :
    trainingKernel σ ω aₜ xs = trainingKernel σ ω a₀ xs := by
  apply Matrix.ext
  intro r s
  unfold trainingKernel
  rw [gradient_lazyNet_param, gradient_lazyNet_param,
      gradient_lazyNet_param, gradient_lazyNet_param]

end SharedDynamics

end ProbabilityTheory
