/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Sqrt

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

end ProbabilityTheory
