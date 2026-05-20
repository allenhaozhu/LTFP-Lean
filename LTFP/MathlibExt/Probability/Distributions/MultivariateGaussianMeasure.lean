/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Multivariate Gaussian distribution as a `Measure` on `EuclideanSpace ℝ (Fin d)`

This file defines the `d`-dimensional Gaussian distribution `N(m, S)` on
`EuclideanSpace ℝ (Fin d)`, with mean `m : EuclideanSpace ℝ (Fin d)` and
positive-semidefinite covariance `S : Matrix (Fin d) (Fin d) ℝ`, as a
`MeasureTheory.Measure` object.

We use `S` rather than the symbol `Σ` for the covariance parameter,
since `Σ` is a reserved Lean keyword for sigma types.

## Construction (Cholesky-style pushforward)

The standard construction route — leveraging existing Mathlib
infrastructure for univariate Gaussian + product measures — is:

1. Start from the **standard normal product measure** on `Fin d → ℝ`,
   namely `Measure.pi (fun _ => gaussianReal 0 1)`.
2. Push forward through the measurable equivalence
   `MeasurableEquiv.toLp 2 (Fin d → ℝ)` to land on
   `EuclideanSpace ℝ (Fin d)`. This gives the **standard multivariate
   Gaussian** `stdMultivariateGaussian d`.
3. Push forward through the **affine map**
   `z ↦ m + (S.sqrt) · z`,
   where `S.sqrt := CFC.sqrt S` is the symmetric positive-semidefinite
   square root of `S`. By `CFC.sqrt_mul_sqrt_self`, this factor
   satisfies `S.sqrt * S.sqrt = S`. Since `S.sqrt` is self-adjoint over
   `ℝ`, this is equivalently `S.sqrt * S.sqrtᵀ = S` — the
   Cholesky-style factorization we need.

The route differs from the textbook Cholesky construction (which
produces a *lower-triangular* factor) only in that we use the
symmetric positive-semidefinite square root provided by the
continuous functional calculus. Either factorization works for the
distributional construction.

## Why not the explicit-PDF route?

An alternative construction is to define the distribution via the
explicit Gaussian PDF and `Measure.withDensity` of the Lebesgue measure
on `EuclideanSpace ℝ (Fin d)`. That route requires a Jacobian-determinant
computation and a multivariate change-of-variables theorem to verify the
normalization constant. The Cholesky pushforward route avoids those
computations by leveraging Mathlib's univariate `gaussianReal`
infrastructure.

## Main definitions

* `stdMultivariateGaussian d` — the standard `d`-variate Gaussian, i.e.
  the law of `d` independent standard normals, viewed as a probability
  measure on `EuclideanSpace ℝ (Fin d)`.
* `multivariateGaussian m S hS` — the `N(m, S)` distribution on
  `EuclideanSpace ℝ (Fin d)`, defined as the pushforward of the standard
  multivariate Gaussian through the affine map
  `z ↦ m + S.sqrt · z`.

## Main results

* `IsProbabilityMeasure (stdMultivariateGaussian d)` and
  `IsProbabilityMeasure (multivariateGaussian m S hS)` — both are
  probability measures.
* `integral_eval_multivariateGaussian` — coordinate-wise mean identity:
  `∫ x, x i ∂(multivariateGaussian m S hS) = m i` (after passing through
  the `ofLp` projection from `EuclideanSpace ℝ (Fin d)` to `Fin d → ℝ`).

## Future work

* Coordinate-wise covariance identity
  `∫ x, (x i - m i) * (x j - m j) ∂(multivariateGaussian m S hS) = S i j`.
  The proof requires a bilinear Fubini-style argument on the product
  measure side that goes substantially beyond the linear identity proved
  here; it is left to a follow-up file.

* `IsGaussian` instance. Mathlib provides
  `ProbabilityTheory.IsGaussian` for general Banach spaces, and a
  Gaussian measure on `EuclideanSpace ℝ (Fin d)` should satisfy this
  predicate. The witness theorem is that the pushforward through every
  continuous linear form is a `gaussianReal`, which in turn requires the
  per-coordinate covariance identity above plus a linear combination
  argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal MatrixOrder

namespace ProbabilityTheory

variable {d : ℕ}

/-! ### Standard multivariate Gaussian -/

/-- The **standard `d`-variate Gaussian** on `EuclideanSpace ℝ (Fin d)`,
defined as the pushforward of the product of `d` independent standard
normals on `Fin d → ℝ` through the canonical measurable equivalence
`Fin d → ℝ ≃ᵐ EuclideanSpace ℝ (Fin d)`. -/
def stdMultivariateGaussian (d : ℕ) : Measure (EuclideanSpace ℝ (Fin d)) :=
  (Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)).map (MeasurableEquiv.toLp 2 (Fin d → ℝ))

instance instIsProbabilityMeasureStdMultivariateGaussian (d : ℕ) :
    IsProbabilityMeasure (stdMultivariateGaussian d) := by
  unfold stdMultivariateGaussian
  exact Measure.isProbabilityMeasure_map
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.aemeasurable

/-- For the standard multivariate Gaussian, the integral of the `i`-th
coordinate (against the EuclideanSpace point) equals the integral of the
identity against a single standard normal, which is `0`. -/
lemma integral_eval_stdMultivariateGaussian (i : Fin d) :
    ∫ x, (WithLp.ofLp (p := 2) (V := Fin d → ℝ) x) i ∂(stdMultivariateGaussian d) = 0 := by
  -- Push forward to `Fin d → ℝ`, then use `integral_comp_eval` to reduce
  -- to a single standard-normal integral.
  have h1 :
      ∫ x, (WithLp.ofLp (p := 2) (V := Fin d → ℝ) x) i ∂(stdMultivariateGaussian d)
        = ∫ z, z i ∂(Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)) := by
    unfold stdMultivariateGaussian
    rw [integral_map (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.aemeasurable
        (by fun_prop)]
    -- After the rewrite, the goal is
    --   `∫ x : Fin d → ℝ, ((toLp 2 x).ofLp) i ∂(pi ...) = ∫ z, z i ∂(pi ...)`.
    -- This holds because `((toLp 2 x).ofLp) = x` definitionally
    -- (`WithLp.ofLp_toLp`).
    rfl
  rw [h1, integral_comp_eval (μ := fun _ : Fin d ↦ gaussianReal 0 1) (i := i)
        (f := fun z : ℝ ↦ z) (by fun_prop)]
  simp [integral_id_gaussianReal]

/-! ### Multivariate Gaussian with general mean and covariance -/

/-- The affine map `z ↦ m + L · z` on `EuclideanSpace ℝ (Fin d)`, as a
measurable function. We use `Matrix.toEuclideanCLM` to convert the
matrix `L` into a continuous linear map on `EuclideanSpace ℝ (Fin d)`. -/
def gaussianAffine (m : EuclideanSpace ℝ (Fin d)) (L : Matrix (Fin d) (Fin d) ℝ) :
    EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
  fun z ↦ m + Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) L z

lemma measurable_gaussianAffine (m : EuclideanSpace ℝ (Fin d))
    (L : Matrix (Fin d) (Fin d) ℝ) :
    Measurable (gaussianAffine m L) := by
  unfold gaussianAffine; fun_prop

lemma continuous_gaussianAffine (m : EuclideanSpace ℝ (Fin d))
    (L : Matrix (Fin d) (Fin d) ℝ) :
    Continuous (gaussianAffine m L) := by
  unfold gaussianAffine; fun_prop

@[simp] lemma gaussianAffine_apply (m : EuclideanSpace ℝ (Fin d))
    (L : Matrix (Fin d) (Fin d) ℝ) (z : EuclideanSpace ℝ (Fin d)) :
    gaussianAffine m L z =
      m + Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) L z := rfl

/-- The **multivariate Gaussian distribution** `N(m, S)` on
`EuclideanSpace ℝ (Fin d)`, with mean `m` and positive-semidefinite
covariance `S`. Defined as the pushforward of the standard multivariate
Gaussian through the affine map `z ↦ m + (CFC.sqrt S) · z`.

The `hS : S.PosSemidef` hypothesis is required at the type level even
though it does not appear in the computational content: it ensures that
`CFC.sqrt S` is the actual symmetric positive-semidefinite square root
(satisfying `CFC.sqrt_mul_sqrt_self : CFC.sqrt S * CFC.sqrt S = S`),
rather than an arbitrary application of the continuous functional
calculus. All theorems about this measure consume `hS`. -/
def multivariateGaussian (m : EuclideanSpace ℝ (Fin d))
    (S : Matrix (Fin d) (Fin d) ℝ) (_hS : S.PosSemidef) :
    Measure (EuclideanSpace ℝ (Fin d)) :=
  (stdMultivariateGaussian d).map (gaussianAffine m (CFC.sqrt S))

instance instIsProbabilityMeasureMultivariateGaussian
    (m : EuclideanSpace ℝ (Fin d)) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) :
    IsProbabilityMeasure (multivariateGaussian m S hS) := by
  unfold multivariateGaussian
  exact Measure.isProbabilityMeasure_map
    (measurable_gaussianAffine m (CFC.sqrt S)).aemeasurable

/-- The pushforward of `multivariateGaussian m S hS` through any
measurable function `f` factors through the standard multivariate
Gaussian and the affine map. -/
lemma map_multivariateGaussian
    {m : EuclideanSpace ℝ (Fin d)} {S : Matrix (Fin d) (Fin d) ℝ} {hS : S.PosSemidef}
    {β : Type*} [MeasurableSpace β] {f : EuclideanSpace ℝ (Fin d) → β} (hf : Measurable f) :
    (multivariateGaussian m S hS).map f
      = (stdMultivariateGaussian d).map (f ∘ gaussianAffine m (CFC.sqrt S)) := by
  unfold multivariateGaussian
  rw [Measure.map_map hf (measurable_gaussianAffine m (CFC.sqrt S))]

/-! ### Mean: coordinate-wise identity -/

/-- For each coordinate `i`, integrating the `i`-th component of `x`
against `multivariateGaussian m S hS` recovers `m i`. This is the
**vector-valued mean identity**, stated coordinatewise. -/
theorem integral_eval_multivariateGaussian
    (m : EuclideanSpace ℝ (Fin d)) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (i : Fin d) :
    ∫ x, (WithLp.ofLp (p := 2) (V := Fin d → ℝ) x) i ∂(multivariateGaussian m S hS)
      = (WithLp.ofLp (p := 2) (V := Fin d → ℝ) m) i := by
  classical
  -- Strategy: push forward through `gaussianAffine`, then expand the
  -- coordinate projection as `m i + ∑ j, A i j * z j` and use linearity.
  set ν : Measure (EuclideanSpace ℝ (Fin d)) := stdMultivariateGaussian d with hν
  set A : Matrix (Fin d) (Fin d) ℝ := CFC.sqrt S with hA
  unfold multivariateGaussian
  rw [integral_map (measurable_gaussianAffine m A).aemeasurable (by fun_prop)]
  -- Now the integral is `∫ z, (m + A·z) i ∂ν`. Expand pointwise.
  have hSplit : ∀ z : EuclideanSpace ℝ (Fin d),
      (WithLp.ofLp (p := 2) (V := Fin d → ℝ) (gaussianAffine m A z)) i
        = (WithLp.ofLp (p := 2) (V := Fin d → ℝ) m) i
            + ∑ j : Fin d, A i j *
                (WithLp.ofLp (p := 2) (V := Fin d → ℝ) z) j := by
    intro z
    -- Unfold `gaussianAffine` and use the fact that `ofLp` is additive
    -- and `ofLp (Matrix.toEuclideanCLM A z) = A *ᵥ ofLp z`.
    show (WithLp.ofLp (p := 2) (V := Fin d → ℝ)
          (m + Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A z)) i = _
    rw [WithLp.ofLp_add]
    rw [Matrix.ofLp_toEuclideanCLM]
    -- LHS is now `(ofLp m + A *ᵥ ofLp z) i = (ofLp m) i + (A *ᵥ ofLp z) i`.
    rw [Pi.add_apply]
    -- `(A *ᵥ ofLp z) i = ∑ j, A i j * (ofLp z) j` by definition of `mulVec`
    -- (which is the dot product of the `i`-th row of `A` with the vector).
    rfl

  -- Each summand `A i j * z j` integrates to `A i j * 0 = 0`.
  have hInt_zj : ∀ j : Fin d,
      ∫ z, (WithLp.ofLp (p := 2) (V := Fin d → ℝ) z) j ∂ν = 0 := by
    intro j; exact integral_eval_stdMultivariateGaussian (d := d) j
  -- Integrability of each `z ↦ z j` against the standard multivariate Gaussian.
  have hInt_int : ∀ j : Fin d,
      Integrable (fun z ↦ (WithLp.ofLp (p := 2) (V := Fin d → ℝ) z) j) ν := by
    intro j
    -- First: the identity is integrable against `gaussianReal 0 1`.
    have hIdInt : Integrable (fun x : ℝ ↦ x) (gaussianReal 0 1) := by
      rw [← memLp_one_iff_integrable]
      exact memLp_id_gaussianReal 1
    -- Second: lift to the product measure via `integrable_comp_eval`.
    have hPi : Integrable (fun z : Fin d → ℝ ↦ z j)
        (Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)) := by
      have := MeasureTheory.integrable_comp_eval
        (X := fun _ : Fin d ↦ ℝ) (μ := fun _ : Fin d ↦ gaussianReal 0 1)
        (i := j) (f := fun x : ℝ ↦ x) hIdInt
      exact this
    -- Third: transport along the pushforward
    -- `(Measure.pi ...).map (toLp 2 ...)`.
    show Integrable (fun z ↦ (WithLp.ofLp (p := 2) (V := Fin d → ℝ) z) j)
        (stdMultivariateGaussian d)
    unfold stdMultivariateGaussian
    rw [integrable_map_measure (by fun_prop)
        (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.aemeasurable]
    -- After the rewrite, the function becomes
    -- `fun z : Fin d → ℝ ↦ ((toLp 2 z).ofLp) j`, which is `fun z ↦ z j`.
    exact hPi
  -- Now compute the integral, using linearity.
  calc
    ∫ z, (WithLp.ofLp (p := 2) (V := Fin d → ℝ) (gaussianAffine m A z)) i ∂ν
        = ∫ z, ((WithLp.ofLp (p := 2) (V := Fin d → ℝ) m) i
            + ∑ j : Fin d, A i j *
                (WithLp.ofLp (p := 2) (V := Fin d → ℝ) z) j) ∂ν := by
          refine integral_congr_ae ?_
          refine Filter.Eventually.of_forall ?_
          intro z; exact hSplit z
      _ = (WithLp.ofLp (p := 2) (V := Fin d → ℝ) m) i
            + ∫ z, ∑ j : Fin d, A i j *
                (WithLp.ofLp (p := 2) (V := Fin d → ℝ) z) j ∂ν := by
          rw [integral_add (integrable_const _) ?_]
          · simp
          · refine integrable_finset_sum _ (fun j _ => ?_)
            exact (hInt_int j).const_mul (A i j)
      _ = (WithLp.ofLp (p := 2) (V := Fin d → ℝ) m) i
            + ∑ j : Fin d, A i j *
                ∫ z, (WithLp.ofLp (p := 2) (V := Fin d → ℝ) z) j ∂ν := by
          congr 1
          rw [integral_finset_sum _ (fun j _ => (hInt_int j).const_mul (A i j))]
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [integral_const_mul]
      _ = (WithLp.ofLp (p := 2) (V := Fin d → ℝ) m) i := by
          simp [hInt_zj]

end ProbabilityTheory

end
