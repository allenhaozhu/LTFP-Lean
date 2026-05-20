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
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Topology.Algebra.Module.FiniteDimension

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

* `covariance_multivariateGaussian` — coordinate-wise covariance
  identity:
  `∫ x, (x i - m i) * (x j - m j) ∂(multivariateGaussian m S hS) = S i j`,
  proved via a bilinear Fubini-style argument on the standard product
  measure plus the matrix algebra identity
  `(CFC.sqrt S) * (CFC.sqrt S) = S`.

## Future work

* `IsGaussian` instance. Mathlib provides
  `ProbabilityTheory.IsGaussian` for general Banach spaces, and a
  Gaussian measure on `EuclideanSpace ℝ (Fin d)` should satisfy this
  predicate. The witness theorem is that the pushforward through every
  continuous linear form is a `gaussianReal`, which in turn requires
  the per-coordinate covariance identity proved here plus an
  `IsGaussian (Measure.pi (gaussianReal 0 1))` instance currently
  missing from Mathlib.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal MatrixOrder Matrix

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

/-! ### Second moments of the standard product measure

The bilinear Fubini computation behind the covariance identity lives
on the product-measure side `Measure.pi (gaussianReal 0 1)`. We
isolate the two cases (`j = k`, `j ≠ k`) here so the final pushforward
proof is purely matrix algebra. -/

/-- Second moment of a single coordinate of the standard product
measure: the identity in `ℝ` has variance `1` under `gaussianReal 0 1`,
which by `integral_comp_eval` becomes
`∫ z, (z j)^2 ∂(pi (gaussianReal 0 1)) = 1`. -/
lemma integral_sq_eval_pi_gaussianReal (j : Fin d) :
    ∫ z : Fin d → ℝ, (z j) ^ 2 ∂(Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)) = 1 := by
  -- Step 1: reduce to the univariate integral via `integral_comp_eval`.
  rw [integral_comp_eval (μ := fun _ : Fin d ↦ gaussianReal 0 1) (i := j)
        (f := fun x : ℝ ↦ x ^ 2) (by fun_prop)]
  -- Step 2: ∫ x ^ 2 ∂(gaussianReal 0 1) = Var[id; gaussianReal 0 1] = 1.
  have hMean : ∫ x : ℝ, x ∂(gaussianReal 0 1) = 0 :=
    integral_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
  have hVar : ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) = ((1 : ℝ≥0) : ℝ) := by
    have h1 : Var[fun x : ℝ ↦ x; gaussianReal 0 1] = ((1 : ℝ≥0) : ℝ) :=
      variance_fun_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
    have h2 : Var[fun x : ℝ ↦ x; gaussianReal 0 1]
        = ∫ x : ℝ, x ^ 2 ∂(gaussianReal 0 1) := by
      have := variance_of_integral_eq_zero (X := fun x : ℝ ↦ x)
        (μ := gaussianReal 0 1) measurable_id.aemeasurable hMean
      simpa using this
    linarith [h1.symm.trans h2]
  simpa using hVar

/-- Cross-product of two distinct coordinates of the standard product
measure vanishes: by Fubini (`integral_fintype_prod_eq_prod`), the
integral factors into a product over `Fin d` whose `i`-th factor is
`∫ x ∂(gaussianReal 0 1) = 0`. -/
lemma integral_mul_eval_pi_gaussianReal (j k : Fin d) (hjk : j ≠ k) :
    ∫ z : Fin d → ℝ, (z j) * (z k)
       ∂(Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)) = 0 := by
  classical
  -- Encode `z j * z k` as `∏ m : Fin d, f m (z m)` with
  --   f j = id, f k = id, f m = const 1 otherwise.
  set f : Fin d → ℝ → ℝ :=
    fun m x => if m = j then x else if m = k then x else 1 with hf_def
  have hProd : ∀ z : Fin d → ℝ, (∏ m, f m (z m)) = z j * z k := by
    intro z
    -- Split the product into the singleton `{j}`, the singleton `{k}`,
    -- and the rest, then evaluate each piece.
    have hjk' : j ∉ ({k} : Finset (Fin d)) := by simpa using hjk
    have hj_mem : j ∈ Finset.univ (α := Fin d) := Finset.mem_univ _
    have hk_mem : k ∈ Finset.univ (α := Fin d) := Finset.mem_univ _
    -- We compute directly using `Finset.prod_eq_mul_prod_diff_singleton`.
    have hsplit_j :
        (∏ m ∈ Finset.univ (α := Fin d), f m (z m))
          = f j (z j) * ∏ m ∈ (Finset.univ.erase j), f m (z m) := by
      rw [← Finset.mul_prod_erase _ _ hj_mem]
    have hsplit_k :
        (∏ m ∈ (Finset.univ.erase j), f m (z m))
          = f k (z k) * ∏ m ∈ (Finset.univ.erase j).erase k, f m (z m) := by
      have hk_mem' : k ∈ Finset.univ.erase j := by
        rw [Finset.mem_erase]; exact ⟨hjk.symm, hk_mem⟩
      rw [← Finset.mul_prod_erase _ _ hk_mem']
    have hOnes : ∀ m ∈ (Finset.univ.erase j).erase k, f m (z m) = 1 := by
      intro m hm
      rw [Finset.mem_erase, Finset.mem_erase] at hm
      obtain ⟨hmk, hmj, _⟩ := hm
      simp [f, hmj, hmk]
    have hRest : (∏ m ∈ (Finset.univ.erase j).erase k, f m (z m)) = 1 := by
      exact Finset.prod_eq_one hOnes
    rw [hsplit_j, hsplit_k, hRest, mul_one]
    simp [f]
  -- Rewrite the integrand and apply Fubini.
  calc
    ∫ z : Fin d → ℝ, (z j) * (z k)
        ∂(Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1))
        = ∫ z : Fin d → ℝ, ∏ m, f m (z m)
            ∂(Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)) := by
          refine integral_congr_ae (.of_forall ?_)
          intro z
          show z j * z k = ∏ m, f m (z m)
          exact (hProd z).symm
    _ = ∏ m, ∫ x : ℝ, f m x ∂(gaussianReal 0 1) := by
          exact integral_fintype_prod_eq_prod (μ := fun _ : Fin d ↦ gaussianReal 0 1) f
    _ = 0 := by
          -- The `j`-th factor of the product equals `∫ x d(gaussianReal 0 1) = 0`,
          -- which collapses the whole product.
          have hj_val : ∫ x : ℝ, f j x ∂(gaussianReal 0 1) = 0 := by
            simp only [f, if_pos rfl]
            exact integral_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))
          refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
          exact hj_val

/-! ### Second moments of the standard multivariate Gaussian -/

/-- Coordinate-wise second moment of the standard multivariate
Gaussian: distinct coordinates are uncorrelated, identical coordinates
have variance one. -/
theorem integral_eval_mul_eval_stdMultivariateGaussian (i j : Fin d) :
    ∫ x, (WithLp.ofLp (p := 2) (V := Fin d → ℝ) x) i
         * (WithLp.ofLp (p := 2) (V := Fin d → ℝ) x) j ∂(stdMultivariateGaussian d)
      = if i = j then 1 else 0 := by
  classical
  -- Pull back to the product measure.
  have hPull :
      ∫ x, (WithLp.ofLp (p := 2) (V := Fin d → ℝ) x) i
           * (WithLp.ofLp (p := 2) (V := Fin d → ℝ) x) j ∂(stdMultivariateGaussian d)
        = ∫ z : Fin d → ℝ, z i * z j
            ∂(Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)) := by
    unfold stdMultivariateGaussian
    rw [integral_map (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.aemeasurable
        (by fun_prop)]
    rfl
  rw [hPull]
  by_cases hij : i = j
  · -- Diagonal: i = j. Use the variance identity.
    subst hij
    have hsq : ∀ z : Fin d → ℝ, z i * z i = (z i) ^ 2 := by
      intro z; ring
    have :
        ∫ z : Fin d → ℝ, z i * z i
          ∂(Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1))
          = ∫ z : Fin d → ℝ, (z i) ^ 2
            ∂(Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)) := by
      refine integral_congr_ae (.of_forall ?_)
      intro z; exact hsq z
    rw [this, integral_sq_eval_pi_gaussianReal (d := d) i]
    simp
  · -- Off-diagonal: i ≠ j. Use the independence identity.
    rw [integral_mul_eval_pi_gaussianReal (d := d) i j hij]
    simp [hij]

/-! ### Covariance identity for the multivariate Gaussian -/

/-- For each pair of coordinates `(i, j)`, the centered cross-moment
`∫ (x i - m i) * (x j - m j) ∂(N(m, S))` equals the `(i, j)` entry of
`S`.

The proof has three pieces:

1. Push forward through the affine map `z ↦ m + L · z`, where
   `L = CFC.sqrt S`, so the integrand becomes `(L · z) i * (L · z) j`.
2. Expand the coordinate products as a bilinear double sum
   `∑ k l, L i k * L j l * z k * z l`, integrate, and use the
   second-moment identity for the standard product measure to collapse
   to `∑ k, L i k * L j k`.
3. Identify `∑ k, L i k * L j k` with the `(i, j)` entry of
   `L * L = (CFC.sqrt S) * (CFC.sqrt S) = S` via
   `CFC.sqrt_mul_sqrt_self`. Self-adjointness of `CFC.sqrt S`
   (`PosSemidef`) is what lets `L * L^T = L * L`. -/
theorem covariance_multivariateGaussian
    (m : EuclideanSpace ℝ (Fin d)) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (i j : Fin d) :
    ∫ x, ((WithLp.ofLp (p := 2) (V := Fin d → ℝ) x) i
           - (WithLp.ofLp (p := 2) (V := Fin d → ℝ) m) i)
         * ((WithLp.ofLp (p := 2) (V := Fin d → ℝ) x) j
           - (WithLp.ofLp (p := 2) (V := Fin d → ℝ) m) j)
       ∂(multivariateGaussian m S hS) = S i j := by
  classical
  set ν : Measure (EuclideanSpace ℝ (Fin d)) := stdMultivariateGaussian d with hν
  set L : Matrix (Fin d) (Fin d) ℝ := CFC.sqrt S with hL
  -- Step 1: push forward through the affine map.
  unfold multivariateGaussian
  rw [integral_map (measurable_gaussianAffine m L).aemeasurable (by fun_prop)]
  -- The integrand becomes (after the affine substitution)
  --   ((m + L · z) i - m i) * ((m + L · z) j - m j) = (L · z) i * (L · z) j.
  have hCenter : ∀ z : EuclideanSpace ℝ (Fin d),
      ((WithLp.ofLp (p := 2) (V := Fin d → ℝ) (gaussianAffine m L z)) i
         - (WithLp.ofLp (p := 2) (V := Fin d → ℝ) m) i)
       * ((WithLp.ofLp (p := 2) (V := Fin d → ℝ) (gaussianAffine m L z)) j
         - (WithLp.ofLp (p := 2) (V := Fin d → ℝ) m) j)
        = (L *ᵥ WithLp.ofLp (p := 2) (V := Fin d → ℝ) z) i
            * (L *ᵥ WithLp.ofLp (p := 2) (V := Fin d → ℝ) z) j := by
    intro z
    have hUnfold :
        WithLp.ofLp (p := 2) (V := Fin d → ℝ) (gaussianAffine m L z)
          = WithLp.ofLp (p := 2) (V := Fin d → ℝ) m
              + (L *ᵥ WithLp.ofLp (p := 2) (V := Fin d → ℝ) z) := by
      unfold gaussianAffine
      rw [WithLp.ofLp_add, Matrix.ofLp_toEuclideanCLM]
    rw [hUnfold]
    -- (a + b) - a = b in each coordinate
    rw [Pi.add_apply, Pi.add_apply]
    ring
  -- Step 2: rewrite as ∑ k ∑ l, L_ik * L_jl * z_k * z_l, then integrate term-by-term.
  -- We bundle the bilinear expansion into a single function and then split using
  -- coordinate-wise linearity of the integral.
  have hBilin : ∀ z : EuclideanSpace ℝ (Fin d),
      (L *ᵥ WithLp.ofLp (p := 2) (V := Fin d → ℝ) z) i
        * (L *ᵥ WithLp.ofLp (p := 2) (V := Fin d → ℝ) z) j
        = ∑ k, ∑ l, (L i k * L j l)
            * ((WithLp.ofLp (p := 2) (V := Fin d → ℝ) z) k
              * (WithLp.ofLp (p := 2) (V := Fin d → ℝ) z) l) := by
    intro z
    -- (L *ᵥ v) i = ∑ k, L i k * v k by definition of `mulVec`.
    have hi : (L *ᵥ WithLp.ofLp (p := 2) (V := Fin d → ℝ) z) i
                = ∑ k, L i k * (WithLp.ofLp (p := 2) (V := Fin d → ℝ) z) k := by
      simp [Matrix.mulVec, dotProduct]
    have hj : (L *ᵥ WithLp.ofLp (p := 2) (V := Fin d → ℝ) z) j
                = ∑ l, L j l * (WithLp.ofLp (p := 2) (V := Fin d → ℝ) z) l := by
      simp [Matrix.mulVec, dotProduct]
    rw [hi, hj, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    refine Finset.sum_congr rfl ?_
    intro l _
    ring
  -- The integrability we need for the bilinear sum: each summand
  --   z ↦ z k * z l
  -- is integrable against ν. This follows because the L^2 norm of `id` against
  -- `gaussianReal 0 1` is finite.
  have hIntZkZl : ∀ k l : Fin d,
      Integrable (fun z : EuclideanSpace ℝ (Fin d) =>
        (WithLp.ofLp (p := 2) (V := Fin d → ℝ) z) k
          * (WithLp.ofLp (p := 2) (V := Fin d → ℝ) z) l) ν := by
    intro k l
    -- Reduce to the product measure side.
    -- For each coordinate `j`, `(z j)^2` is integrable against the product
    -- measure (via `integrable_comp_eval` and univariate L^2). Then
    -- `|z k * z l| ≤ ((z k)^2 + (z l)^2) / 2` by AM-GM gives integrability of
    -- the product.
    have hIdSqInt : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) := by
      have : MemLp (fun x : ℝ => x) 2 (gaussianReal 0 1) := by
        simpa using memLp_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) 2
      -- `MemLp f 2 μ ↔ Integrable (fun x ↦ f x ^ 2)` (modulo absolute values)
      have hMul := MemLp.integrable_mul this this
      simpa [sq, mul_comm] using hMul
    -- The function `z ↦ (z k)^2` is integrable against the product measure.
    have hPiSqZk : Integrable (fun z : Fin d → ℝ => (z k) ^ 2)
        (Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)) := by
      exact integrable_comp_eval (μ := fun _ : Fin d ↦ gaussianReal 0 1)
        (i := k) (f := fun x : ℝ => x ^ 2) hIdSqInt
    have hPiSqZl : Integrable (fun z : Fin d → ℝ => (z l) ^ 2)
        (Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)) := by
      exact integrable_comp_eval (μ := fun _ : Fin d ↦ gaussianReal 0 1)
        (i := l) (f := fun x : ℝ => x ^ 2) hIdSqInt
    -- Use AM-GM: |a * b| ≤ (a^2 + b^2) / 2, so the product is bounded by a
    -- linear combination of integrable squares.
    have hPiMul : Integrable (fun z : Fin d → ℝ => z k * z l)
        (Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)) := by
      have hAEMeas : AEStronglyMeasurable (fun z : Fin d → ℝ => z k * z l)
          (Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)) := by
        refine AEStronglyMeasurable.mul ?_ ?_
        · exact (measurable_pi_apply k).aestronglyMeasurable
        · exact (measurable_pi_apply l).aestronglyMeasurable
      refine ⟨hAEMeas, ?_⟩
      -- Show finite L^1-norm via bound by `a^2 + b^2`.
      have hBound : ∀ z : Fin d → ℝ,
          ‖z k * z l‖ ≤ ‖(z k) ^ 2 + (z l) ^ 2‖ := by
        intro z
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
        have habs_sum_nn : 0 ≤ (z k) ^ 2 + (z l) ^ 2 := by positivity
        rw [abs_of_nonneg habs_sum_nn]
        nlinarith [sq_abs (z k), sq_abs (z l), sq_nonneg (|z k| - |z l|)]
      have hSumInt : Integrable (fun z : Fin d → ℝ => (z k) ^ 2 + (z l) ^ 2)
          (Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)) := hPiSqZk.add hPiSqZl
      exact (hSumInt.mono hAEMeas (.of_forall hBound)).hasFiniteIntegral
    -- Transport along the toLp pushforward.
    show Integrable (fun z =>
        (WithLp.ofLp (p := 2) (V := Fin d → ℝ) z) k
          * (WithLp.ofLp (p := 2) (V := Fin d → ℝ) z) l) (stdMultivariateGaussian d)
    unfold stdMultivariateGaussian
    rw [integrable_map_measure (by fun_prop)
        (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.aemeasurable]
    exact hPiMul
  -- Step 2 done. Now compute the integral as a double sum.
  calc
    ∫ z, ((WithLp.ofLp (p := 2) (V := Fin d → ℝ) (gaussianAffine m L z)) i
           - (WithLp.ofLp (p := 2) (V := Fin d → ℝ) m) i)
         * ((WithLp.ofLp (p := 2) (V := Fin d → ℝ) (gaussianAffine m L z)) j
           - (WithLp.ofLp (p := 2) (V := Fin d → ℝ) m) j) ∂ν
        = ∫ z, ∑ k, ∑ l, (L i k * L j l)
            * ((WithLp.ofLp (p := 2) (V := Fin d → ℝ) z) k
              * (WithLp.ofLp (p := 2) (V := Fin d → ℝ) z) l) ∂ν := by
          refine integral_congr_ae (.of_forall ?_)
          intro z
          show ((WithLp.ofLp (p := 2) (V := Fin d → ℝ) (gaussianAffine m L z)) i
                  - (WithLp.ofLp (p := 2) (V := Fin d → ℝ) m) i)
               * ((WithLp.ofLp (p := 2) (V := Fin d → ℝ) (gaussianAffine m L z)) j
                  - (WithLp.ofLp (p := 2) (V := Fin d → ℝ) m) j)
                = _
          rw [hCenter z, hBilin z]
    _ = ∑ k, ∑ l, (L i k * L j l) *
            ∫ z, ((WithLp.ofLp (p := 2) (V := Fin d → ℝ) z) k
              * (WithLp.ofLp (p := 2) (V := Fin d → ℝ) z) l) ∂ν := by
          -- Linearity: pull both sums and the constant factor through the integral.
          rw [integral_finset_sum _ ?_]
          · refine Finset.sum_congr rfl ?_
            intro k _
            rw [integral_finset_sum _ ?_]
            · refine Finset.sum_congr rfl ?_
              intro l _
              rw [integral_const_mul]
            · intro l _
              exact (hIntZkZl k l).const_mul _
          · intro k _
            refine integrable_finset_sum _ ?_
            intro l _
            exact (hIntZkZl k l).const_mul _
    _ = ∑ k, ∑ l, (L i k * L j l) * (if k = l then 1 else 0) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          refine Finset.sum_congr rfl ?_
          intro l _
          rw [integral_eval_mul_eval_stdMultivariateGaussian (d := d) k l]
    _ = ∑ k, L i k * L j k := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [Finset.sum_eq_single k]
          · simp
          · intro l _ hlk
            simp [hlk.symm]
          · intro hk
            exact (hk (Finset.mem_univ k)).elim
    _ = S i j := by
          -- Use the matrix identity (L * L^T)_ij = ∑ k, L i k * L j k together with
          -- L^T = L (real-valued Hermitian) and L * L = S (CFC.sqrt_mul_sqrt_self).
          have hSqrtPosSemidef : (CFC.sqrt S).PosSemidef :=
            Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg S)
          have hHerm : L.IsHermitian := hSqrtPosSemidef.1
          have hTransp : Lᵀ = L := by
            have hConj : Lᴴ = Lᵀ :=
              Matrix.conjTranspose_eq_transpose_of_trivial L
            -- `IsHermitian L` is `Lᴴ = L`, combined with `Lᴴ = Lᵀ` gives `Lᵀ = L`.
            calc Lᵀ = Lᴴ := hConj.symm
              _ = L := hHerm.eq
          have hSqSq : L * L = S := by
            -- `0 ≤ S` follows from `S.PosSemidef`; this discharges the `cfc_tac`
            -- side goal of `CFC.sqrt_mul_sqrt_self`.
            have hSnonneg : 0 ≤ S := hS.nonneg
            exact CFC.sqrt_mul_sqrt_self (a := S) hSnonneg
          -- (L * L) i j = ∑ k, L i k * L k j by `Matrix.mul_apply`. Then
          -- L k j = (Lᵀ) j k = L j k by `hTransp`.
          have : ∑ k, L i k * L j k = (L * L) i j := by
            rw [Matrix.mul_apply]
            refine Finset.sum_congr rfl ?_
            intro k _
            have : L j k = L k j := by
              have hk : (Lᵀ) j k = L k j := by rfl
              rw [← hk, hTransp]
            rw [this]
          rw [this, hSqSq]

/-! ### `IsGaussian` instances

The multivariate Gaussian measures defined above are Gaussian in the
Mathlib `ProbabilityTheory.IsGaussian` sense: the pushforward by every
continuous linear form on `EuclideanSpace ℝ (Fin d)` is a real
Gaussian measure. We register this for both
`stdMultivariateGaussian d` and the general `multivariateGaussian m S hS`.

The route, mirroring the construction:

1. The univariate `gaussianReal 0 1` is Gaussian (Mathlib).
2. The finite product `Measure.pi (fun _ : Fin d => gaussianReal 0 1)`
   is Gaussian by induction on `d`, using
   `measurePreserving_piFinSuccAbove` to identify it with a binary
   product of a univariate Gaussian and a smaller product Gaussian.
3. `stdMultivariateGaussian d` is the pushforward of the product
   measure by the continuous linear equivalence
   `(PiLp.continuousLinearEquiv 2 ℝ _).symm : (Fin d → ℝ) ≃L[ℝ]
   EuclideanSpace ℝ (Fin d)`, hence Gaussian.
4. `multivariateGaussian m S hS` is the pushforward of
   `stdMultivariateGaussian d` by the affine map
   `z ↦ m + (CFC.sqrt S) z`, hence Gaussian by linear + translation
   preservation. -/

/-- The standard product Gaussian on `Fin d → ℝ` is Gaussian. -/
instance instIsGaussianMeasurePiGaussian (d : ℕ) :
    IsGaussian (Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)) := by
  induction d with
  | zero =>
      -- Base case: `Fin 0 → ℝ` is a subsingleton, so `Measure.pi ...` is
      -- a Dirac measure (the empty function), which is Gaussian.
      have hSub : Subsingleton (Fin 0 → ℝ) := by
        refine ⟨fun f g => funext ?_⟩
        intro i; exact Fin.elim0 i
      have hUniv :
          (Measure.pi (fun _ : Fin 0 ↦ gaussianReal 0 1)) Set.univ = 1 := by
        rw [Measure.pi_univ]
        simp
      have hIsProb :
          IsProbabilityMeasure (Measure.pi (fun _ : Fin 0 ↦ gaussianReal 0 1)) := ⟨hUniv⟩
      -- A probability measure on a subsingleton is a Dirac mass at any
      -- (and hence every) point.
      have hDirac :
          Measure.pi (fun _ : Fin 0 ↦ gaussianReal 0 1)
            = Measure.dirac (fun i : Fin 0 => (0 : ℝ)) := by
        refine Measure.ext ?_
        intro s _
        by_cases hs : (fun i : Fin 0 => (0 : ℝ)) ∈ s
        · -- Both sides equal 1: LHS because the measure is a probability
          -- measure on a subsingleton and `s` contains the unique point;
          -- RHS by `Measure.dirac_apply` since the point is in `s`.
          have hsuniv : s = Set.univ := by
            apply Set.eq_univ_of_forall
            intro x
            have hx : x = (fun i : Fin 0 => (0 : ℝ)) := Subsingleton.elim _ _
            simpa [hx] using hs
          rw [hsuniv, hUniv, Measure.dirac_apply' _ MeasurableSet.univ]
          simp
        · -- Both sides equal 0: `s` is empty.
          have hsempty : s = ∅ := by
            apply Set.eq_empty_of_forall_notMem
            intro x hx
            have hx' : x = (fun i : Fin 0 => (0 : ℝ)) := Subsingleton.elim _ _
            exact hs (hx' ▸ hx)
          rw [hsempty]
          simp
      rw [hDirac]
      infer_instance
  | succ n ih =>
      -- Inductive step: use `Fin.consEquivL` to identify
      -- `Measure.pi (fun _ : Fin (n+1) => μ)` with
      -- `μ.prod (Measure.pi (fun _ : Fin n => μ))`, via the
      -- `measurePreserving_piFinSuccAbove` measure-preserving fact.
      have hMP :
          MeasurePreserving (MeasurableEquiv.piFinSuccAbove
              (fun _ : Fin (n + 1) => ℝ) 0)
            (Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1))
            ((gaussianReal 0 1).prod
              (Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1))) := by
        have h := measurePreserving_piFinSuccAbove
          (μ := fun _ : Fin (n + 1) => gaussianReal 0 1) (0 : Fin (n + 1))
        -- The codomain measure given by Mathlib is
        --   (μ 0).prod (Measure.pi fun j => μ ((0:Fin _).succAbove j))
        -- and `(0:Fin (n+1)).succAbove j = Fin.succ j`. Both indexed
        -- measures are still `gaussianReal 0 1`, so the second factor
        -- equals `Measure.pi (fun _ : Fin n => gaussianReal 0 1)`.
        exact h
      -- The CLE between `ℝ × (Fin n → ℝ)` and `Fin (n+1) → ℝ`.
      let L : (Fin (n + 1) → ℝ) ≃L[ℝ] ℝ × (Fin n → ℝ) :=
        (Fin.consEquivL ℝ (fun _ : Fin (n + 1) => ℝ)).symm
      -- The CLE and the measurable equivalence have the same underlying
      -- function: both equal `fun f => (f 0, fun j => f (Fin.succ j))`.
      have hLfun :
          ∀ f : Fin (n + 1) → ℝ,
            (L f) =
              MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 f := by
        intro f
        rfl
      -- Therefore the CLE pushforward equals the binary product measure.
      have hMap :
          (Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1)).map L
            = (gaussianReal 0 1).prod
                (Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)) := by
        have hMPeq : (Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1)).map
              (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0)
            = (gaussianReal 0 1).prod
                (Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1)) := hMP.map_eq
        -- Replace the CLE pushforward by the measurable-equivalence
        -- pushforward, since they have the same underlying function.
        have hEq : (Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1)).map L
                = (Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1)).map
                    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0) := by
          refine Measure.map_congr ?_
          refine Filter.Eventually.of_forall ?_
          exact hLfun
        rw [hEq]
        exact hMPeq
      -- The product measure is Gaussian (using IH for the second factor).
      haveI : IsGaussian ((gaussianReal 0 1).prod
            (Measure.pi (fun _ : Fin n ↦ gaussianReal 0 1))) := inferInstance
      -- Pull back along the CLE.
      have hMapGauss :
          IsGaussian
            ((Measure.pi (fun _ : Fin (n + 1) ↦ gaussianReal 0 1)).map L) := by
        rw [hMap]; infer_instance
      exact (isGaussian_map_equiv_iff L).mp hMapGauss

/-- The standard multivariate Gaussian on `EuclideanSpace ℝ (Fin d)` is
Gaussian. The pushforward of the product Gaussian by the continuous
linear equivalence `(Fin d → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin d)`. -/
instance instIsGaussianStdMultivariateGaussian (d : ℕ) :
    IsGaussian (stdMultivariateGaussian d) := by
  -- `stdMultivariateGaussian d` is defined as a pushforward by
  -- `MeasurableEquiv.toLp 2 (Fin d → ℝ)`, whose underlying function
  -- equals the symm of the continuous linear equivalence
  -- `PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)`.
  -- Rewriting through this identification, the measure becomes a CLE
  -- pushforward of a Gaussian product measure, hence Gaussian.
  unfold stdMultivariateGaussian
  -- The continuous linear equivalence we transport along.
  set L : (Fin d → ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin d) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm with hL_def
  -- The CLE and the measurable equivalence agree as functions:
  -- both equal `WithLp.toLp 2` on `Fin d → ℝ`.
  have hLfun :
      ∀ x : Fin d → ℝ,
        (L x) = MeasurableEquiv.toLp 2 (Fin d → ℝ) x := by
    intro x; rfl
  -- Replace the measurable-equivalence pushforward with the CLE
  -- pushforward, then invoke `isGaussian_map_equiv`.
  have hRewrite :
      (Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)).map
            (MeasurableEquiv.toLp 2 (Fin d → ℝ))
        = (Measure.pi (fun _ : Fin d ↦ gaussianReal 0 1)).map L := by
    refine (Measure.map_congr ?_).symm
    refine Filter.Eventually.of_forall ?_
    exact hLfun
  rw [hRewrite]
  -- Now apply the IsGaussian-CLE-pushforward instance, using the IsGaussian
  -- instance on the product measure.
  exact isGaussian_map_equiv L

/-- The general multivariate Gaussian `N(m, S)` on
`EuclideanSpace ℝ (Fin d)` is Gaussian. We push forward the standard
multivariate Gaussian through the linear map `Matrix.toEuclideanCLM
(CFC.sqrt S)` (yielding a Gaussian by `isGaussian_map`), and then
shift by `m` (yielding a Gaussian by Mathlib's translation instance). -/
instance instIsGaussianMultivariateGaussian
    (m : EuclideanSpace ℝ (Fin d)) (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef) :
    IsGaussian (multivariateGaussian m S hS) := by
  unfold multivariateGaussian
  -- The continuous linear map for the linear part of the affine map.
  set A : EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) :=
    Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (CFC.sqrt S) with hA_def
  -- Decompose `gaussianAffine m (CFC.sqrt S)` into a linear map followed by
  -- a translation:  `z ↦ m + A z = (translate by m) ∘ A`.
  have hDecomp :
      gaussianAffine m (CFC.sqrt S)
        = (fun y : EuclideanSpace ℝ (Fin d) => m + y) ∘ A := by
    funext z
    rfl
  rw [hDecomp]
  -- Split the composed pushforward as two successive maps:
  -- `(std).map ((·+m) ∘ A) = ((std).map A).map (·+m)`.
  rw [← Measure.map_map (μ := stdMultivariateGaussian d)
        (f := A) (g := fun y : EuclideanSpace ℝ (Fin d) => m + y)
        (by fun_prop) (by fun_prop)]
  -- The linear pushforward `(std).map A` is Gaussian by `isGaussian_map`.
  -- Then the translation pushforward is Gaussian by Mathlib's translation
  -- instance.
  haveI hLin : IsGaussian ((stdMultivariateGaussian d).map A) :=
    isGaussian_map (μ := stdMultivariateGaussian d) A
  infer_instance

/-- Sanity check: the `IsGaussian` instance chain resolves at concrete
parameters, verifying that all four instances above are wired together
correctly. -/
example {m : EuclideanSpace ℝ (Fin 3)} {S : Matrix (Fin 3) (Fin 3) ℝ}
    (hS : S.PosSemidef) : IsGaussian (multivariateGaussian m S hS) :=
  inferInstance

/-! ### Gaussian observation kernel

We now build the **Gaussian observation kernel** that takes a parameter
`θ : EuclideanSpace ℝ (Fin d)` and produces the observation distribution
`N(X · θ, ν² · I)` on `EuclideanSpace ℝ (Fin n)`. This is the standard
Gaussian linear-regression likelihood:
  `y ∣ θ ∼ N(X θ, ν² I)`.

The construction goes through:

1. The **noise covariance** `ν² • 1 : Matrix (Fin n) (Fin n) ℝ` is
   positive semidefinite (`PosSemidef.smul` of `PosSemidef.one` with
   `0 ≤ ν²`).
2. The **linear regression map** `X : Matrix (Fin n) (Fin d) ℝ` becomes
   a continuous linear map `regressionCLM X :
   EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin n)` via
   `Matrix.toEuclideanLin` followed by `LinearMap.toContinuousLinearMap`
   (the latter is fine because the domain is finite-dimensional).
3. The **observation kernel** is built by `Kernel.map` of the product
   kernel `(deterministic id) ×ₖ (const _ μ_noise)` through the affine
   map `(θ, y) ↦ X θ + y`. By the `prod_apply`/`deterministic`/`const`
   semantics, this kernel sends `θ` to the pushforward
   `(multivariateGaussian 0 (ν² • 1)).map (fun y ↦ X θ + y)`, which by
   the translation-invariance of the Gaussian (and the affine
   reparametrisation lemma) equals `multivariateGaussian (X θ) (ν² • 1)`.
4. The **joint measure** `prior ⊗ₘ obsKernel` on
   `EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)` is Gaussian:
   it equals the pushforward of the independent product
   `(multivariateGaussian 0 priorCov).prod (multivariateGaussian 0 (ν² • 1))`
   through the continuous linear automorphism `(θ, ε) ↦ (θ, X θ + ε)`,
   so it is Gaussian by `IsGaussian.prod` and `isGaussian_map`.
-/

variable {n : ℕ}

/-- The noise covariance `ν² • 1` is positive semidefinite. -/
lemma posSemidef_sq_smul_one (ν : ℝ) :
    ((ν ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef :=
  Matrix.PosSemidef.smul Matrix.PosSemidef.one (sq_nonneg ν)

/-- The matrix `X : Matrix (Fin n) (Fin d) ℝ` viewed as a continuous
linear map `EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin n)`.
We compose `Matrix.toEuclideanLin` (the linear-map version, valid for
rectangular matrices) with `LinearMap.toContinuousLinearMap` (which
upgrades to a continuous linear map, using that the domain is a
finite-dimensional Hausdorff space).

Numerical content: `regressionCLM X θ = X *ᵥ ofLp θ` after the
`EuclideanSpace`/`Fin d → ℝ` identification (see `ofLp_regressionCLM`). -/
def regressionCLM (X : Matrix (Fin n) (Fin d) ℝ) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
  LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X)

@[simp] lemma ofLp_regressionCLM (X : Matrix (Fin n) (Fin d) ℝ)
    (θ : EuclideanSpace ℝ (Fin d)) :
    WithLp.ofLp (p := 2) (V := Fin n → ℝ) (regressionCLM X θ)
      = X *ᵥ WithLp.ofLp (p := 2) (V := Fin d → ℝ) θ := by
  rfl

lemma continuous_regressionCLM (X : Matrix (Fin n) (Fin d) ℝ) :
    Continuous (regressionCLM X) :=
  (regressionCLM X).continuous

lemma measurable_regressionCLM (X : Matrix (Fin n) (Fin d) ℝ) :
    Measurable (regressionCLM X) :=
  (continuous_regressionCLM X).measurable

/-- The **observation joint map** `Ψ : E_d × E_n → E_d × E_n` defined by
`Ψ (θ, ε) = (θ, X θ + ε)`. This is a continuous linear automorphism: the
identity on the first coordinate and an affine reparametrisation on the
second. It is the change of variables that turns the independent
product `prior ⊗ noise` into the joint prior-observation law. -/
def observationJointMap (X : Matrix (Fin n) (Fin d) ℝ) :
    EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) :=
  (ContinuousLinearMap.fst ℝ _ _).prod
    ((regressionCLM X).comp (ContinuousLinearMap.fst ℝ _ _)
      + ContinuousLinearMap.snd ℝ _ _)

@[simp] lemma observationJointMap_apply (X : Matrix (Fin n) (Fin d) ℝ)
    (p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) :
    observationJointMap X p = (p.1, regressionCLM X p.1 + p.2) := rfl

/-- The Gaussian observation **kernel** `θ ↦ N(X θ, ν² · I)`.

We build it as a `Kernel.map` of the deterministic-times-constant
product kernel `(deterministic id) ×ₖ (const _ ε)` through the affine
map `(θ, y) ↦ X θ + y`. The semantics is verified in
`gaussianObservationKernel_apply`. -/
noncomputable def gaussianObservationKernel
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) :
    Kernel (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin n)) :=
  Kernel.map
    ((Kernel.deterministic (id : EuclideanSpace ℝ (Fin d) →
        EuclideanSpace ℝ (Fin d)) measurable_id)
      ×ₖ
      (Kernel.const (EuclideanSpace ℝ (Fin d))
        (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
          ((ν ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ))
          (posSemidef_sq_smul_one (n := n) ν))))
    (fun p : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) =>
      regressionCLM X p.1 + p.2)

/-- The observation kernel applied to `θ` is the pushforward of the
noise distribution by the shift `y ↦ X θ + y`. -/
theorem gaussianObservationKernel_apply
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) (θ : EuclideanSpace ℝ (Fin d)) :
    gaussianObservationKernel X ν θ
      = (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
            ((ν ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ))
            (posSemidef_sq_smul_one (n := n) ν)).map
          (fun y => regressionCLM X θ + y) := by
  classical
  -- Unfold and use `Kernel.map_apply` then `Kernel.prod_apply`.
  unfold gaussianObservationKernel
  have hf : Measurable (fun p : EuclideanSpace ℝ (Fin d)
        × EuclideanSpace ℝ (Fin n) => regressionCLM X p.1 + p.2) := by
    refine Measurable.add ?_ measurable_snd
    exact (measurable_regressionCLM X).comp measurable_fst
  rw [Kernel.map_apply _ hf]
  rw [Kernel.prod_apply, Kernel.deterministic_apply, Kernel.const_apply]
  -- Now `((dirac θ).prod μ_noise).map (fun p => X p.1 + p.2)` is the
  -- pushforward of μ_noise by `fun y => X θ + y`.
  rw [MeasureTheory.Measure.dirac_prod]
  -- Goal: map (fun p => X p.1 + p.2) (map (Prod.mk θ) noise) = map (X θ + ·) noise.
  rw [Measure.map_map hf (by fun_prop : Measurable (Prod.mk (id θ)))]
  rfl

/-- `gaussianObservationKernel X ν θ` is a probability measure. -/
instance instIsProbabilityMeasureGaussianObservationKernel
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) (θ : EuclideanSpace ℝ (Fin d)) :
    IsProbabilityMeasure (gaussianObservationKernel X ν θ) := by
  rw [gaussianObservationKernel_apply]
  exact Measure.isProbabilityMeasure_map (by fun_prop)

/-- The Gaussian observation kernel is a Markov kernel. -/
instance instIsMarkovKernelGaussianObservationKernel
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) :
    IsMarkovKernel (gaussianObservationKernel X ν) :=
  ⟨fun _ => instIsProbabilityMeasureGaussianObservationKernel X ν _⟩

/-- The Gaussian observation kernel is in particular S-finite, which is
the structural property required to form composition-products with it. -/
instance instIsSFiniteKernelGaussianObservationKernel
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) :
    IsSFiniteKernel (gaussianObservationKernel X ν) :=
  inferInstance

/-- Each observation measure `gaussianObservationKernel X ν θ` is
Gaussian. The pushforward of a Gaussian noise distribution through
the translation `y ↦ X θ + y` is Gaussian by Mathlib's translation
instance for `IsGaussian`. -/
instance instIsGaussianGaussianObservationKernel
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) (θ : EuclideanSpace ℝ (Fin d)) :
    IsGaussian (gaussianObservationKernel X ν θ) := by
  rw [gaussianObservationKernel_apply]
  -- Pushforward by `y ↦ c + y` of a Gaussian is Gaussian.
  infer_instance

/-! ### Joint prior–observation measure -/

/-- The **joint prior–observation measure** on
`EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)`. This is the
distribution of the pair `(θ, y)` where `θ ∼ N(0, priorCov)` and, given
`θ`, `y ∼ N(X θ, ν² I)`.

We define it as the composition-product
`(multivariateGaussian 0 priorCov hPrior) ⊗ₘ gaussianObservationKernel X ν`. -/
noncomputable def jointPriorObservation
    (priorCov : Matrix (Fin d) (Fin d) ℝ) (hPrior : priorCov.PosSemidef)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) :
    Measure ((EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin n))) :=
  (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) priorCov hPrior)
    ⊗ₘ (gaussianObservationKernel X ν)

/-- The joint prior–observation measure is a probability measure. -/
instance instIsProbabilityMeasureJointPriorObservation
    (priorCov : Matrix (Fin d) (Fin d) ℝ) (hPrior : priorCov.PosSemidef)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) :
    IsProbabilityMeasure (jointPriorObservation priorCov hPrior X ν) := by
  unfold jointPriorObservation
  infer_instance

/-! ### `IsGaussian` for the joint prior–observation law

To prove the joint measure is Gaussian, we identify it with the
pushforward of an **independent product** of Gaussians through a
continuous linear automorphism.

Specifically, let:
  * `priorMeas := multivariateGaussian 0 priorCov hPrior` on `E_d`.
  * `noiseMeas := multivariateGaussian 0 (ν² • 1) (posSemidef_sq_smul_one ν)` on `E_n`.
  * `Ψ := observationJointMap X : E_d × E_n →L[ℝ] E_d × E_n`,
    `(θ, ε) ↦ (θ, X θ + ε)`.

Then `jointPriorObservation = (priorMeas.prod noiseMeas).map Ψ`. The
RHS is Gaussian because `priorMeas.prod noiseMeas` is Gaussian by
`IsGaussian.prod` and `Ψ` is continuous linear.
-/

/-- The key identity: the joint prior–observation measure equals the
pushforward of an independent prior–noise product through the
observation map `(θ, ε) ↦ (θ, X θ + ε)`. -/
theorem jointPriorObservation_eq_map_prod
    (priorCov : Matrix (Fin d) (Fin d) ℝ) (hPrior : priorCov.PosSemidef)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) :
    jointPriorObservation priorCov hPrior X ν
      = ((multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) priorCov hPrior).prod
            (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
              ((ν ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ))
              (posSemidef_sq_smul_one (n := n) ν))).map (observationJointMap X) := by
  classical
  -- Strategy: take an arbitrary measurable set `s` and show both sides agree.
  -- LHS via `compProd_apply`; RHS via `map_apply` then `Measure.prod_apply`.
  ext s hs
  -- LHS: ∫⁻ θ, (obsK θ) (Prod.mk θ ⁻¹' s) ∂prior.
  set priorMeas : Measure (EuclideanSpace ℝ (Fin d)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) priorCov hPrior with hPriorMeas
  set noiseMeas : Measure (EuclideanSpace ℝ (Fin n)) :=
    multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
      ((ν ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ))
      (posSemidef_sq_smul_one (n := n) ν) with hNoiseMeas
  unfold jointPriorObservation
  rw [Measure.compProd_apply hs]
  -- Rewrite obsK θ via gaussianObservationKernel_apply.
  have hobs : ∀ θ : EuclideanSpace ℝ (Fin d),
      (gaussianObservationKernel X ν θ) (Prod.mk θ ⁻¹' s)
        = noiseMeas ((fun y => regressionCLM X θ + y) ⁻¹' (Prod.mk θ ⁻¹' s)) := by
    intro θ
    rw [gaussianObservationKernel_apply]
    rw [Measure.map_apply (by fun_prop) (measurable_prodMk_left hs)]
  simp_rw [hobs]
  -- RHS: map by Ψ, prod measure.
  have hΨ : Measurable (observationJointMap X) :=
    (observationJointMap X).continuous.measurable
  rw [Measure.map_apply hΨ hs]
  rw [Measure.prod_apply (hΨ hs)]
  -- Now goal: ∫⁻ θ, noiseMeas (...) ∂prior = ∫⁻ θ, noiseMeas (Prod.mk θ ⁻¹' (Ψ ⁻¹' s)) ∂prior.
  -- Both inner sets are equal as sets of `y`: `(observationJointMap X) (θ, y) = (θ, X θ + y)`,
  -- so `Prod.mk θ ⁻¹' (observationJointMap X ⁻¹' s) = (fun y => regressionCLM X θ + y) ⁻¹' (Prod.mk θ ⁻¹' s)`.
  rfl

/-- The joint prior–observation measure is **Gaussian**. This follows
from the affine pushforward identity above plus `IsGaussian.prod` and
the CLM-pushforward instance. -/
instance instIsGaussianJointPriorObservation
    (priorCov : Matrix (Fin d) (Fin d) ℝ) (hPrior : priorCov.PosSemidef)
    (X : Matrix (Fin n) (Fin d) ℝ) (ν : ℝ) :
    IsGaussian (jointPriorObservation priorCov hPrior X ν) := by
  rw [jointPriorObservation_eq_map_prod]
  -- The pushforward is by a continuous linear map, hence Gaussian.
  -- The base measure is the product of two Gaussian measures, hence Gaussian
  -- by `IsGaussian.prod`.
  have hPriorG : IsGaussian (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
      priorCov hPrior) := inferInstance
  have hNoiseG : IsGaussian (multivariateGaussian (0 : EuclideanSpace ℝ (Fin n))
      ((ν ^ 2) • (1 : Matrix (Fin n) (Fin n) ℝ))
      (posSemidef_sq_smul_one (n := n) ν)) := inferInstance
  -- `IsGaussian.prod` gives Gaussian on the product; then `isGaussian_map`
  -- transports it through the CLM `observationJointMap X`.
  infer_instance

/-- Sanity check: the joint prior–observation measure resolves
`IsGaussian` at a concrete instantiation, verifying the kernel +
joint-construction stack composes correctly. -/
example {priorCov : Matrix (Fin 2) (Fin 2) ℝ} (hPrior : priorCov.PosSemidef)
    {X : Matrix (Fin 3) (Fin 2) ℝ} {ν : ℝ} :
    IsGaussian (jointPriorObservation priorCov hPrior X ν) :=
  inferInstance

end ProbabilityTheory

end
