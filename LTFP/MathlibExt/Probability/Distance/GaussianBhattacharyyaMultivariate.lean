/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Probability.Distributions.Gaussian.Real
import LTFP.MathlibExt.Probability.Distance.Bhattacharyya
import LTFP.MathlibExt.Probability.Distance.GaussianBhattacharyya
import LTFP.MathlibExt.Probability.Distributions.MultivariateGaussianMeasure

/-!
# Multivariate diagonal-covariance Bhattacharyya identity

This module lifts the scalar measure-theoretic Bhattacharyya identity
`bhattacharyya_gaussianReal_scalar_eq` from `GaussianBhattacharyya.lean`
to the multivariate setting with a diagonal covariance `σ² · I`:

```
bhattacharyya
    (multivariateGaussian m₀ (σ² • 1) hPSD)
    (multivariateGaussian m₁ (σ² • 1) hPSD)
  = Real.exp (-‖m₀ - m₁‖² / (8 σ²))
```

where `‖m₀ - m₁‖² = ∑ᵢ (m₀ᵢ - m₁ᵢ)²` is the squared `EuclideanSpace`
L² norm.

The strategy bypasses the missing-from-Mathlib `Measure.rnDeriv_pi`
infrastructure by working **coordinate-wise from the outset**: the
multivariate Gaussian with diagonal covariance pulls back through the
`toLp` measurable equivalence to a product measure of univariate
Gaussians on `Fin d → ℝ`, and the Bhattacharyya integral against this
product measure factors via `MeasureTheory.integral_fintype_prod_eq_prod`
into a product of `d` copies of the scalar Bhattacharyya integral.

## Main results

* `bhattacharyya_map_measurableEquiv`: the Bhattacharyya affinity is
  invariant under joint pushforward by a measurable equivalence.
* `multivariateGaussian_diagonal_eq_map_pi_gaussianReal`: identification
  of `multivariateGaussian m (σ²·I) hPSD` with the pushforward through
  `toLp 2` of the coordinate-wise product of univariate Gaussians.
* `bhattacharyya_pi_gaussianReal_diagonal_eq_prod`: product factorisation
  of the Bhattacharyya affinity between two `Measure.pi` of univariate
  Gaussians sharing the same coordinatewise variance.
* `bhattacharyya_multivariateGaussian_diagonal_eq`: the headline
  multivariate identity.

-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Matrix MatrixOrder

namespace LTFP.MathlibExt.Probability

/-! ### Step 1: Bhattacharyya is invariant under measurable-equiv pushforward -/

/-- The Bhattacharyya affinity is invariant under joint pushforward by a
measurable equivalence. Reason: the dominating measure `μ + ν` pushes
forward to `(μ.map e) + (ν.map e)`, the Radon–Nikodym derivatives
transport via `MeasurableEmbedding.rnDeriv_map`, and the integrand is a
positive square root that is pushed through by change of variables. -/
theorem bhattacharyya_map_measurableEquiv
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ ν : Measure α) [SigmaFinite μ] [SigmaFinite ν]
    (e : α ≃ᵐ β) :
    bhattacharyya (μ.map e) (ν.map e) = bhattacharyya μ ν := by
  have he : MeasurableEmbedding e := e.measurableEmbedding
  -- Rewrite the dominating measure on the RHS through pushforward.
  have hadd : (μ + ν).map e = μ.map e + ν.map e :=
    Measure.map_add _ _ e.measurable
  -- Apply MeasurableEmbedding.integral_map on the LHS, then use rnDeriv pushforward.
  unfold bhattacharyya
  -- LHS: ∫ y, √((μ.map e).rnDeriv (μ.map e + ν.map e) y).toReal
  --              * ((ν.map e).rnDeriv (μ.map e + ν.map e) y).toReal ∂(μ.map e + ν.map e)
  -- Rewrite τ' = μ.map e + ν.map e back to (μ + ν).map e.
  rw [← hadd]
  -- Apply integral_map (we have a measurable embedding).
  rw [he.integral_map]
  -- Now LHS = ∫ x, √(((μ.map e).rnDeriv ((μ+ν).map e) (e x)).toReal *
  --                  ((ν.map e).rnDeriv ((μ+ν).map e) (e x)).toReal) ∂(μ + ν)
  -- and RHS = ∫ x, √((μ.rnDeriv (μ+ν) x).toReal *
  --                  (ν.rnDeriv (μ+ν) x).toReal) ∂(μ + ν).
  -- Use he.rnDeriv_map twice with ν := μ+ν.
  have h_rn_μ : (fun x => (μ.map e).rnDeriv ((μ + ν).map e) (e x))
      =ᵐ[μ + ν] μ.rnDeriv (μ + ν) := he.rnDeriv_map μ (μ + ν)
  have h_rn_ν : (fun x => (ν.map e).rnDeriv ((μ + ν).map e) (e x))
      =ᵐ[μ + ν] ν.rnDeriv (μ + ν) := he.rnDeriv_map ν (μ + ν)
  refine integral_congr_ae ?_
  filter_upwards [h_rn_μ, h_rn_ν] with x hx_μ hx_ν
  rw [hx_μ, hx_ν]

/-! ### Step 2: Diagonal multivariate Gaussian = pushforward of product

The CFC.sqrt of `(σ:ℝ)² • (1 : Matrix (Fin d) (Fin d) ℝ)` should be
`|σ| • 1` (its eigenvalues are all `σ²`, sqrt has eigenvalues `|σ|`,
sqrt is `|σ| • 1`). We sidestep the explicit CFC computation by working
directly with the affine map `z ↦ m + (CFC.sqrt(σ²·I))·z`, multiplying
through against the EuclideanSpace coordinates. -/

variable {d : ℕ}

/-! ### Coordinate-wise affine map

The affine map `gaussianAffine m (CFC.sqrt (σ²·I))` on
`EuclideanSpace ℝ (Fin d)`, after pulling back through `toLp 2`, acts
coordinate-wise as `z i ↦ (ofLp m) i + |σ| · z i`. The
coordinate-wise factor squares to `σ²`, so by `gaussianReal_map_const_mul`
composed with `gaussianReal_map_const_add` the pushforward of
`gaussianReal 0 1` becomes `gaussianReal (mᵢ) σ²`. -/

/-- The coordinate-wise affine transform `zᵢ ↦ mᵢ + σ · zᵢ` on `Fin d → ℝ`,
where `m : Fin d → ℝ` and `σ : ℝ`. -/
def coordAffineMap (m : Fin d → ℝ) (σ : ℝ) : (Fin d → ℝ) → (Fin d → ℝ) :=
  fun z i => m i + σ * z i

lemma measurable_coordAffineMap (m : Fin d → ℝ) (σ : ℝ) :
    Measurable (coordAffineMap m σ) := by
  unfold coordAffineMap
  refine measurable_pi_lambda _ ?_
  intro i
  have h1 : Measurable (fun z : Fin d → ℝ => z i) := measurable_pi_apply i
  exact (h1.const_mul σ).const_add (m i)

/-- The pushforward of `gaussianReal 0 1` under `x ↦ μ + σ · x` is
`gaussianReal μ (σ² • 1) = gaussianReal μ σ²` (here `σ² : ℝ≥0`). -/
lemma gaussianReal_map_affine (μ σ : ℝ) :
    (gaussianReal 0 1).map (fun x : ℝ => μ + σ * x) =
      gaussianReal μ (⟨σ ^ 2, sq_nonneg _⟩) := by
  -- Factor the affine map as `(· + μ) ∘ (σ * ·)` and push the standard
  -- normal through each Mathlib step.
  have hcomp : (fun x : ℝ => μ + σ * x) = (fun x : ℝ => μ + x) ∘ (fun x : ℝ => σ * x) := by
    funext x; simp
  -- Pushforward of standard normal under multiplication by σ.
  have h1 : (gaussianReal 0 1).map (fun x : ℝ => σ * x)
      = gaussianReal (σ * 0) (⟨σ ^ 2, sq_nonneg _⟩ * 1) :=
    gaussianReal_map_const_mul σ
  rw [hcomp, ← Measure.map_map (by fun_prop) (by fun_prop), h1]
  -- Now reduce to ` (gaussianReal (σ·0) (σ²·1)).map (μ + ·) = gaussianReal μ σ² `.
  rw [gaussianReal_map_const_add μ]
  congr 1
  · ring
  · -- `⟨σ², _⟩ * 1 = ⟨σ², _⟩` as NNReals.
    rw [mul_one]

/-- The pushforward of `Measure.pi (gaussianReal 0 1)` (the i.i.d. standard
normals on `Fin d → ℝ`) by the coordinate-wise affine map `coordAffineMap m σ`
is the product `Measure.pi (gaussianReal (m i) σ²)`. -/
lemma map_pi_gaussianReal_coordAffine (m : Fin d → ℝ) (σ : ℝ) :
    ((Measure.pi (fun _ : Fin d => gaussianReal 0 1)).map (coordAffineMap m σ))
      = Measure.pi (fun i => gaussianReal (m i) (⟨σ ^ 2, sq_nonneg _⟩)) := by
  have hpi := Measure.pi_map_pi
    (X := fun _ : Fin d => ℝ) (Y := fun _ : Fin d => ℝ)
    (μ := fun _ : Fin d => gaussianReal 0 1)
    (f := fun i x => m i + σ * x)
    (hμ := by
      intro i
      have : (gaussianReal 0 1).map (fun x : ℝ => m i + σ * x)
          = gaussianReal (m i) (⟨σ ^ 2, sq_nonneg _⟩) :=
        gaussianReal_map_affine (m i) σ
      rw [this]; infer_instance)
    (hf := by intro i; fun_prop)
  -- hpi : (pi (fun _ => gaussianReal 0 1)).map (fun z i => m i + σ * z i)
  --      = pi (fun i => (gaussianReal 0 1).map (fun x => m i + σ * x))
  -- Identify both sides as the desired equation.
  have h_rhs : (fun i : Fin d => (gaussianReal 0 1).map (fun x : ℝ => m i + σ * x))
      = fun i => gaussianReal (m i) (⟨σ ^ 2, sq_nonneg _⟩) := by
    funext i; exact gaussianReal_map_affine (m i) σ
  rw [h_rhs] at hpi
  -- The LHS function `fun z i => m i + σ * z i` is definitionally `coordAffineMap m σ`.
  exact hpi

/-! ### Step 3: Identifying `multivariateGaussian m (σ²·I)` with the product

The key matrix identity is `CFC.sqrt ((σ:ℝ)² • (1 : Matrix (Fin d) (Fin d) ℝ))
  = |σ| • 1`. This is a special case of `CFC.sqrt_eq_iff`: the right-hand
side squares to `σ² • 1`, hence by uniqueness of the PSD square root, it
equals `CFC.sqrt (σ²·1)`. -/

/-- Self-product of `|σ| • 1` (as a matrix) equals `σ² • 1`. -/
lemma abs_smul_one_mul_self (σ : ℝ) :
    (|σ| • (1 : Matrix (Fin d) (Fin d) ℝ)) * (|σ| • 1) = (σ ^ 2) • 1 := by
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_one]
  congr 1
  rw [← sq, sq_abs]

/-- `|σ| • 1` is positive semidefinite. -/
lemma posSemidef_abs_smul_one (σ : ℝ) :
    (|σ| • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef :=
  Matrix.PosSemidef.smul Matrix.PosSemidef.one (abs_nonneg _)

/-- The continuous functional calculus square root of `σ² • I` is `|σ| • I`. -/
lemma cfc_sqrt_sq_smul_one (σ : ℝ) :
    CFC.sqrt ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ)) =
      |σ| • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  rw [CFC.sqrt_eq_iff _ _
    (Matrix.PosSemidef.smul Matrix.PosSemidef.one (sq_nonneg _)).nonneg
    (posSemidef_abs_smul_one σ).nonneg]
  exact abs_smul_one_mul_self σ

/-- The `gaussianAffine m (|σ| • 1)` map on `EuclideanSpace ℝ (Fin d)`,
read through `toLp 2` / `ofLp`, is the coordinate-wise affine map
`coordAffineMap (ofLp m) |σ|` on `Fin d → ℝ`. Specifically,
`(gaussianAffine m (|σ| • 1)) ∘ toLp 2 = toLp 2 ∘ coordAffineMap (ofLp m) |σ|`. -/
lemma gaussianAffine_abs_smul_one_toLp (m : EuclideanSpace ℝ (Fin d)) (σ : ℝ) :
    (gaussianAffine m (|σ| • (1 : Matrix (Fin d) (Fin d) ℝ)))
        ∘ (MeasurableEquiv.toLp 2 (Fin d → ℝ))
      = (MeasurableEquiv.toLp 2 (Fin d → ℝ))
        ∘ (coordAffineMap (WithLp.ofLp (p := 2) (V := Fin d → ℝ) m) |σ|) := by
  funext z
  -- Unfold both sides; both live in `EuclideanSpace ℝ (Fin d) = PiLp 2 (Fin d → ℝ)`.
  -- It suffices to show pointwise (per-coordinate) equality on the underlying
  -- `Fin d → ℝ` carrier via `WithLp.ofLp`.
  apply (MeasurableEquiv.toLp 2 (Fin d → ℝ)).symm.injective
  -- `(toLp 2).symm = ofLp`, so this reduces both sides to `Fin d → ℝ`.
  show WithLp.ofLp (p := 2) (V := Fin d → ℝ)
        (gaussianAffine m (|σ| • (1 : Matrix (Fin d) (Fin d) ℝ))
          (MeasurableEquiv.toLp 2 (Fin d → ℝ) z))
      = coordAffineMap (WithLp.ofLp (p := 2) (V := Fin d → ℝ) m) |σ| z
  -- Unfold `gaussianAffine` and split the sum through `ofLp`.
  unfold gaussianAffine
  rw [WithLp.ofLp_add, Matrix.ofLp_toEuclideanCLM]
  -- `ofLp (toLp z) = z`, so the matrix-vector product becomes `(|σ|·1) *ᵥ z`.
  have hLp : WithLp.ofLp (p := 2) (V := Fin d → ℝ)
        (MeasurableEquiv.toLp 2 (Fin d → ℝ) z) = z := rfl
  rw [hLp]
  -- The RHS unfolds coordinate-wise to `i ↦ (ofLp m) i + |σ| * z i`.
  funext i
  unfold coordAffineMap
  show (WithLp.ofLp (p := 2) (V := Fin d → ℝ) m) i
        + ((|σ| • (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ z) i
      = (WithLp.ofLp (p := 2) (V := Fin d → ℝ) m) i + |σ| * z i
  congr 1
  -- `((|σ|•1) *ᵥ z) i = |σ| * z i`.
  simp [Matrix.smul_mulVec, Matrix.one_mulVec]

/-- **Identification of the diagonal multivariate Gaussian as a product
measure pushforward.** For mean `m : EuclideanSpace ℝ (Fin d)` and scalar
`σ : ℝ`, the multivariate Gaussian `N(m, σ² · I)` equals the pushforward
of the product of univariate Gaussians `pi (gaussianReal (mᵢ) σ²)`
through the measurable equivalence `toLp 2`. -/
theorem multivariateGaussian_diagonal_eq_map_pi_gaussianReal
    (m : EuclideanSpace ℝ (Fin d)) (σ : ℝ) :
    multivariateGaussian m ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ))
        (posSemidef_sq_smul_one (n := d) σ)
      = (Measure.pi (fun i => gaussianReal
          ((WithLp.ofLp (p := 2) (V := Fin d → ℝ) m) i)
          (⟨σ ^ 2, sq_nonneg _⟩))).map
        (MeasurableEquiv.toLp 2 (Fin d → ℝ)) := by
  unfold multivariateGaussian
  -- Substitute CFC.sqrt (σ²·1) = |σ|·1.
  rw [cfc_sqrt_sq_smul_one σ]
  -- Now LHS = (stdMultivariateGaussian d).map (gaussianAffine m (|σ|·1))
  -- Unfold stdMultivariateGaussian and use map_map.
  unfold stdMultivariateGaussian
  rw [Measure.map_map (measurable_gaussianAffine m (|σ| • 1))
    (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable]
  -- Now LHS = (pi (gaussianReal 0 1)).map (gaussianAffine m (|σ|·1) ∘ toLp 2)
  rw [gaussianAffine_abs_smul_one_toLp m σ]
  -- Now LHS = (pi (gaussianReal 0 1)).map (toLp 2 ∘ coordAffineMap (ofLp m) |σ|)
  -- = ((pi (gaussianReal 0 1)).map (coordAffineMap (ofLp m) |σ|)).map (toLp 2)
  rw [← Measure.map_map (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable
    (measurable_coordAffineMap _ _)]
  -- Apply map_pi_gaussianReal_coordAffine.
  rw [map_pi_gaussianReal_coordAffine
    (WithLp.ofLp (p := 2) (V := Fin d → ℝ) m) |σ|]
  -- The variance `⟨|σ|², _⟩ = ⟨σ², _⟩` since `|σ|² = σ²`.
  have h_var : (⟨|σ| ^ 2, sq_nonneg _⟩ : NNReal) = ⟨σ ^ 2, sq_nonneg _⟩ := by
    rw [← NNReal.coe_inj]; simp [sq_abs]
  -- Rewrite the variance inside the product.
  conv_lhs => rw [show (fun i : Fin d =>
      gaussianReal ((WithLp.ofLp (p := 2) (V := Fin d → ℝ) m) i)
        (⟨|σ| ^ 2, sq_nonneg _⟩))
    = (fun i : Fin d =>
      gaussianReal ((WithLp.ofLp (p := 2) (V := Fin d → ℝ) m) i)
        (⟨σ ^ 2, sq_nonneg _⟩)) from by
      funext i; rw [h_var]]

end LTFP.MathlibExt.Probability

end

