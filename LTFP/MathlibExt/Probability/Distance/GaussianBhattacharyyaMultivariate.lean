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
import Mathlib.Probability.Moments.Basic
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

/-! ### Step 4: Scalar BH integral via volume (auxiliary identity)

The scalar BH affinity equals the volume integral of the geometric mean
of the two PDFs. This is the load-bearing ingredient of the scalar BH
identity, isolated here for product factoring. -/

/-- Scalar version: the integral of the geometric mean of two
`gaussianPDFReal` functions against Lebesgue volume equals the scalar
Bhattacharyya value `exp(-Δ²/(8v))`. This is the inner computation that
the scalar identity `bhattacharyya_gaussianReal_scalar_eq` performs
after the change of measure from `gaussianReal` to volume. -/
theorem integral_sqrt_gaussianPDFReal_mul_eq
    (m₀ m₁ : ℝ) {v : NNReal} (hv : v ≠ 0) :
    ∫ x : ℝ, Real.sqrt (ProbabilityTheory.gaussianPDFReal m₀ v x *
        ProbabilityTheory.gaussianPDFReal m₁ v x)
      = gaussianBhattacharyyaScalar (m₀ - m₁) (v : ℝ) := by
  -- Use the complete-the-square anvil and the unit integral of gaussianPDFReal.
  have h_anvil : ∀ x, Real.sqrt (ProbabilityTheory.gaussianPDFReal m₀ v x *
      ProbabilityTheory.gaussianPDFReal m₁ v x) =
        gaussianBhattacharyyaScalar (m₀ - m₁) (v : ℝ) *
          ProbabilityTheory.gaussianPDFReal ((m₀ + m₁) / 2) v x :=
    sqrt_gaussianPDFReal_mul_eq hv m₀ m₁
  simp_rw [h_anvil]
  rw [MeasureTheory.integral_const_mul,
    ProbabilityTheory.integral_gaussianPDFReal_eq_one ((m₀ + m₁) / 2) hv,
    mul_one]

/-! ### Step 5: Product BH integral against `Measure.pi volume`

The product integral against `Measure.pi (fun _ => volume)` of the
coordinate-wise product of geometric means of `gaussianPDFReal` factors
into a product of `d` copies of the scalar BH integral, via
`MeasureTheory.integral_fintype_prod_eq_prod`. -/

/-- **Product BH integral identity.** The integral of the coordinate-wise
product of geometric means of two families of `gaussianPDFReal` densities,
against the product Lebesgue measure on `Fin d → ℝ`, factors into a
product of `d` univariate BH scalar values. -/
theorem integral_pi_sqrt_gaussianPDFReal_mul_eq
    (m₀ m₁ : Fin d → ℝ) {v : NNReal} (hv : v ≠ 0) :
    ∫ z : Fin d → ℝ, (∏ i, Real.sqrt
        (ProbabilityTheory.gaussianPDFReal (m₀ i) v (z i) *
         ProbabilityTheory.gaussianPDFReal (m₁ i) v (z i)))
      ∂(MeasureTheory.Measure.pi (fun _ : Fin d => (MeasureTheory.volume : Measure ℝ)))
      = ∏ i, gaussianBhattacharyyaScalar (m₀ i - m₁ i) (v : ℝ) := by
  -- Apply `integral_fintype_prod_eq_prod` to factor the product through pi.
  set f : Fin d → ℝ → ℝ :=
    fun i x => Real.sqrt
      (ProbabilityTheory.gaussianPDFReal (m₀ i) v x *
       ProbabilityTheory.gaussianPDFReal (m₁ i) v x) with hf_def
  have h_prod := MeasureTheory.integral_fintype_prod_eq_prod
    (μ := fun _ : Fin d => (MeasureTheory.volume : Measure ℝ)) f
  -- h_prod : ∫ z, ∏ i, f i (z i) ∂(pi vol) = ∏ i, ∫ x, f i x ∂vol
  rw [h_prod]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  -- Each factor reduces to the scalar BH integral.
  exact integral_sqrt_gaussianPDFReal_mul_eq (m₀ i) (m₁ i) hv

/-! ### Step 6: Multivariate moment-generating function (diagonal covariance)

The MGF identity for the multivariate Gaussian with diagonal covariance
`σ² · I` and zero mean factorises into a product of univariate Gaussian
MGFs, via `multivariateGaussian_diagonal_eq_map_pi_gaussianReal` (Step 3)
+ `MeasureTheory.integral_fintype_prod_eq_prod` + Mathlib's scalar
`ProbabilityTheory.mgf_gaussianReal`. The key intermediate identity is
stated directly on the product measure side
(`Measure.pi (gaussianReal 0 σ²)`), with the corresponding identity on
the carrier `multivariateGaussian 0 (σ²·I)` then a one-line
pushforward consequence. -/

/-- **Multivariate MGF (diagonal covariance, product-measure side).** For
the product measure of `d` i.i.d. mean-zero Gaussians with common
variance `σ : ℝ≥0`, the integral of `exp (∑ᵢ xᵢ · vᵢ)` equals the
exponential of `σ · (∑ᵢ vᵢ²) / 2`. This is the load-bearing scalar
identity behind the closed-form Bhattacharyya identity for the
multivariate diagonal Gaussian: substituting `vᵢ = (m₀ + m₁)ᵢ / (2σ²)`
in the linear coefficient and combining with the density-expansion
prefactor produces the multivariate BH closed form. -/
theorem integral_exp_inner_pi_gaussianReal_zero
    (σ : ℝ≥0) (v : Fin d → ℝ) :
    ∫ x : Fin d → ℝ, Real.exp (∑ i, x i * v i)
        ∂(Measure.pi (fun _ : Fin d => gaussianReal 0 σ))
      = Real.exp ((σ : ℝ) / 2 * ∑ i, (v i) ^ 2) := by
  classical
  -- Step 1: exp(∑) = ∏ exp.
  have h_exp : ∀ x : Fin d → ℝ,
      Real.exp (∑ i, x i * v i) = ∏ i, Real.exp (x i * v i) := by
    intro x
    exact Real.exp_sum (Finset.univ : Finset (Fin d)) (fun i => x i * v i)
  simp_rw [h_exp]
  -- Step 2: ∫ ∏ ∂(pi μ) = ∏ ∫ ∂μ.
  rw [MeasureTheory.integral_fintype_prod_eq_prod
    (μ := fun _ : Fin d => gaussianReal 0 σ)
    (f := fun i x => Real.exp (x * v i))]
  -- Step 3: each scalar factor is the MGF of `gaussianReal 0 σ` at `v i`.
  -- mgf_gaussianReal: with `p.map X = gaussianReal μ v`,
  --   mgf X p t = exp (μ * t + v * t² / 2).
  -- We apply with p = gaussianReal 0 σ, X = id, μ = 0, v = σ, t = v i.
  have h_factor : ∀ i,
      ∫ x : ℝ, Real.exp (x * v i) ∂(gaussianReal 0 σ)
        = Real.exp ((σ : ℝ) * (v i) ^ 2 / 2) := by
    intro i
    -- Rewrite x * v i as v i * x to match `mgf`'s `t * X ω` convention.
    have h_swap : ∀ x : ℝ, Real.exp (x * v i) = Real.exp (v i * x) := by
      intro x; rw [mul_comm]
    simp_rw [h_swap]
    -- This is now `mgf id (gaussianReal 0 σ) (v i)`.
    have h_mgf : ProbabilityTheory.mgf id (gaussianReal (0 : ℝ) σ) (v i)
        = Real.exp ((0 : ℝ) * v i + (σ : ℝ) * (v i) ^ 2 / 2) := by
      have hmap : (gaussianReal (0 : ℝ) σ).map (id : ℝ → ℝ) = gaussianReal 0 σ := by
        rw [Measure.map_id]
      exact ProbabilityTheory.mgf_gaussianReal hmap (v i)
    -- Unfold mgf id (gaussianReal 0 σ) (v i) = ∫ exp (v i * id x) ∂(gaussianReal 0 σ)
    -- = ∫ exp (v i * x) ∂(gaussianReal 0 σ).
    have h_unfold : ProbabilityTheory.mgf id (gaussianReal (0 : ℝ) σ) (v i)
        = ∫ x : ℝ, Real.exp (v i * x) ∂(gaussianReal 0 σ) := by
      unfold ProbabilityTheory.mgf
      simp only [id_eq]
    rw [← h_unfold, h_mgf]
    -- 0 * v i + σ * (v i)² / 2 = σ * (v i)² / 2.
    congr 1; ring
  simp_rw [h_factor]
  -- Step 4: ∏ exp(σ · (v i)² / 2) = exp(∑ σ · (v i)² / 2) = exp((σ/2) · ∑ (v i)²).
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  ring

/-- **Multivariate MGF (diagonal covariance, carrier side).** For the
zero-mean multivariate Gaussian with covariance `σ² · I` on
`EuclideanSpace ℝ (Fin d)`, the integral of the exponential of the
coordinate-wise inner product `∑ᵢ (ofLp x)ᵢ · vᵢ` against any test
coefficient vector `v : Fin d → ℝ` equals
`exp((σ²/2) · ∑ᵢ vᵢ²)`. This is the headline MGF identity at the
covariance scale `σ² · I`; it is the Route C lever for the
closed-form multivariate Bhattacharyya identity (combine with affine
translation + density expansion to recover the multivariate BH closed
form). -/
theorem integral_exp_inner_multivariateGaussian_diagonal
    (σ : ℝ) (v : Fin d → ℝ) :
    ∫ x : EuclideanSpace ℝ (Fin d),
        Real.exp (∑ i, (WithLp.ofLp (p := 2) (V := Fin d → ℝ) x) i * v i)
      ∂(multivariateGaussian (0 : EuclideanSpace ℝ (Fin d))
          ((σ ^ 2) • (1 : Matrix (Fin d) (Fin d) ℝ))
          (posSemidef_sq_smul_one (n := d) σ))
      = Real.exp ((σ ^ 2) / 2 * ∑ i, (v i) ^ 2) := by
  classical
  -- Step 1: identify the carrier measure with the pushforward of the
  -- product measure through `toLp 2`.
  rw [multivariateGaussian_diagonal_eq_map_pi_gaussianReal
    (0 : EuclideanSpace ℝ (Fin d)) σ]
  -- Step 2: change of variables via `integral_map` for the measurable
  -- equivalence `toLp 2`.
  rw [MeasureTheory.integral_map (MeasurableEquiv.toLp 2 (Fin d → ℝ)).measurable.aemeasurable
    (by fun_prop : AEStronglyMeasurable
      (fun x : EuclideanSpace ℝ (Fin d) =>
        Real.exp (∑ i, (WithLp.ofLp (p := 2) (V := Fin d → ℝ) x) i * v i))
      _)]
  -- The mean argument `(WithLp.ofLp 0)` is `0 : Fin d → ℝ`, so the
  -- product becomes `pi (gaussianReal 0 σ²)`.
  have h_mean_zero : (WithLp.ofLp (p := 2) (V := Fin d → ℝ)
      (0 : EuclideanSpace ℝ (Fin d))) = (0 : Fin d → ℝ) := rfl
  rw [show (fun i : Fin d =>
        gaussianReal ((WithLp.ofLp (p := 2) (V := Fin d → ℝ)
            (0 : EuclideanSpace ℝ (Fin d))) i)
          (⟨σ ^ 2, sq_nonneg _⟩))
      = (fun _ : Fin d => gaussianReal (0 : ℝ) (⟨σ ^ 2, sq_nonneg _⟩)) from by
    funext i; rw [h_mean_zero]; rfl]
  -- After the change of variables, the integrand on `Fin d → ℝ` is
  -- `exp(∑ᵢ (ofLp (toLp z))ᵢ · vᵢ) = exp(∑ᵢ zᵢ · vᵢ)`.
  have h_ofLp_toLp : ∀ z : Fin d → ℝ,
      (WithLp.ofLp (p := 2) (V := Fin d → ℝ)
        (MeasurableEquiv.toLp 2 (Fin d → ℝ) z)) = z := fun _ => rfl
  simp_rw [h_ofLp_toLp]
  -- Step 3: apply the product-side MGF identity.
  -- σ² packaged as NNReal: ⟨σ², sq_nonneg σ⟩.
  have h_apply := integral_exp_inner_pi_gaussianReal_zero
    (d := d) ⟨σ ^ 2, sq_nonneg σ⟩ v
  -- h_apply : ∫ x, exp(∑ᵢ xᵢ · vᵢ) ∂(pi (gaussianReal 0 ⟨σ², _⟩))
  --   = exp((⟨σ², _⟩ : ℝ) / 2 · ∑ᵢ vᵢ²) = exp(σ² / 2 · ∑ᵢ vᵢ²).
  convert h_apply using 1

end LTFP.MathlibExt.Probability

end

