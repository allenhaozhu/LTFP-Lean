/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.MatrixAnalysis.BernsteinCFCLift
import LTFP.MathlibExt.MatrixAnalysis.LiebTroppJensenBochner
import LTFP.MathlibExt.MatrixAnalysis.MatrixExpPositivity
import LTFP.MathlibExt.MatrixAnalysis.MatrixCFCContinuity
import LTFP.MathlibExt.MatrixAnalysis.LiebTraceComplementary
import LTFP.MathlibExt.MatrixAnalysis.PosSemidefClosed
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Centered bounded matrix Bernstein per-summand MGF bound (log form)

For a centered family `X : Ω → Matrix n n ℂ` of Hermitian matrices with
`‖X ω‖ ≤ R` a.s., a probability measure `μ` on `Ω`, and real scalars
`0 ≤ R`, `0 ≤ θ`, `θ * R < 3`, the matrix MGF satisfies the canonical
Bernstein bound

  `CFC.log (∫ ω, exp (θ • X ω) ∂μ)
    ≤ (θ^2 / (2 * (1 - θR/3))) • (∫ ω, (X ω) * (X ω) ∂μ)`

in the Loewner order on `Matrix n n ℂ`.

## Proof outline

1.  Integrate the per-ω Bennett-Bernstein operator inequality from
    `Matrix.exp_smul_le_one_add_smul_add_sq_smul_of_hermitian_norm_le`
    (Part 8b):

      `exp (θ • X ω) ≤ 1 + θ • X ω + c • (X ω * X ω)`

    With the centering hypothesis `∫ X = 0` and Bochner linearity,
    the integrated RHS becomes `1 + c • ∫ (X·X)`.

    Integral-side monotonicity for Loewner order: use closedness of
    `{A : Matrix n n ℂ | 0 ≤ A}` (`Matrix.isClosed_setOf_nonneg`) and
    `Convex.integral_mem` applied to the difference of the two
    integrands.

2.  Apply the operator inequality `1 + V ≤ exp V` (CFC lift of the
    scalar `Real.add_one_le_exp`) at `V := c • ∫ (X·X)`, which is
    Hermitian (since `X ω * X ω` is Hermitian for Hermitian `X ω`).

3.  Strict positivity of `∫ exp (θ X)` (lower bound `exp (-θR) • 1`
    from the per-ω bound + closedness of the Loewner half-space) and
    of `exp (c • ∫ X²)` (Hermitian-exponential strict positivity from
    `Matrix.IsHermitian.isStrictlyPositive_exp`).

4.  Take `CFC.log` on both sides via `CFC.log_le_log`. The RHS
    simplifies through `CFC.log_exp` to `c • ∫ (X·X)`.

## Main result

* `Matrix.log_integral_exp_smul_le_of_centered_bounded` — the
  centered bounded summand MGF log bound for matrix Bernstein.

## References

* J. A. Tropp, *User-friendly tail bounds for sums of random matrices*,
  Found. Comput. Math. (2012), Lemma 6.7 (Bernstein per-summand MGF
  bound). The centered bounded version stated above is the standard
  reference inequality underlying the matrix Bernstein concentration
  result.
-/

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator CFC.Matrix.Norms.L2Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Helper lemmas -/

/-- The coefficient `c := θ^2 / (2 * (1 - θR/3))` is nonnegative under
the Bernstein hypotheses `0 ≤ θ`, `0 ≤ R`, `θ * R < 3`. -/
private lemma bernstein_coeff_nonneg
    {R θ : ℝ} (_hR : 0 ≤ R) (_hθ : 0 ≤ θ) (hθR : θ * R < 3) :
    0 ≤ θ ^ 2 / (2 * (1 - θ * R / 3)) := by
  have h1 : 0 ≤ θ ^ 2 := sq_nonneg θ
  have h2 : 0 < 1 - θ * R / 3 := by linarith
  have h3 : 0 < 2 * (1 - θ * R / 3) := by linarith
  exact div_nonneg h1 h3.le

omit [DecidableEq n] [Nonempty n] in
/-- For Hermitian `X`, the product `X * X` is Hermitian. -/
private lemma hermitian_mul_self_of_hermitian
    {X : Matrix n n ℂ} (hX : X.IsHermitian) :
    (X * X).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_mul, hX]

omit [Nonempty n] in
/-- Operator inequality `1 + V ≤ exp V` for Hermitian `V`.

This is the CFC lift of the scalar `Real.add_one_le_exp : x + 1 ≤ exp x`,
which holds for all real `x`. -/
private lemma one_add_le_normedSpace_exp_of_hermitian
    {V : Matrix n n ℂ} (hV : V.IsHermitian) :
    (1 : Matrix n n ℂ) + V ≤ NormedSpace.exp V := by
  have hV_sa : IsSelfAdjoint V := hV.isSelfAdjoint
  -- The scalar inequality `1 + x ≤ Real.exp x` for all real `x`.
  have h_scalar : ∀ x : ℝ, 1 + x ≤ Real.exp x := by
    intro x
    have := Real.add_one_le_exp x
    linarith
  -- CFC-lift via `cfc_mono`.
  have h_cfc_mono :
      cfc (fun x : ℝ => 1 + x) V ≤ cfc Real.exp V := by
    refine cfc_mono (a := V) (f := fun x : ℝ => 1 + x) (g := Real.exp) ?_ ?_ ?_
    · intro x _; exact h_scalar x
    · exact (continuous_const.add continuous_id).continuousOn
    · exact Real.continuous_exp.continuousOn
  -- Identify both sides.
  have h_LHS : cfc (fun x : ℝ => 1 + x) V = (1 : Matrix n n ℂ) + V := by
    rw [cfc_const_add (R := ℝ) (a := V) (r := 1) (f := fun x : ℝ => x)
      continuousOn_id hV_sa]
    rw [cfc_id' (R := ℝ) V hV_sa]
    simp
  have h_RHS : cfc Real.exp V = NormedSpace.exp V :=
    CFC.real_exp_eq_normedSpace_exp (a := V) hV_sa
  rw [h_LHS, h_RHS] at h_cfc_mono
  exact h_cfc_mono

/-! ### Norm bounds from the centered bounded hypothesis -/

/-- For Hermitian `X` with `‖X‖ ≤ R`, `0 ≤ θ`, `0 ≤ R`, and `θ * R < 3`,
the exponential `exp (θ • X)` is Hermitian and lies in the Loewner-spectral
box `[exp (-θR) • 1, exp (θR) • 1]`.

This is a direct corollary of `Matrix.exp_isHermitian_and_Icc_smul_one_of_norm_le`
applied to `θ • X`, which has norm bounded by `θ * R`. -/
private lemma exp_smul_in_slice
    {X : Matrix n n ℂ} (hX : X.IsHermitian)
    {R θ : ℝ} (hθ : 0 ≤ θ) (hbound : ‖X‖ ≤ R) :
    (NormedSpace.exp (θ • X) : Matrix n n ℂ).IsHermitian ∧
      (Real.exp (-(θ * R)) • (1 : Matrix n n ℂ)) ≤ NormedSpace.exp (θ • X) ∧
      (NormedSpace.exp (θ • X) : Matrix n n ℂ) ≤ Real.exp (θ * R) • (1 : Matrix n n ℂ) := by
  have hθX_sa : (θ • X).IsHermitian := by
    have hX_sa : IsSelfAdjoint X := hX.isSelfAdjoint
    exact ((IsSelfAdjoint.all θ).smul hX_sa : IsSelfAdjoint (θ • X))
  have h_norm : ‖(θ : ℝ) • X‖ ≤ θ * R := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ]
    exact mul_le_mul_of_nonneg_left hbound hθ
  exact Matrix.exp_isHermitian_and_Icc_smul_one_of_norm_le hθX_sa h_norm

/-! ### Main theorem -/

set_option maxHeartbeats 2400000 in
/-- **Centered bounded matrix Bernstein per-summand MGF log bound.**

For a centered family `X : Ω → Matrix n n ℂ` of Hermitian matrices
uniformly bounded in operator norm by `R ≥ 0`, a probability measure
`μ` on `Ω`, and real scalars `0 ≤ θ`, `θ * R < 3`,

  `CFC.log (∫ ω, exp (θ • X ω) ∂μ)
    ≤ (θ^2 / (2 * (1 - θR/3))) • (∫ ω, (X ω) * (X ω) ∂μ)`

in the Loewner order. This is the canonical Bernstein per-summand MGF
log bound (Tropp 2012, Lemma 6.7) for matrix concentration.

The proof integrates the per-ω Bennett-Bernstein remainder bound from
`Matrix.exp_smul_le_one_add_smul_add_sq_smul_of_hermitian_norm_le`
(Part 8b), applies the centering hypothesis `∫ X = 0`, uses the
operator inequality `1 + V ≤ exp V` (CFC lift of `Real.add_one_le_exp`),
and concludes by monotonicity of the operator logarithm. -/
theorem log_integral_exp_smul_le_of_centered_bounded
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → Matrix n n ℂ) (hX : ∀ ω, (X ω).IsHermitian)
    (hX_meas : MeasureTheory.AEStronglyMeasurable X μ)
    (R θ : ℝ) (hR : 0 ≤ R) (hθ : 0 ≤ θ) (hθR : θ * R < 3)
    (hbound : ∀ ω, ‖X ω‖ ≤ R)
    (hcenter : ∫ ω, X ω ∂μ = 0) :
    CFC.log (∫ ω, NormedSpace.exp ((θ : ℝ) • X ω) ∂μ)
      ≤ (θ ^ 2 / (2 * (1 - θ * R / 3))) • (∫ ω, (X ω) * (X ω) ∂μ) := by
  classical
  -- ─── Notation ────────────────────────────────────────────────────────
  set c : ℝ := θ ^ 2 / (2 * (1 - θ * R / 3)) with hc_def
  have hc_nn : 0 ≤ c := bernstein_coeff_nonneg hR hθ hθR
  -- ─── Step 1.  Per-ω operator inequality (Part 8b). ───────────────────
  have h_part8b : ∀ ω,
      NormedSpace.exp ((θ : ℝ) • X ω)
        ≤ (1 : Matrix n n ℂ) + (θ : ℝ) • X ω + c • ((X ω) * (X ω)) := by
    intro ω
    have := exp_smul_le_one_add_smul_add_sq_smul_of_hermitian_norm_le
      (X := X ω) (hX ω) hR hθ hθR (hbound ω)
    -- Match `c` to the explicit coefficient.
    rwa [show c = θ ^ 2 / (2 * (1 - θ * R / 3)) from hc_def] at *
  -- ─── Step 2.  AE strong measurability of exp ∘ (θ • X). ──────────────
  have h_smul_meas : MeasureTheory.AEStronglyMeasurable
      (fun ω => (θ : ℝ) • X ω) μ :=
    hX_meas.const_smul θ
  -- `exp` is continuous on `Matrix n n ℂ` (via the ℚ-restriction trick).
  let +nondep : NormedAlgebra ℚ (Matrix n n ℂ) :=
    NormedAlgebra.restrictScalars ℚ ℂ (Matrix n n ℂ)
  have h_exp_meas : MeasureTheory.AEStronglyMeasurable
      (fun ω => NormedSpace.exp ((θ : ℝ) • X ω)) μ :=
    NormedSpace.exp_continuous.comp_aestronglyMeasurable h_smul_meas
  have h_XX_meas : MeasureTheory.AEStronglyMeasurable
      (fun ω => (X ω) * (X ω)) μ :=
    hX_meas.mul hX_meas
  -- ─── Step 3.  Norm bounds and integrability. ─────────────────────────
  -- Norm bound on `exp (θ • X ω)`.
  have h_exp_norm_bound : ∀ ω, ‖NormedSpace.exp ((θ : ℝ) • X ω)‖ ≤ Real.exp (θ * R) := by
    intro ω
    obtain ⟨h_herm, h_low, h_up⟩ := exp_smul_in_slice (hX ω) hθ (hbound ω)
    -- `‖exp (θ • X ω)‖ ≤ exp (θR)` via `CStarAlgebra.norm_le_iff_le_algebraMap`.
    have hθR_nn : (0 : ℝ) ≤ Real.exp (θ * R) := (Real.exp_pos _).le
    -- For lower bound `exp(-θR) • 1 ≤ exp(θ • X ω)`, and `exp(-θR) > 0`, so
    -- `0 ≤ exp(-θR) • 1 ≤ exp(θ • X ω)`.
    have h_neg_pos : (0 : ℝ) < Real.exp (-(θ * R)) := Real.exp_pos _
    have h_alg_sp : IsStrictlyPositive
        (algebraMap ℝ (Matrix n n ℂ) (Real.exp (-(θ * R)))) :=
      isStrictlyPositive_algebraMap (𝕜 := ℝ) (A := Matrix n n ℂ) h_neg_pos
    have h_alg_eq :
        algebraMap ℝ (Matrix n n ℂ) (Real.exp (-(θ * R)))
          = Real.exp (-(θ * R)) • (1 : Matrix n n ℂ) :=
      Algebra.algebraMap_eq_smul_one _
    have h_zero_le_r1 : (0 : Matrix n n ℂ) ≤ Real.exp (-(θ * R)) • (1 : Matrix n n ℂ) := by
      rw [← h_alg_eq]; exact h_alg_sp.nonneg
    have h_zero_le : (0 : Matrix n n ℂ) ≤ NormedSpace.exp ((θ : ℝ) • X ω) :=
      h_zero_le_r1.trans h_low
    rw [CStarAlgebra.norm_le_iff_le_algebraMap (a := NormedSpace.exp ((θ : ℝ) • X ω))
      (r := Real.exp (θ * R)) hθR_nn h_zero_le]
    rw [Algebra.algebraMap_eq_smul_one]; exact h_up
  -- Integrability of `exp (θ • X ω)`.
  have h_int_const_exp : MeasureTheory.Integrable (fun _ : Ω => Real.exp (θ * R)) μ :=
    MeasureTheory.integrable_const _
  have h_int_exp : MeasureTheory.Integrable
      (fun ω => NormedSpace.exp ((θ : ℝ) • X ω) : Ω → Matrix n n ℂ) μ := by
    refine h_int_const_exp.mono h_exp_meas ?_
    refine MeasureTheory.ae_of_all μ ?_
    intro ω
    have h1 := h_exp_norm_bound ω
    have h2 : Real.exp (θ * R) ≤ ‖Real.exp (θ * R)‖ := by
      rw [Real.norm_eq_abs]; exact le_abs_self _
    exact h1.trans h2
  -- Integrability of `X ω`.
  have h_int_X : MeasureTheory.Integrable X μ := by
    refine (MeasureTheory.integrable_const R).mono hX_meas ?_
    refine MeasureTheory.ae_of_all μ ?_
    intro ω
    have h1 := hbound ω
    have h2 : R ≤ ‖R‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
    exact h1.trans h2
  -- Norm bound on `X ω * X ω` from `‖X ω‖ ≤ R`.
  have h_XX_norm_bound : ∀ ω, ‖(X ω) * (X ω)‖ ≤ R * R := by
    intro ω
    calc ‖(X ω) * (X ω)‖
        ≤ ‖X ω‖ * ‖X ω‖ := norm_mul_le _ _
      _ ≤ R * R := mul_le_mul (hbound ω) (hbound ω) (norm_nonneg _) hR
  -- Integrability of `X ω * X ω`.
  have h_int_XX : MeasureTheory.Integrable (fun ω => (X ω) * (X ω)) μ := by
    refine (MeasureTheory.integrable_const (R * R)).mono h_XX_meas ?_
    refine MeasureTheory.ae_of_all μ ?_
    intro ω
    have h1 := h_XX_norm_bound ω
    have h2 : R * R ≤ ‖R * R‖ := by rw [Real.norm_eq_abs]; exact le_abs_self _
    exact h1.trans h2
  -- Integrability of the RHS sum `1 + θ • X + c • (X * X)`.
  have h_int_const_one : MeasureTheory.Integrable
      (fun _ : Ω => (1 : Matrix n n ℂ)) μ :=
    MeasureTheory.integrable_const _
  have h_int_thetaX : MeasureTheory.Integrable (fun ω => (θ : ℝ) • X ω) μ :=
    h_int_X.smul θ
  have h_int_cXX : MeasureTheory.Integrable (fun ω => c • ((X ω) * (X ω))) μ :=
    h_int_XX.smul c
  have h_int_rhs : MeasureTheory.Integrable
      (fun ω => (1 : Matrix n n ℂ) + (θ : ℝ) • X ω + c • ((X ω) * (X ω))) μ :=
    (h_int_const_one.add h_int_thetaX).add h_int_cXX
  -- ─── Step 4.  Integrate the per-ω inequality via PSD cone closedness. ─
  -- Define the difference function `D ω := RHS - LHS ≥ 0` (Loewner).
  set D : Ω → Matrix n n ℂ := fun ω =>
    ((1 : Matrix n n ℂ) + (θ : ℝ) • X ω + c • ((X ω) * (X ω)))
      - NormedSpace.exp ((θ : ℝ) • X ω) with hD_def
  -- Each `D ω ∈ {A | 0 ≤ A}`.
  have h_D_mem : ∀ ω, (0 : Matrix n n ℂ) ≤ D ω := by
    intro ω
    show 0 ≤ ((1 : Matrix n n ℂ) + (θ : ℝ) • X ω + c • ((X ω) * (X ω)))
        - NormedSpace.exp ((θ : ℝ) • X ω)
    exact sub_nonneg.mpr (h_part8b ω)
  have h_D_mem_ae : ∀ᵐ ω ∂μ, D ω ∈ {A : Matrix n n ℂ | (0 : Matrix n n ℂ) ≤ A} :=
    MeasureTheory.ae_of_all μ (fun ω => h_D_mem ω)
  -- `{A | 0 ≤ A}` is closed and convex.
  have h_nn_closed : IsClosed {A : Matrix n n ℂ | (0 : Matrix n n ℂ) ≤ A} :=
    Matrix.isClosed_setOf_nonneg
  have h_nn_convex : Convex ℝ {A : Matrix n n ℂ | (0 : Matrix n n ℂ) ≤ A} := by
    intro A hA B hB t u ht hu _
    simp only [Set.mem_setOf_eq] at hA hB ⊢
    have h1 : (0 : Matrix n n ℂ) ≤ t • A := smul_nonneg ht hA
    have h2 : (0 : Matrix n n ℂ) ≤ u • B := smul_nonneg hu hB
    have h3 : (0 : Matrix n n ℂ) + 0 ≤ t • A + u • B := add_le_add h1 h2
    simpa using h3
  -- Integrability of `D`.
  have h_int_D : MeasureTheory.Integrable D μ :=
    h_int_rhs.sub h_int_exp
  -- `∫ D ∈ {A | 0 ≤ A}` via `Convex.integral_mem`.
  have h_int_D_mem : (∫ ω, D ω ∂μ) ∈ {A : Matrix n n ℂ | (0 : Matrix n n ℂ) ≤ A} :=
    h_nn_convex.integral_mem h_nn_closed h_D_mem_ae h_int_D
  -- Translate to `∫ exp (θ • X) ≤ ∫ RHS`.
  have h_int_le_step1 :
      ∫ ω, NormedSpace.exp ((θ : ℝ) • X ω) ∂μ
        ≤ ∫ ω, ((1 : Matrix n n ℂ) + (θ : ℝ) • X ω + c • ((X ω) * (X ω))) ∂μ := by
    have h_eq : (∫ ω, D ω ∂μ)
        = (∫ ω, ((1 : Matrix n n ℂ) + (θ : ℝ) • X ω + c • ((X ω) * (X ω))) ∂μ)
          - ∫ ω, NormedSpace.exp ((θ : ℝ) • X ω) ∂μ :=
      MeasureTheory.integral_sub h_int_rhs h_int_exp
    have h0 : (0 : Matrix n n ℂ) ≤ ∫ ω, D ω ∂μ := h_int_D_mem
    have h1 : (0 : Matrix n n ℂ) ≤
        (∫ ω, ((1 : Matrix n n ℂ) + (θ : ℝ) • X ω + c • ((X ω) * (X ω))) ∂μ)
          - ∫ ω, NormedSpace.exp ((θ : ℝ) • X ω) ∂μ := h_eq ▸ h0
    exact sub_nonneg.mp h1
  -- ─── Step 5.  Simplify ∫ RHS using linearity and `hcenter`. ──────────
  have h_int_rhs_eq :
      ∫ ω, ((1 : Matrix n n ℂ) + (θ : ℝ) • X ω + c • ((X ω) * (X ω))) ∂μ
        = (1 : Matrix n n ℂ) + c • (∫ ω, (X ω) * (X ω) ∂μ) := by
    -- Step A: split as `(1 + θ•X) + c•X²`.
    have hstepA :
        ∫ ω, ((1 : Matrix n n ℂ) + (θ : ℝ) • X ω + c • ((X ω) * (X ω))) ∂μ
          = (∫ ω, ((1 : Matrix n n ℂ) + (θ : ℝ) • X ω) ∂μ)
            + (∫ ω, c • ((X ω) * (X ω)) ∂μ) := by
      have h_int_1plusX : MeasureTheory.Integrable
          (fun ω => (1 : Matrix n n ℂ) + (θ : ℝ) • X ω) μ :=
        h_int_const_one.add h_int_thetaX
      have := MeasureTheory.integral_add h_int_1plusX h_int_cXX
      simpa using this
    -- Step B: split `(1 + θ•X)` further.
    have hstepB :
        ∫ ω, ((1 : Matrix n n ℂ) + (θ : ℝ) • X ω) ∂μ
          = (∫ ω, (1 : Matrix n n ℂ) ∂μ) + (∫ ω, (θ : ℝ) • X ω ∂μ) := by
      have := MeasureTheory.integral_add h_int_const_one h_int_thetaX
      simpa using this
    -- Step C: ∫ const = const for probability measure.
    have hstepC : ∫ _ : Ω, (1 : Matrix n n ℂ) ∂μ = (1 : Matrix n n ℂ) := by
      rw [MeasureTheory.integral_const]
      have hμ_one : (μ.real Set.univ) = 1 := MeasureTheory.probReal_univ
      rw [hμ_one, one_smul]
    -- Step D: ∫ (θ • X) = θ • ∫ X.
    have hstepD : ∫ ω, (θ : ℝ) • X ω ∂μ = (θ : ℝ) • ∫ ω, X ω ∂μ :=
      MeasureTheory.integral_smul (c := (θ : ℝ)) (f := X)
    -- Step E: ∫ (c • X²) = c • ∫ X².
    have hstepE : ∫ ω, c • ((X ω) * (X ω)) ∂μ = c • ∫ ω, (X ω) * (X ω) ∂μ :=
      MeasureTheory.integral_smul (c := c) (f := fun ω => (X ω) * (X ω))
    rw [hstepA, hstepB, hstepC, hstepD, hstepE, hcenter, smul_zero, add_zero]
  rw [h_int_rhs_eq] at h_int_le_step1
  -- ─── Step 6.  Apply `1 + V ≤ exp V` at `V := c • ∫ (X·X)`. ───────────
  -- Hermicity of `∫ (X·X)`.
  have h_XX_herm_ae : ∀ ω, ((X ω) * (X ω)).IsHermitian :=
    fun ω => hermitian_mul_self_of_hermitian (hX ω)
  -- `∫ (X·X)` is Hermitian: integrate the IsHermitian condition.
  -- Use `IsHermitian` ↔ `IsSelfAdjoint`, and that the self-adjoint cone is closed and convex.
  have h_int_XX_herm : (∫ ω, (X ω) * (X ω) ∂μ).IsHermitian := by
    -- {A | A.IsHermitian} is closed and convex.
    have h_herm_closed : IsClosed {A : Matrix n n ℂ | A.IsHermitian} :=
      Matrix.isClosed_setOf_isHermitian
    have h_herm_convex : Convex ℝ {A : Matrix n n ℂ | A.IsHermitian} := by
      intro A hA B hB t u ht hu _
      have hA_sa : IsSelfAdjoint A := hA
      have hB_sa : IsSelfAdjoint B := hB
      have htA : IsSelfAdjoint (t • A) := (IsSelfAdjoint.all t).smul hA_sa
      have huB : IsSelfAdjoint (u • B) := (IsSelfAdjoint.all u).smul hB_sa
      exact (htA.add huB : IsSelfAdjoint (t • A + u • B))
    have h_mem_ae : ∀ᵐ ω ∂μ, ((X ω) * (X ω)) ∈ {A : Matrix n n ℂ | A.IsHermitian} :=
      MeasureTheory.ae_of_all μ (fun ω => h_XX_herm_ae ω)
    exact h_herm_convex.integral_mem h_herm_closed h_mem_ae h_int_XX
  -- Hermicity of `c • ∫ (X·X)`.
  have h_cXX_herm : (c • ∫ ω, (X ω) * (X ω) ∂μ).IsHermitian := by
    have : IsSelfAdjoint (c • ∫ ω, (X ω) * (X ω) ∂μ) :=
      (IsSelfAdjoint.all c).smul h_int_XX_herm.isSelfAdjoint
    exact this
  -- Apply `1 + V ≤ exp V`.
  have h_1plusV_le_expV :
      (1 : Matrix n n ℂ) + c • (∫ ω, (X ω) * (X ω) ∂μ)
        ≤ NormedSpace.exp (c • (∫ ω, (X ω) * (X ω) ∂μ)) :=
    one_add_le_normedSpace_exp_of_hermitian h_cXX_herm
  -- Chain: `∫ exp (θ • X) ≤ 1 + c • ∫ X² ≤ exp (c • ∫ X²)`.
  have h_int_le_step2 :
      ∫ ω, NormedSpace.exp ((θ : ℝ) • X ω) ∂μ
        ≤ NormedSpace.exp (c • (∫ ω, (X ω) * (X ω) ∂μ)) :=
    h_int_le_step1.trans h_1plusV_le_expV
  -- ─── Step 7.  Strict positivity of both sides. ───────────────────────
  -- LHS strict positivity: `exp (-θR) • 1 ≤ ∫ exp (θ • X)`.
  -- Integrate the per-ω lower bound `exp (-θR) • 1 ≤ exp (θ • X ω)`.
  have h_exp_lower_ae : ∀ ω,
      Real.exp (-(θ * R)) • (1 : Matrix n n ℂ) ≤ NormedSpace.exp ((θ : ℝ) • X ω) := by
    intro ω
    obtain ⟨_, h_low, _⟩ := exp_smul_in_slice (hX ω) hθ (hbound ω)
    exact h_low
  -- Use `Convex.integral_mem` on the set `{A | exp(-θR) • 1 ≤ A}`.
  have h_lower_closed : IsClosed
      {A : Matrix n n ℂ | Real.exp (-(θ * R)) • (1 : Matrix n n ℂ) ≤ A} := by
    -- Use `isClosed_setOf_le_left` from PosSemidefClosed.
    exact Matrix.isClosed_setOf_le_left (Real.exp (-(θ * R)) • (1 : Matrix n n ℂ))
  have h_lower_convex : Convex ℝ
      {A : Matrix n n ℂ | Real.exp (-(θ * R)) • (1 : Matrix n n ℂ) ≤ A} := by
    intro A hA B hB t u ht hu htu
    simp only [Set.mem_setOf_eq] at hA hB ⊢
    calc Real.exp (-(θ * R)) • (1 : Matrix n n ℂ)
        = (t + u) • (Real.exp (-(θ * R)) • (1 : Matrix n n ℂ)) := by rw [htu, one_smul]
      _ = t • (Real.exp (-(θ * R)) • (1 : Matrix n n ℂ))
            + u • (Real.exp (-(θ * R)) • (1 : Matrix n n ℂ)) := add_smul _ _ _
      _ ≤ t • A + u • B := by
        exact add_le_add (smul_le_smul_of_nonneg_left hA ht)
          (smul_le_smul_of_nonneg_left hB hu)
  have h_int_exp_lower :
      Real.exp (-(θ * R)) • (1 : Matrix n n ℂ) ≤
        ∫ ω, NormedSpace.exp ((θ : ℝ) • X ω) ∂μ := by
    have h_mem_ae : ∀ᵐ ω ∂μ, NormedSpace.exp ((θ : ℝ) • X ω) ∈
        {A : Matrix n n ℂ | Real.exp (-(θ * R)) • (1 : Matrix n n ℂ) ≤ A} :=
      MeasureTheory.ae_of_all μ (fun ω => h_exp_lower_ae ω)
    exact h_lower_convex.integral_mem h_lower_closed h_mem_ae h_int_exp
  -- Strict positivity of LHS via `IsStrictlyPositive.of_le`.
  have h_lhs_sp : IsStrictlyPositive
      (∫ ω, NormedSpace.exp ((θ : ℝ) • X ω) ∂μ : Matrix n n ℂ) := by
    have h_alg_eq :
        algebraMap ℝ (Matrix n n ℂ) (Real.exp (-(θ * R)))
          = Real.exp (-(θ * R)) • (1 : Matrix n n ℂ) :=
      Algebra.algebraMap_eq_smul_one _
    have h_alg_sp : IsStrictlyPositive
        (algebraMap ℝ (Matrix n n ℂ) (Real.exp (-(θ * R)))) :=
      isStrictlyPositive_algebraMap (𝕜 := ℝ) (A := Matrix n n ℂ) (Real.exp_pos _)
    have h_alg_le :
        algebraMap ℝ (Matrix n n ℂ) (Real.exp (-(θ * R)))
          ≤ ∫ ω, NormedSpace.exp ((θ : ℝ) • X ω) ∂μ := by
      rw [h_alg_eq]; exact h_int_exp_lower
    exact h_alg_sp.of_le h_alg_le
  -- RHS strict positivity: `exp` of a Hermitian matrix is strictly positive.
  have h_rhs_sp : IsStrictlyPositive
      (NormedSpace.exp (c • (∫ ω, (X ω) * (X ω) ∂μ)) : Matrix n n ℂ) :=
    h_cXX_herm.isStrictlyPositive_exp
  -- ─── Step 8.  Take log via `CFC.log_le_log`. ──────────────────────────
  have h_log_le :
      CFC.log (∫ ω, NormedSpace.exp ((θ : ℝ) • X ω) ∂μ)
        ≤ CFC.log (NormedSpace.exp (c • (∫ ω, (X ω) * (X ω) ∂μ))) :=
    CFC.log_le_log h_int_le_step2 h_lhs_sp
  -- Simplify RHS via `CFC.log_exp`.
  have h_log_exp_eq :
      CFC.log (NormedSpace.exp (c • (∫ ω, (X ω) * (X ω) ∂μ)))
        = c • (∫ ω, (X ω) * (X ω) ∂μ) :=
    CFC.log_exp _ h_cXX_herm.isSelfAdjoint
  rw [h_log_exp_eq] at h_log_le
  exact h_log_le

end Matrix
