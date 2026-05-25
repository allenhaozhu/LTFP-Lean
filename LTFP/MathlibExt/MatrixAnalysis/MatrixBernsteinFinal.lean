/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.MatrixAnalysis.MatrixBernsteinOneTail
import LTFP.Ch01_Preliminaries.Concentration

/-!
# Final matrix Bernstein theorem

Composes the carrier-facing `2d · exp(...)` wrapper
`Matrix.bernstein_scalar_one_tail_2d_wrapper` with the post-Lieb optimisation
collapse `LTFP.matrix_bernstein_via_lieb` to produce the complete matrix
Bernstein tail bound

  `P(λ_max(∑ i, X i (ω i)) ≥ t)
    ≤ matrix_bernstein_bound (card d) t σ² R
    = 2 · (card d) · exp(-t² / 2 / (σ² + R t / 3))`

with no parametric `θ`-hypotheses: the optimal Chernoff parameter
`θ* := t / (σ² + R t / 3)` is supplied internally, and the side condition
`θ* · R < 3` is discharged from `0 < σ²` (algebraic).

## Main result

* `Matrix.bernstein_full` — the final matrix Bernstein bound. The factor of 2
  matches the carrier's two-tail convention; the bound applies to the upper
  tail of `λ_max`.

## References

* J. A. Tropp, *User-friendly tail bounds for sums of random matrices*,
  Found. Comput. Math. 12 (2012), 389–434, Theorem 6.1.
* F. Bach, *Learning Theory from First Principles*, MIT Press 2024,
  Proposition 1.7 (matrix Bernstein, p. 19).
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace Matrix

set_option maxHeartbeats 800000 in
/-- **Matrix Bernstein tail bound (final composed form).**

For an independent family `X i : Ω i → Matrix dn dn ℂ` of centered Hermitian
random matrices on probability spaces `(Ω i, μ i)` with `‖X i ω‖ ≤ R`,
`∫ X i = 0`, and second-moment Loewner bound
`∑ i, ∫ X i · X i ≤ σ² • 1`, the upper tail of the maximum eigenvalue of the
sum satisfies the matrix Bernstein bound

  `P(λ_max(∑ i, X i (ω i)) ≥ t) ≤ matrix_bernstein_bound (card dn) t σ² R`
  `                              = 2 · (card dn) · exp(-t² / 2 / (σ² + R t / 3))`.

The optimal Chernoff parameter `θ* := t / (σ² + R t / 3)` is used internally;
the side condition `θ* · R < 3` is discharged from `0 < σ²` via
`R t / (σ² + R t / 3) < 3 ⟺ R t < 3 σ² + R t ⟺ 0 < 3 σ²`. -/
theorem bernstein_full
    {dn m : Type*} [Fintype dn] [DecidableEq dn] [Nonempty dn]
    [Fintype m] [DecidableEq m]
    {Ω : m → Type*} [∀ i, MeasurableSpace (Ω i)]
    (μ : ∀ i, MeasureTheory.Measure (Ω i))
    [∀ i, MeasureTheory.IsProbabilityMeasure (μ i)]
    (X : ∀ i, Ω i → Matrix dn dn ℂ)
    (hX : ∀ i ω, (X i ω).IsHermitian)
    (hmeas : ∀ i, MeasureTheory.AEStronglyMeasurable (X i) (μ i))
    (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ i ω, ‖X i ω‖ ≤ R)
    (hcenter : ∀ i, ∫ x, X i x ∂μ i = 0)
    (σ2 : ℝ) (hσ2 : 0 < σ2)
    (hvar : ∑ i, ∫ x, X i x * X i x ∂μ i ≤ σ2 • (1 : Matrix dn dn ℂ))
    (t : ℝ) (ht : 0 < t)
    (hSum : ∀ ω : ∀ i, Ω i, (∑ i, X i (ω i)).IsHermitian)
    (hLamMeas : AEMeasurable
      (fun ω => Finset.sup' Finset.univ Finset.univ_nonempty (hSum ω).eigenvalues)
      (MeasureTheory.Measure.pi μ))
    (htrInt : MeasureTheory.Integrable
      (fun ω => (Matrix.trace (NormedSpace.exp
        (LTFP.matrix_bernstein_theta t σ2 R • (∑ i, X i (ω i))))).re)
      (MeasureTheory.Measure.pi μ)) :
    (MeasureTheory.Measure.pi μ).real
      {ω | t ≤ Finset.sup' Finset.univ Finset.univ_nonempty (hSum ω).eigenvalues}
    ≤ LTFP.matrix_bernstein_bound (Fintype.card dn) t σ2 R := by
  classical
  -- Optimal Chernoff parameter.
  set θ : ℝ := LTFP.matrix_bernstein_theta t σ2 R with hθ_def
  -- Denominator `D := σ² + R t / 3` is positive.
  have hRt3 : 0 ≤ R * t / 3 := by positivity
  have hD_pos : 0 < σ2 + R * t / 3 := by linarith
  -- Positivity of θ.
  have hθ_pos : 0 < θ :=
    LTFP.matrix_bernstein_theta_pos t σ2 R ht hD_pos
  -- Side condition `θ * R < 3`.
  --
  -- Algebra: `θ * R = (t / D) * R = R*t / D`.
  -- We need `R*t / D < 3`, i.e. `R*t < 3 * D = 3*σ² + R*t`, i.e. `0 < 3*σ²`.
  have hθR : θ * R < 3 := by
    -- `θ = t / D`, so `θ * R = R * t / D`.
    have h1 : θ * R = R * t / (σ2 + R * t / 3) := by
      rw [hθ_def]
      unfold LTFP.matrix_bernstein_theta
      field_simp
    rw [h1]
    -- Show `R * t / D < 3` ⇔ `R * t < 3 * D`.
    rw [div_lt_iff₀ hD_pos]
    -- Goal: `R * t < 3 * (σ² + R * t / 3)`. Equivalently `0 < 3 σ²`.
    nlinarith [hσ2]
  -- Step 1: apply the `2d · exp(...)` wrapper.
  have hWrap := Matrix.bernstein_scalar_one_tail_2d_wrapper
    μ X hX hmeas R hR hbound hcenter σ2 hσ2.le hvar t θ hθ_pos hθR
    hSum hLamMeas htrInt
  -- Reshape `hWrap` to match `matrix_bernstein_via_lieb`'s `hLieb` shape:
  --   `2 * d * exp(-θ*t + θ²*σ²/(2*(1-θR/3)))`.
  have hLieb :
      (MeasureTheory.Measure.pi μ).real
        {ω | t ≤ Finset.sup' Finset.univ Finset.univ_nonempty (hSum ω).eigenvalues}
      ≤ 2 * (Fintype.card dn : ℝ) * Real.exp
          (-(LTFP.matrix_bernstein_theta t σ2 R) * t
            + (LTFP.matrix_bernstein_theta t σ2 R) ^ 2 * σ2
                / (2 * (1 - (LTFP.matrix_bernstein_theta t σ2 R) * R / 3))) := by
    -- `hWrap` uses `θ^2` (caret), `hLieb` uses `θ^2` (caret) — same.
    -- Just unfold the `θ` abbreviation; shapes match exactly.
    have := hWrap
    simp only [hθ_def] at this
    exact this
  -- Step 2: apply the carrier `matrix_bernstein_via_lieb`.
  exact LTFP.matrix_bernstein_via_lieb (Fintype.card dn) t σ2 R hσ2 hR ht.le
    _ hLieb

end Matrix
