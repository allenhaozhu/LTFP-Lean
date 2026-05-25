/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Spectral trace-exponential lower bound

For a Hermitian complex matrix `A` with eigenvalues `λ₁, …, λₙ`, the
matrix exponential `exp(θ • A)` is again Hermitian and its trace is
the sum of the scalar exponentials `∑ᵢ exp(θ · λᵢ)`. Since each
summand is non-negative, the trace is bounded below by any single term,
in particular by `exp(θ · λₘₐₓ)` where `λₘₐₓ` is the largest
eigenvalue of `A`.

This is the foundational spectral bridge used in the matrix Bernstein
inequality.

## Main result

* `CFC.exp_theta_lambdaMax_le_trace_exp` : for a Hermitian
  `A : Matrix n n ℂ` and any `θ : ℝ`,
  `Real.exp (θ * λₘₐₓ) ≤ (trace (exp (θ • A))).re`.
-/
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic

namespace CFC

open NormedSpace Unitary Matrix Finset

/-- For a Hermitian complex matrix `A` and any real scalar `θ`, the
trace of the matrix exponential `exp(θ • A)` (as a complex number) has
real part at least `Real.exp (θ · λₘₐₓ)`, where `λₘₐₓ` is the maximum
eigenvalue of `A`.

This is the spectral lower bound underlying matrix Bernstein. -/
theorem exp_theta_lambdaMax_le_trace_exp
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (θ : ℝ) :
    Real.exp
        (θ * Finset.sup' Finset.univ Finset.univ_nonempty hA.eigenvalues) ≤
      (Matrix.trace (NormedSpace.exp (θ • A))).re := by
  classical
  -- Notation: the eigenvector unitary `U` and the real-diagonal `D`.
  set U : Matrix.unitaryGroup n ℂ := hA.eigenvectorUnitary with hU_def
  set D : Matrix n n ℂ := Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) with hD_def
  -- Pick an index `i₀` attaining the supremum of the eigenvalues.
  obtain ⟨i₀, _, hi₀⟩ :=
    Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset n))
      Finset.univ_nonempty hA.eigenvalues
  -- Step 1: rewrite `θ • A` using the spectral theorem.
  have hA_eq : A = (U : Matrix n n ℂ) * D * (star U : Matrix n n ℂ) := by
    simpa [conjStarAlgAut_apply] using hA.spectral_theorem
  have h_smul_eq : θ • A =
      (U : Matrix n n ℂ) * (θ • D) * (star U : Matrix n n ℂ) := by
    rw [hA_eq, mul_assoc, ← mul_smul_comm, ← smul_mul_assoc, ← mul_assoc]
  -- Step 2: push `exp` past the unitary conjugation via the
  -- ⋆-algebra automorphism `conjStarAlgAut`.
  have hU_unit : IsUnit (U : Matrix n n ℂ) := Unitary.isUnit_coe
  have hU_inv : ((U : Matrix n n ℂ)⁻¹ : Matrix n n ℂ) = (star U : Matrix n n ℂ) :=
    Matrix.inv_eq_left_inv
      (Unitary.coe_star_mul_self U : (star U : Matrix n n ℂ) * (U : Matrix n n ℂ) = 1)
  have h_exp_conj :
      NormedSpace.exp ((U : Matrix n n ℂ) * (θ • D) * (star U : Matrix n n ℂ))
        = (U : Matrix n n ℂ) * NormedSpace.exp (θ • D) * (star U : Matrix n n ℂ) := by
    have := Matrix.exp_conj (U := (U : Matrix n n ℂ)) (A := θ • D) hU_unit
    rw [hU_inv] at this
    exact this
  -- Step 3: trace cyclic and `star U * U = 1` collapse the unitary.
  have h_trace_collapse :
      (Matrix.trace
          ((U : Matrix n n ℂ) * NormedSpace.exp (θ • D) *
            (star U : Matrix n n ℂ))).re
        = (Matrix.trace (NormedSpace.exp (θ • D))).re := by
    have hcycle :
        Matrix.trace
            ((U : Matrix n n ℂ) * NormedSpace.exp (θ • D) *
              (star U : Matrix n n ℂ))
          = Matrix.trace
              ((star U : Matrix n n ℂ) * (U : Matrix n n ℂ) *
                NormedSpace.exp (θ • D)) := by
      rw [Matrix.trace_mul_cycle]
    rw [hcycle]
    have h_unit : (star U : Matrix n n ℂ) * (U : Matrix n n ℂ) = 1 :=
      Unitary.coe_star_mul_self U
    rw [h_unit, one_mul]
  -- Step 4: combine to get the trace identity.
  have h_trace_eq :
      (Matrix.trace (NormedSpace.exp (θ • A))).re
        = (Matrix.trace (NormedSpace.exp (θ • D))).re := by
    rw [h_smul_eq, h_exp_conj, h_trace_collapse]
  -- Step 5: `θ • D` is diagonal, so `exp` is pointwise.
  have h_smul_diag :
      θ • D = Matrix.diagonal (fun i => (θ : ℂ) * (hA.eigenvalues i : ℂ)) := by
    rw [hD_def]
    ext i j
    by_cases h : i = j
    · subst h
      simp [Matrix.diagonal, Matrix.smul_apply, Algebra.smul_def]
    · simp [Matrix.diagonal, Matrix.smul_apply, h]
  have h_exp_diag :
      NormedSpace.exp (θ • D)
        = Matrix.diagonal
            (fun i => NormedSpace.exp ((θ : ℂ) * (hA.eigenvalues i : ℂ))) := by
    rw [h_smul_diag, Matrix.exp_diagonal, Pi.exp_def]
  -- Step 6: trace of diagonal is the sum of diagonal entries.
  have h_trace_diag :
      Matrix.trace (NormedSpace.exp (θ • D))
        = ∑ i, NormedSpace.exp ((θ : ℂ) * (hA.eigenvalues i : ℂ)) := by
    rw [h_exp_diag, Matrix.trace_diagonal]
  -- Convert each complex `exp` entry to a real `Real.exp`.
  have h_entry :
      ∀ i, NormedSpace.exp ((θ : ℂ) * (hA.eigenvalues i : ℂ))
        = ((Real.exp (θ * hA.eigenvalues i) : ℝ) : ℂ) := by
    intro i
    have : ((θ : ℂ) * (hA.eigenvalues i : ℂ)) = ((θ * hA.eigenvalues i : ℝ) : ℂ) := by
      push_cast
      ring
    rw [this, Complex.exp_eq_exp_ℂ.symm, ← Complex.ofReal_exp]
  -- Step 7: collect the real part.
  have h_trace_sum_real :
      (Matrix.trace (NormedSpace.exp (θ • D))).re
        = ∑ i, Real.exp (θ * hA.eigenvalues i) := by
    rw [h_trace_diag]
    simp_rw [h_entry]
    rw [← Complex.ofReal_sum]
    exact Complex.ofReal_re _
  -- Step 8: the i₀ summand bounds the full sum from below.
  have h_lower :
      Real.exp (θ * hA.eigenvalues i₀)
        ≤ ∑ i, Real.exp (θ * hA.eigenvalues i) :=
    Finset.single_le_sum
      (f := fun i => Real.exp (θ * hA.eigenvalues i))
      (fun i _ => Real.exp_nonneg _) (Finset.mem_univ i₀)
  -- Assemble.
  have h_rhs :
      (Matrix.trace (NormedSpace.exp (θ • A))).re
        = ∑ i, Real.exp (θ * hA.eigenvalues i) := by
    rw [h_trace_eq, h_trace_sum_real]
  rw [h_rhs]
  -- The supremum is exactly `hA.eigenvalues i₀`.
  rw [hi₀]
  exact h_lower

end CFC
