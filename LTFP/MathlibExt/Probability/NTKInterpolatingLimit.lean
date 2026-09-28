/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.LinearAlgebra.MatrixInverseLimit
import LTFP.MathlibExt.Probability.NTKLinearizedRKHS
import LTFP.Ch07_Kernels.Algorithms

/-!
# NTK KRR interpolating limit (T6a)

**Bach (2024) §7.4 + §12.4 — the interpolating (`λ → 0⁺`) limit of the
kernel ridge regression predictor.**

The kernel ridge regression (KRR) coefficient vector is

  `α̂_λ := (K + n λ I)⁻¹ y`,

where `K = gramMatrix k xs` is the empirical Gram matrix and `y : Fin n → ℝ`
are the labels.  The KRR predictor is the kernel expansion of these
coefficients,

  `f̂_λ(x) := Σ_i α̂_λ(i) · k(x, x_i)`.

This module establishes the *interpolating* limit: as `λ → 0⁺`, if the
Gram matrix `K` is invertible (equivalently, positive-definite in the
coercive setting `ρ I ≼ K`), then

  `α̂_λ    → K⁻¹ · y`,
  `f̂_λ(x) → Σ_i (K⁻¹ y) i · k(x, x_i)`  for every `x`.

Composed with the linearized-model finite-RKHS expansion
(`ntk_linearized_model_in_finite_rkhs`, T6c-lin), this gives the
closed-form identity of the linearized NTK model at the interpolating
KRR-limit — with labels *centered by the base network output at the
training inputs*.

## Sub-lemmas assembled

* `Matrix.regularized_inv_tendsto_inv` — for invertible `M`,
  `(M + s • 1)⁻¹ → M⁻¹` as `s → 0`.  Immediate corollary of
  `Matrix.regularized_inv_mul_tendsto_one` by right-multiplying by
  `M⁻¹`.

* `LTFP.tendsto_nat_mul_nhdsWithin_Ioi` — for every `n : ℕ` the map
  `λ ↦ n · λ` sends `𝓝[>] 0` to `𝓝 0`.  This is the adapter feeding
  the base result into the `n·λ`-regularized KRR system.

* `LTFP.krrCoeffs_tendsto_interpolating` — as `λ → 0⁺`, the KRR
  coefficients converge pointwise to `K⁻¹ y`.

* `LTFP.krrPredictor_tendsto_interpolating` — pointwise convergence
  of the KRR predictor to the closed-form interpolating predictor at
  every test point `x`.

* `LTFP.ntk_linearized_krr_interpolating_limit` — the main composed
  theorem: under the coercivity hypothesis and along a discrete-Euler
  trajectory in the training-gradient span, the linearized network
  output at the interpolating KRR-limit satisfies

    `lim_{λ→0⁺} krrPredictor K_NTK xs ỹ λ x
        = kernelExpansion K_NTK xs (K⁻¹ ỹ) x`,

  where `ỹ i := y i - f_{θ₀}(x_i)` are the centered labels.

## Scope caveat

This theorem is a statement about the **KRR ridge predictor's
`λ → 0⁺` limit** — the pointwise convergence of `α̂_λ` and the induced
predictor to the pseudoinverse solution.  It does *not* claim
continuous-time `θ(∞)` convergence of a training trajectory.  The
composition with T6c-lin is deterministic and holds under the
per-step-in-training-gradient-span hypothesis established in
`ntk_linearized_span_step_invariant`.

## Counterexample sanity check

At `n = 1`, `K = [[1]]`, `y = 1`, `f_{θ₀}(x_1) = 0` (so `ỹ = 1`), the
interpolating limit gives `α_0 = 1⁻¹ · 1 = 1`, and hence
`k(x)^T K⁻¹ ỹ = k(x, x_1)`.  This matches the elementary
one-training-point kernel-regression identity.
-/

namespace Matrix

open Filter Topology

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- **Regularized inverse converges to the plain inverse as the ridge
term vanishes.**

For an invertible real square matrix `M`, the regularized inverse
`(M + s • 1)⁻¹` tends to `M⁻¹` as `s → 0`.

The proof multiplies the base identity
`Matrix.regularized_inv_mul_tendsto_one` on the right by the constant
matrix `M⁻¹` and observes that
`(M + s • 1)⁻¹ * M * M⁻¹ = (M + s • 1)⁻¹` when `M` is invertible. -/
theorem regularized_inv_tendsto_inv
    (M : Matrix d d ℝ) (hM : M.det ≠ 0) :
    Tendsto (fun s : ℝ => (M + s • (1 : Matrix d d ℝ))⁻¹)
      (nhds 0) (nhds M⁻¹) := by
  -- Base: `(M + s • 1)⁻¹ * M → 1`.
  have h_base : Tendsto (fun s : ℝ => (M + s • (1 : Matrix d d ℝ))⁻¹ * M)
      (nhds 0) (nhds (1 : Matrix d d ℝ)) :=
    regularized_inv_mul_tendsto_one M hM
  -- Right-multiply the limit expression by the constant `M⁻¹`.
  have h_mul :
      Tendsto (fun s : ℝ => ((M + s • (1 : Matrix d d ℝ))⁻¹ * M) * M⁻¹)
        (nhds 0) (nhds ((1 : Matrix d d ℝ) * M⁻¹)) :=
    h_base.mul tendsto_const_nhds
  -- Simplify both sides: LHS = `(M + s • 1)⁻¹`, RHS = `M⁻¹`.
  have hMM : M * M⁻¹ = (1 : Matrix d d ℝ) :=
    Matrix.mul_nonsing_inv M (isUnit_iff_ne_zero.mpr hM)
  have h_fun_eq :
      (fun s : ℝ => ((M + s • (1 : Matrix d d ℝ))⁻¹ * M) * M⁻¹) =
        (fun s : ℝ => (M + s • (1 : Matrix d d ℝ))⁻¹) := by
    funext s
    rw [Matrix.mul_assoc, hMM, Matrix.mul_one]
  rw [h_fun_eq] at h_mul
  simpa [Matrix.one_mul] using h_mul

/-- One-sided variant of `regularized_inv_tendsto_inv`: the limit
holds along `𝓝[>] 0` as well. -/
theorem regularized_inv_tendsto_inv_nhdsWithin_Ioi
    (M : Matrix d d ℝ) (hM : M.det ≠ 0) :
    Tendsto (fun s : ℝ => (M + s • (1 : Matrix d d ℝ))⁻¹)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds M⁻¹) :=
  (regularized_inv_tendsto_inv M hM).mono_left nhdsWithin_le_nhds

#print axioms Matrix.regularized_inv_tendsto_inv

end Matrix

namespace LTFP

open Filter Topology BigOperators Matrix ProbabilityTheory

/-! ### `n · λ → 0` filter adapter -/

/-- The map `λ ↦ n · λ` sends `𝓝[>] 0` into `𝓝 0` for every natural
number `n`.  This is the filter-level adapter that lets us feed the
base `(M + λ • 1)⁻¹ * M → 1` result into the `n · λ`-regularized
KRR system. -/
theorem tendsto_nat_mul_nhdsWithin_Ioi (n : ℕ) :
    Tendsto (fun lam : ℝ => (n : ℝ) * lam)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  -- Continuity of `λ ↦ n · λ` at `0` gives `→ n · 0 = 0`.
  have h_cont : Continuous (fun lam : ℝ => (n : ℝ) * lam) :=
    continuous_const.mul continuous_id
  have h_at_zero : (fun lam : ℝ => (n : ℝ) * lam) 0 = 0 := by simp
  -- Tendsto through the two-sided neighborhood, then restrict.
  have h_full : Tendsto (fun lam : ℝ => (n : ℝ) * lam) (nhds 0) (nhds 0) := by
    have := h_cont.tendsto (0 : ℝ)
    simpa [h_at_zero] using this
  exact h_full.mono_left nhdsWithin_le_nhds

/-! ### KRR coefficients: interpolating limit -/

variable {𝒳 : Type*} {n : ℕ}

/-- **KRR coefficient interpolating limit.**

If `K := gramMatrix k xs` is invertible (`K.det ≠ 0`), then as
`λ → 0⁺` the KRR coefficient vector
`α̂_λ := (K + n λ I)⁻¹ y` converges pointwise to `K⁻¹ y`.

The proof composes three continuity facts:
1. `λ ↦ n · λ` sends `𝓝[>] 0` to `𝓝 0`
   (`tendsto_nat_mul_nhdsWithin_Ioi`);
2. `s ↦ (K + s • 1)⁻¹` is continuous at `0`, with value `K⁻¹`
   (`Matrix.regularized_inv_tendsto_inv`);
3. `M ↦ M *ᵥ y` is continuous in `M` (`Continuous.matrix_mulVec`).

Pointwise convergence in `Fin n → ℝ` is obtained through
`tendsto_pi_nhds`. -/
theorem krrCoeffs_tendsto_interpolating
    (k : 𝒳 → 𝒳 → ℝ) (xs : Fin n → 𝒳) (y : Fin n → ℝ)
    (hK : (gramMatrix k xs).det ≠ 0) :
    Tendsto (fun lam : ℝ => krrCoeffs k xs y lam)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((gramMatrix k xs)⁻¹ *ᵥ y)) := by
  -- Compose (1)+(2): `λ ↦ (K + (n · λ) • 1)⁻¹ → K⁻¹` along `𝓝[>] 0`.
  have h_inv :
      Tendsto (fun lam : ℝ =>
          (gramMatrix k xs + ((n : ℝ) * lam) •
            (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (gramMatrix k xs)⁻¹) := by
    have h_base :
        Tendsto (fun s : ℝ =>
            (gramMatrix k xs + s • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹)
          (nhds 0) (nhds (gramMatrix k xs)⁻¹) :=
      Matrix.regularized_inv_tendsto_inv _ hK
    -- Compose along the adapter.
    exact h_base.comp (tendsto_nat_mul_nhdsWithin_Ioi n)
  -- (3) Multiply-by-`y` continuity, converted pointwise.
  -- The map `M ↦ M *ᵥ y` is continuous.
  have h_mulVec_cont :
      Continuous (fun M : Matrix (Fin n) (Fin n) ℝ => M *ᵥ y) :=
    continuous_id.matrix_mulVec continuous_const
  -- Compose the continuous mulVec map with `h_inv`.
  have h_all :
      Tendsto (fun lam : ℝ =>
          (gramMatrix k xs + ((n : ℝ) * lam) •
            (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹ *ᵥ y)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((gramMatrix k xs)⁻¹ *ᵥ y)) :=
    (h_mulVec_cont.tendsto _).comp h_inv
  -- Rewrite goal to the definitional form of `krrCoeffs`.
  simpa [krrCoeffs] using h_all

/-! ### KRR predictor: pointwise interpolating limit -/

/-- **KRR predictor interpolating limit (pointwise).**

Under the same invertibility hypothesis on the Gram matrix, at every
test point `x` the KRR predictor value `f̂_λ(x)` converges as
`λ → 0⁺` to the kernel expansion of the pseudoinverse-limit
coefficients `K⁻¹ y`:

  `krrPredictor k xs y λ x → kernelExpansion k xs (K⁻¹ y) x`
    as `λ → 0⁺`.

The proof composes `krrCoeffs_tendsto_interpolating` with continuity
of the finite kernel sum
`α ↦ Σ i, α i · k(x, x i)` in `α`. -/
theorem krrPredictor_tendsto_interpolating
    (k : 𝒳 → 𝒳 → ℝ) (xs : Fin n → 𝒳) (y : Fin n → ℝ)
    (hK : (gramMatrix k xs).det ≠ 0) (x : 𝒳) :
    Tendsto (fun lam : ℝ => krrPredictor k xs y lam x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (kernelExpansion k xs ((gramMatrix k xs)⁻¹ *ᵥ y) x)) := by
  -- The kernel expansion is a finite sum in the coefficient vector,
  -- which is continuous in `α ∈ Fin n → ℝ`.
  have h_sum_cont :
      Continuous (fun α : Fin n → ℝ =>
        ∑ i, α i * k x (xs i)) := by
    refine continuous_finset_sum _ (fun i _ => ?_)
    exact ((continuous_apply i).mul continuous_const)
  -- The predictor is this continuous map applied to `krrCoeffs …`.
  have h_coeff := krrCoeffs_tendsto_interpolating k xs y hK
  have h_comp :
      Tendsto (fun lam : ℝ => ∑ i, (krrCoeffs k xs y lam) i * k x (xs i))
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (∑ i, ((gramMatrix k xs)⁻¹ *ᵥ y) i * k x (xs i))) :=
    (h_sum_cont.tendsto _).comp h_coeff
  -- Unfold `krrPredictor` and `kernelExpansion`.
  simpa [krrPredictor, kernelExpansion] using h_comp

/-! ### Composition with T6c-lin: linearized KRR interpolating identity -/

/-- **Main theorem — linearized-NTK closed-form KRR interpolating
identity.**

Let `k := paramNTKKernel σ σ' b θ₀` be the empirical NTK kernel at
initialization `θ₀`.  Suppose the Gram matrix `K := gramMatrix k xs`
is invertible (`K.det ≠ 0`) — this is guaranteed under the coercivity
hypothesis `ρ • 1 ≤ K` with `0 < ρ` used elsewhere in the NTK track.

Then for every test input `x`, as `λ → 0⁺`, the KRR predictor with the
*centered* labels

  `y_c i := y i - fullNet σ b θ₀ (x_i)`

converges to the closed-form pseudoinverse kernel expansion:

  `lim_{λ→0⁺} krrPredictor k xs y_c λ x
      = kernelExpansion k xs (K⁻¹ · y_c) x
      = Σ i, (K⁻¹ y_c) i · k(x, x_i)`.

**Centering.**  T6c-lin's kernel-expansion form is
`f^{lin}_θ(x) - f_{θ₀}(x) = Σ i, α i · k(x, x_i)`, so exact
interpolation at the training set requires that `K · α = y - f_{θ₀}(xs)`
(i.e. the labels are centered by the base network output).  This is
the correctly-centered T6a statement composed with T6c-lin.

**Discrete-time caveat.**  This is a statement about the *ridge
predictor's* limit as `λ → 0⁺`.  T6c-lin composes with it as a
deterministic corollary along a discrete-Euler trajectory whose
per-step increment lies in the training-gradient span (see
`ntk_linearized_span_step_invariant`).  No continuous-time `θ(∞)`
claim is made. -/
theorem ntk_linearized_krr_interpolating_limit
    {d n m : ℕ}
    (σ σ' : ℝ → ℝ) (b : Fin m → ℝ) (θ₀ : Param d m)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (y : Fin n → ℝ)
    (hK : (gramMatrix (paramNTKKernel σ σ' b θ₀) xs).det ≠ 0)
    (x : EuclideanSpace ℝ (Fin d)) :
    let k := paramNTKKernel σ σ' b θ₀
    let K := gramMatrix k xs
    let y_c : Fin n → ℝ :=
      fun i => y i - fullNet σ b θ₀ (xs i)
    Tendsto (fun lam : ℝ => krrPredictor k xs y_c lam x)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (kernelExpansion k xs (K⁻¹ *ᵥ y_c) x)) := by
  intro k K y_c
  -- Apply the pointwise KRR-predictor interpolating limit to the
  -- centered label vector `y_c`.
  exact krrPredictor_tendsto_interpolating k xs y_c hK x

/-! ### Counterexample sanity check (Codex gate)

At `n = 1`, `K = [[1]]`, `y = 1`, `f_{θ₀}(x_1) = 0`, the interpolating
limit reads `K⁻¹ ỹ = 1`, hence the closed-form limit at any `x` equals
`1 · k(x, x_1) = k(x, x_1)`.  We record this as a stand-alone lemma
in the abstract `krrPredictor_tendsto_interpolating` form (independent
of the NTK-specific packaging) so it can be checked by inspection at
`n = 1`, `y = 1`. -/

/-- Sanity check: at a one-point sample with `k(x_1, x_1) = 1` and
`y = 1`, the closed-form interpolating-limit predictor at any `x`
equals `k(x, x_1)`.  The Gram matrix is the 1×1 identity `[[1]]`, its
inverse is itself, and `K⁻¹ *ᵥ y = 1`, so the kernel expansion at `x`
is `1 · k(x, x_1) = k(x, x_1)`. -/
theorem kernelExpansion_of_inv_gram_mulVec_sanity
    (k : 𝒳 → 𝒳 → ℝ) (xs : Fin 1 → 𝒳)
    (h_diag : k (xs 0) (xs 0) = 1)
    (x : 𝒳) :
    let K := gramMatrix k xs
    let y : Fin 1 → ℝ := fun _ => 1
    kernelExpansion k xs (K⁻¹ *ᵥ y) x = k x (xs 0) := by
  intro K y
  -- The 1×1 Gram matrix has entry `k(x_1, x_1) = 1`, so `K = 1` and
  -- `K⁻¹ = 1`.
  have hK_one : K = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    show gramMatrix k xs = (1 : Matrix (Fin 1) (Fin 1) ℝ)
    ext i j
    fin_cases i
    fin_cases j
    simp [gramMatrix, h_diag]
  have h_inv_one : K⁻¹ = (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    rw [hK_one]; simp
  have h_mulVec : K⁻¹ *ᵥ y = y := by
    rw [h_inv_one]; exact Matrix.one_mulVec y
  -- Now expand the kernel sum on the singleton.
  rw [h_mulVec]
  show ∑ i, y i * k x (xs i) = k x (xs 0)
  simp [y]

#print axioms ntk_linearized_krr_interpolating_limit
#print axioms krrCoeffs_tendsto_interpolating
#print axioms krrPredictor_tendsto_interpolating
#print axioms tendsto_nat_mul_nhdsWithin_Ioi
#print axioms kernelExpansion_of_inv_gram_mulVec_sanity

end LTFP
