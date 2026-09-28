/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Analysis.ParamL2
import LTFP.MathlibExt.Calculus.FullNetworkContDiff2Smooth
import LTFP.MathlibExt.Probability.FullNetworkFrechet
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# `fullNetL2` — the two-layer predictor viewed as a function of an L² parameter

**R4 NTK L2 — L² parameter norm redesign, Phase 2.**

`ParamL2.lean` (Phase L1) introduces the flat L² parameter space
`ParamL2 d m := EuclideanSpace ℝ (Fin (m + m * d))` and the linear
equivalence `paramL2Equiv d m : ParamL2 d m ≃ₗ[ℝ] Param d m`.  The
existing `fullNet σ b θ x` predictor is defined on the sup-normed
`Param d m`.  This file lifts the predictor to `ParamL2 d m` and
transports the `ContDiff ℝ 2` structure and the Fréchet-derivative
identity from Phase 2a through the linear-equivalence bridge.

The key output is `fullNetL2_iteratedFDeriv_two`, which expresses the
second iterated Fréchet derivative of `fullNetL2` as a
`compContinuousLinearMap` pullback of the sup-norm second iterated
Fréchet derivative through `paramL2EquivCLE`.  Phase L3 will Cauchy-
Schwarz the resulting bilinear form over the flat L² coordinates to
recover the correct `L₀ / √m` Chizat-Bach rate.

## Layout

`ParamL2 d m` is finite-dimensional (a `EuclideanSpace` over `Fin (m + m * d)`).
`Param d m` is a product of `Fin m → ℝ` and `Fin m → EuclideanSpace ℝ (Fin d)`,
also finite-dimensional.  Between finite-dimensional real normed spaces every
`ℝ`-linear equivalence promotes to a continuous linear equivalence via
`LinearEquiv.toContinuousLinearEquiv`.

## Main definitions

* `paramL2EquivCLE d m : ParamL2 d m ≃L[ℝ] Param d m` — the continuous
  promotion of `paramL2Equiv d m`.
* `fullNetL2 σ b θ x` — the two-layer predictor as a function of the
  flat L² parameter: `fullNet σ b (paramL2EquivCLE θ) x`.

## Main results

* `fullNetL2_contDiff_two` — `θ ↦ fullNetL2 σ b θ x` is `ContDiff ℝ 2`
  in the L² parameter, when `σ` is `ContDiff ℝ 2`.
* `fullNetL2_hasFDerivAt` — the Fréchet derivative of `fullNetL2` at
  `θ` is the composition of the sup-norm Fréchet derivative at
  `paramL2EquivCLE θ` with the CLE.
* `fullNetL2_fderiv` — the same statement in `fderiv` form.
* `fullNetL2_iteratedFDeriv_two` — the L² second iterated Fréchet
  derivative equals the sup-norm second iterated Fréchet derivative
  composed with `paramL2EquivCLE` on all input slots.
* `fullNetL2_hessian_bilinear_form` — evaluated on tangent vectors
  `v u : ParamL2 d m`, the L² second iterated Fréchet derivative
  equals the sup-norm one on the unwrapped tangent vectors
  `ParamL2.toParam v` and `ParamL2.toParam u`.  This is the identity
  that Phase L3 Cauchy-Schwarzes.

## Sanity check

At `d = m = 1, σ = softplus, a₁ = 1, w₁ = (0), b₁ = 0, x = (1)`:
`fullNetL2 softplus b θ x = fullNet softplus b (toParam θ) x
                          = (1/√1) · 1 · softplus(0) = log 2`
which we unit-test symbolically via `Real.softplus_zero`.
-/

namespace ProbabilityTheory

open BigOperators Real

variable {d m : ℕ}

/-! ### The continuous linear equivalence -/

/-- **Continuous linear equivalence** `ParamL2 d m ≃L[ℝ] Param d m`.

Both spaces are finite-dimensional real normed spaces, so the abstract
`ℝ`-linear equivalence `paramL2Equiv d m` from `ParamL2.lean`
promotes to a continuous linear equivalence via
`LinearEquiv.toContinuousLinearEquiv`.  This is NOT an isometry — the
norms differ by the sup/L² gap quantified in
`param_sup_le_paramL2` and `paramL2_le_scale_param_sup`.  It IS
continuous both ways, which is all that is needed for the chain-rule
composition of `ContDiff` and `iteratedFDeriv`. -/
noncomputable def paramL2EquivCLE (d m : ℕ) : ParamL2 d m ≃L[ℝ] Param d m :=
  (paramL2Equiv d m).toContinuousLinearEquiv

@[simp]
theorem paramL2EquivCLE_apply (θ : ParamL2 d m) :
    paramL2EquivCLE d m θ = ParamL2.toParam θ := rfl

@[simp]
theorem paramL2EquivCLE_symm_apply (θ : Param d m) :
    (paramL2EquivCLE d m).symm θ = ParamL2.ofParam θ := rfl

/-! ### The L² predictor -/

/-- **The two-layer predictor as a function of an L² parameter.**

Definitionally `fullNet σ b (ParamL2.toParam θ) x`, i.e. we unwrap the
flat L² vector into the sup-normed `Param d m` and feed the existing
`fullNet` predictor.  The advantage of `fullNetL2` over `fullNet` for
Chizat-Bach analysis is that the parameter space now carries a native
L² norm, so the Fréchet Hessian bound can be Cauchy-Schwarzed at the
correct rate `L₀ / √m`. -/
noncomputable def fullNetL2
    (σ : ℝ → ℝ)
    (b : Fin m → ℝ)
    (θ : ParamL2 d m)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  fullNet σ b (ParamL2.toParam θ) x

/-- Unfolding lemma: `fullNetL2` is `fullNet` composed with the unwrap map. -/
theorem fullNetL2_eq_comp
    (σ : ℝ → ℝ) (b : Fin m → ℝ) (x : EuclideanSpace ℝ (Fin d)) :
    (fun θ : ParamL2 d m => fullNetL2 σ b θ x) =
      (fun θ' : Param d m => fullNet σ b θ' x) ∘ (paramL2EquivCLE d m) := by
  funext θ
  rfl

/-! ### Smoothness -/

/-- **`fullNetL2 σ b · x` is `ContDiff ℝ 2` in the L² parameter.**

The predictor factors as `fullNet σ b · x ∘ paramL2EquivCLE`.  The CLE is
smooth (any continuous linear map is `ContDiff`), and the sup-norm
predictor is `ContDiff ℝ 2` by Phase 2a's `fullNet_contDiff_two`.  The
composition inherits `ContDiff ℝ 2`. -/
theorem fullNetL2_contDiff_two
    (σ : ℝ → ℝ)
    (hσ : ContDiff ℝ 2 σ)
    (b : Fin m → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    ContDiff ℝ 2 (fun θ : ParamL2 d m => fullNetL2 σ b θ x) := by
  rw [fullNetL2_eq_comp σ b x]
  have h_fullNet : ContDiff ℝ 2 (fun θ' : Param d m => fullNet σ b θ' x) :=
    fullNet_contDiff_two (d := d) σ hσ b x
  exact h_fullNet.comp (paramL2EquivCLE d m).contDiff

/-- More general `ContDiff n` version, useful for the softplus (C^∞)
instantiation. -/
theorem fullNetL2_contDiff
    {n : WithTop ℕ∞}
    (σ : ℝ → ℝ)
    (hσ : ContDiff ℝ n σ)
    (b : Fin m → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    ContDiff ℝ n (fun θ : ParamL2 d m => fullNetL2 σ b θ x) := by
  rw [fullNetL2_eq_comp σ b x]
  have h_fullNet : ContDiff ℝ n (fun θ' : Param d m => fullNet σ b θ' x) :=
    fullNet_contDiff (n := n) (d := d) σ hσ b x
  exact h_fullNet.comp (paramL2EquivCLE d m).contDiff

/-- Softplus-specific `C^∞` corollary. -/
theorem fullNetL2_softplus_contDiff
    {n : WithTop ℕ∞}
    (b : Fin m → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    ContDiff ℝ n
      (fun θ : ParamL2 d m => fullNetL2 Real.softplus b θ x) :=
  fullNetL2_contDiff (n := n) Real.softplus Real.contDiff_softplus b x

/-! ### Fréchet derivative -/

/-- **Fréchet differentiability (as `HasFDerivAt`) of `fullNetL2` in
the L² parameter.**

If the sup-norm predictor `fullNet σ b · x` has a Fréchet derivative
`Φ` at the unwrapped parameter `paramL2EquivCLE θ`, then `fullNetL2`
has a Fréchet derivative at `θ` equal to `Φ.comp paramL2EquivCLE`.
This is the standard chain rule composition through the CLE. -/
theorem fullNetL2_hasFDerivAt
    (σ : ℝ → ℝ)
    (b : Fin m → ℝ)
    (θ : ParamL2 d m)
    (x : EuclideanSpace ℝ (Fin d))
    {Φ : Param d m →L[ℝ] ℝ}
    (hΦ : HasFDerivAt (fun θ' : Param d m => fullNet σ b θ' x) Φ
      (paramL2EquivCLE d m θ)) :
    HasFDerivAt (fun θ' : ParamL2 d m => fullNetL2 σ b θ' x)
      (Φ.comp ((paramL2EquivCLE d m) : ParamL2 d m →L[ℝ] Param d m)) θ := by
  have h_lin :
      HasFDerivAt (fun θ' : ParamL2 d m => (paramL2EquivCLE d m) θ')
        ((paramL2EquivCLE d m) : ParamL2 d m →L[ℝ] Param d m) θ :=
    ((paramL2EquivCLE d m) : ParamL2 d m →L[ℝ] Param d m).hasFDerivAt
  exact hΦ.comp θ h_lin

/-- **`fderiv` form of the L² Fréchet derivative identity.**

The `fderiv` of `fullNetL2 σ b · x` at `θ` is the CLM-composition of
the sup-norm `fderiv` at `paramL2EquivCLE θ` with the CLE `paramL2EquivCLE`.

This states the derivative of a composition `f ∘ g` at `θ`:
`fderiv (f ∘ g) θ = (fderiv f (g θ)).comp (fderiv g θ)`,
with `g = paramL2EquivCLE` (a CLM), so `fderiv g θ = g` as CLMs. -/
theorem fullNetL2_fderiv
    (σ : ℝ → ℝ)
    (hσ_diff : Differentiable ℝ σ)
    (b : Fin m → ℝ)
    (θ : ParamL2 d m)
    (x : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fun θ' : ParamL2 d m => fullNetL2 σ b θ' x) θ =
      (fderiv ℝ (fun θ' : Param d m => fullNet σ b θ' x)
        (paramL2EquivCLE d m θ)).comp
        ((paramL2EquivCLE d m) : ParamL2 d m →L[ℝ] Param d m) := by
  have h_diff : DifferentiableAt ℝ
      (fun θ' : Param d m => fullNet σ b θ' x) (paramL2EquivCLE d m θ) :=
    (fullNet_differentiable_param (d := d) σ hσ_diff b x) _
  have hΦ : HasFDerivAt (fun θ' : Param d m => fullNet σ b θ' x)
      (fderiv ℝ (fun θ' : Param d m => fullNet σ b θ' x)
        (paramL2EquivCLE d m θ))
      (paramL2EquivCLE d m θ) := h_diff.hasFDerivAt
  exact (fullNetL2_hasFDerivAt σ b θ x hΦ).fderiv

/-- **Pointwise Fréchet-derivative identity on a tangent vector `v`.**

For a differentiable `σ`, the Fréchet derivative of `fullNetL2 σ b · x`
at `θ` in direction `v` equals the Fréchet derivative of `fullNet σ b · x`
at `paramL2EquivCLE θ` in direction `paramL2EquivCLE v`.  This is the
pointwise chain rule that Phase 3 uses to relate `∇_L² fullNetL2` to
`∇_sup fullNet`. -/
theorem fullNetL2_fderiv_apply
    (σ : ℝ → ℝ)
    (hσ_diff : Differentiable ℝ σ)
    (b : Fin m → ℝ)
    (θ v : ParamL2 d m)
    (x : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (fun θ' : ParamL2 d m => fullNetL2 σ b θ' x) θ v =
      fderiv ℝ (fun θ' : Param d m => fullNet σ b θ' x)
        (paramL2EquivCLE d m θ) (paramL2EquivCLE d m v) := by
  rw [fullNetL2_fderiv σ hσ_diff b θ x]
  rfl

/-! ### Second iterated Fréchet derivative -/

/-- **L² iterated Fréchet derivative in terms of the sup-norm one.**

For a `ContDiff ℝ n` activation `σ`, the L² `i`-th iterated Fréchet
derivative of `fullNetL2` at `θ` is the sup-norm one at
`paramL2EquivCLE θ` composed on every input slot with the CLE
`paramL2EquivCLE`.

This is the direct application of `ContinuousLinearMap.iteratedFDeriv_comp_right`
to the decomposition `fullNetL2 σ b · x = fullNet σ b · x ∘ paramL2EquivCLE`. -/
theorem fullNetL2_iteratedFDeriv
    {n : WithTop ℕ∞}
    (σ : ℝ → ℝ)
    (hσ : ContDiff ℝ n σ)
    (b : Fin m → ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (θ : ParamL2 d m)
    {i : ℕ} (hi : (i : WithTop ℕ∞) ≤ n) :
    iteratedFDeriv ℝ i (fun θ' : ParamL2 d m => fullNetL2 σ b θ' x) θ =
      (iteratedFDeriv ℝ i
        (fun θ' : Param d m => fullNet σ b θ' x)
        (paramL2EquivCLE d m θ)).compContinuousLinearMap
        (fun _ : Fin i =>
          ((paramL2EquivCLE d m) : ParamL2 d m →L[ℝ] Param d m)) := by
  have h_fullNet : ContDiff ℝ n
      (fun θ' : Param d m => fullNet σ b θ' x) :=
    fullNet_contDiff (n := n) (d := d) σ hσ b x
  have h_eq :
      (fun θ' : ParamL2 d m => fullNetL2 σ b θ' x) =
        (fun θ' : Param d m => fullNet σ b θ' x) ∘
          ((paramL2EquivCLE d m) : ParamL2 d m →L[ℝ] Param d m) := by
    funext θ'; rfl
  rw [h_eq]
  exact ((paramL2EquivCLE d m) :
    ParamL2 d m →L[ℝ] Param d m).iteratedFDeriv_comp_right h_fullNet θ hi

/-- **L² second iterated Fréchet derivative** — the Phase L3 substrate.

For a `ContDiff ℝ 2` activation `σ`, the L² second iterated Fréchet
derivative equals the sup-norm one composed with the CLE on both input
slots.  This is `fullNetL2_iteratedFDeriv` specialized at `i = 2`. -/
theorem fullNetL2_iteratedFDeriv_two
    (σ : ℝ → ℝ)
    (hσ : ContDiff ℝ 2 σ)
    (b : Fin m → ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (θ : ParamL2 d m) :
    iteratedFDeriv ℝ 2 (fun θ' : ParamL2 d m => fullNetL2 σ b θ' x) θ =
      (iteratedFDeriv ℝ 2
        (fun θ' : Param d m => fullNet σ b θ' x)
        (paramL2EquivCLE d m θ)).compContinuousLinearMap
        (fun _ : Fin 2 =>
          ((paramL2EquivCLE d m) : ParamL2 d m →L[ℝ] Param d m)) := by
  exact fullNetL2_iteratedFDeriv (n := 2) σ hσ b x θ (le_refl _)

/-- **Bilinear form of the L² Hessian.**

Evaluated on tangent vectors `v u : ParamL2 d m`, the L² second
iterated Fréchet derivative equals the sup-norm second iterated
Fréchet derivative evaluated on the unwrapped tangent vectors
`ParamL2.toParam v` and `ParamL2.toParam u`.

This is the identity that Phase L3 will Cauchy-Schwarz over the
flat L² coordinates.  The sup-norm bilinear form (RHS) is what the
Phase 2a explicit-softplus development pointwise-bounds; the L² norm
of `v, u` on the LHS is the natural pairing under which the Chizat-
Bach `L₀ / √m` rate holds. -/
theorem fullNetL2_hessian_bilinear_form
    (σ : ℝ → ℝ)
    (hσ : ContDiff ℝ 2 σ)
    (b : Fin m → ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (θ v u : ParamL2 d m) :
    iteratedFDeriv ℝ 2 (fun θ' : ParamL2 d m => fullNetL2 σ b θ' x) θ
        ![v, u] =
      iteratedFDeriv ℝ 2 (fun θ' : Param d m => fullNet σ b θ' x)
        (paramL2EquivCLE d m θ)
        ![ParamL2.toParam v, ParamL2.toParam u] := by
  rw [fullNetL2_iteratedFDeriv_two σ hσ b x θ]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  -- The remaining goal is that
  --   iteratedFDeriv ℝ 2 (…) (…) (fun i => paramL2EquivCLE (![v, u] i))
  -- equals
  --   iteratedFDeriv ℝ 2 (…) (…) ![toParam v, toParam u].
  -- Both index families are equal componentwise (Fin 2 has two indices).
  congr 1
  funext i
  fin_cases i <;> rfl

/-- **Continuity of the L² second Fréchet derivative in `θ`.**

For a `ContDiff ℝ 2` activation `σ`, the map
`θ ↦ iteratedFDeriv ℝ 2 (fullNetL2 σ b · x) θ` is continuous.  This is
`ContDiff.continuous_iteratedFDeriv` applied to `fullNetL2_contDiff_two`. -/
theorem fullNetL2_iteratedFDeriv_two_continuous
    (σ : ℝ → ℝ)
    (hσ : ContDiff ℝ 2 σ)
    (b : Fin m → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    Continuous (fun θ : ParamL2 d m =>
      iteratedFDeriv ℝ 2 (fun θ' : ParamL2 d m => fullNetL2 σ b θ' x) θ) :=
  (fullNetL2_contDiff_two (d := d) σ hσ b x).continuous_iteratedFDeriv
    (m := 2) (by norm_num)

end ProbabilityTheory

/-! ### Sanity check

At `d = m = 1, σ = softplus, a₁ = 1, w₁ = (0), b₁ = 0, x = (1)`, the
L² predictor reduces to `softplus 0 = log 2`.  Since `fullNetL2` is
definitionally `fullNet σ b (toParam θ) x` and `toParam` unwraps the
flat coordinates back into `(a, w)` layout, this is the same numerical
value as the sup-norm `fullNet`.

We record a symbolic identity confirming the reduction. -/
section SanityCheck

/-- Sanity: `fullNetL2 σ b θ x = fullNet σ b (ParamL2.toParam θ) x` by
definition — a `#eval`-style reminder in theorem form. -/
theorem ProbabilityTheory.fullNetL2_def_eq
    {d m : ℕ}
    (σ : ℝ → ℝ) (b : Fin m → ℝ) (θ : ProbabilityTheory.ParamL2 d m)
    (x : EuclideanSpace ℝ (Fin d)) :
    ProbabilityTheory.fullNetL2 σ b θ x =
      ProbabilityTheory.fullNet σ b (ProbabilityTheory.ParamL2.toParam θ) x :=
  rfl

end SanityCheck
