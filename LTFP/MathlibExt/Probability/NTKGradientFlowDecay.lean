/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.NTKGradientFlowResidual
import LTFP.MathlibExt.Probability.ResidualGronwallDecay
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Residual decay and parameter movement on `[0, T]`

Interval versions of the Grönwall decay and movement estimates for the
explicit gradient flow of `fullNet`. All hypotheses are stated on
`[0, s]` only: continuity on `Icc 0 s` and one-sided derivatives within
`Ici t` for `t ∈ Ico 0 s`.

## Main results

* `sq_norm_le_of_hasDerivWithinAt_neg_coercive` — if `r' = -K(t) r` and
  `⟪r, K(t) r⟫ ≥ c ‖r‖²` on `[0, s)`, then `‖r t‖² ≤ ‖r 0‖² e^{-2ct}`.
* `inner_toEuclideanLin_ge_of_loewner` — Loewner coercivity
  `(ρ/2) • 1 ≤ K` gives the quadratic-form lower bound.
* `gfFieldFullNet_neuron_norm_le` — per-neuron bound on the flow field
  in terms of the residual norm.
* `neuron_dist_le_of_deriv_exp_decay` — per-neuron movement from an
  exponentially decaying velocity bound.
-/

namespace ProbabilityTheory

open BigOperators Real Matrix LTFP Set
open scoped InnerProductSpace MatrixOrder

variable {d n m : ℕ}

/-! ### Grönwall decay on `[0, s]` -/

/-- **Interval Grönwall decay.** If `r' = -K(t) r` (right derivative) and
`c ‖r‖² ≤ ⟪r, K(t) r⟫` on `[0, s)`, with `r` continuous on `[0, s]`, then
`‖r t‖² ≤ ‖r 0‖² · exp (-(2 c t))` on `[0, s]`. -/
theorem sq_norm_le_of_hasDerivWithinAt_neg_coercive
    (r : ℝ → EuclideanSpace ℝ (Fin n)) (K : ℝ → Matrix (Fin n) (Fin n) ℝ)
    (s c : ℝ) (hcont : ContinuousOn r (Icc 0 s))
    (hder : ∀ t ∈ Ico 0 s,
      HasDerivWithinAt r (-(Matrix.toEuclideanLin (K t)) (r t)) (Ici t) t)
    (hcoer : ∀ t ∈ Ico 0 s,
      c * ‖r t‖ ^ 2 ≤ ⟪r t, Matrix.toEuclideanLin (K t) (r t)⟫_ℝ) :
    ∀ t ∈ Icc 0 s, ‖r t‖ ^ 2 ≤ ‖r 0‖ ^ 2 * Real.exp (-(2 * c * t)) := by
  set g : ℝ → ℝ := fun t => ‖r t‖ ^ 2 * Real.exp (2 * c * t) with hg
  have hexp : ∀ t, HasDerivAt (fun u => Real.exp (2 * c * u))
      (Real.exp (2 * c * t) * (2 * c)) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ => 2 * c * u) (2 * c) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * c)
    exact (Real.hasDerivAt_exp _).comp t h1
  have hgder : ∀ t ∈ Ico 0 s, HasDerivWithinAt g
      (2 * ⟪r t, -(Matrix.toEuclideanLin (K t)) (r t)⟫_ℝ * Real.exp (2 * c * t)
        + ‖r t‖ ^ 2 * (Real.exp (2 * c * t) * (2 * c))) (Ici t) t := by
    intro t ht
    exact ((hder t ht).norm_sq).mul (hexp t).hasDerivWithinAt
  have hgcont : ContinuousOn g (Icc 0 s) := by
    refine ContinuousOn.mul ?_ (Continuous.continuousOn (by fun_prop))
    exact (continuous_norm.comp_continuousOn hcont).pow 2
  have hmain : ∀ ⦃t⦄, t ∈ Icc 0 s → g t ≤ (fun _ => g 0) t := by
    refine image_le_of_deriv_right_le_deriv_boundary (B := fun _ => g 0) (B' := fun _ => 0)
      hgcont hgder le_rfl continuousOn_const (fun t _ => hasDerivWithinAt_const _ _ _) ?_
    intro t ht
    have hc := hcoer t ht
    have hpos := Real.exp_pos (2 * c * t)
    rw [inner_neg_right]
    have : (2 * -⟪r t, Matrix.toEuclideanLin (K t) (r t)⟫_ℝ
        + ‖r t‖ ^ 2 * (2 * c)) * Real.exp (2 * c * t) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by nlinarith) hpos.le
    linarith
  intro t ht
  have h := hmain ht
  simp only [hg, mul_zero, Real.exp_zero, mul_one] at h
  have hpos := Real.exp_pos (2 * c * t)
  have hexp_mul : Real.exp (-(2 * c * t)) * Real.exp (2 * c * t) = 1 := by
    rw [← Real.exp_add]; simp
  calc ‖r t‖ ^ 2 = ‖r t‖ ^ 2 * Real.exp (2 * c * t) * Real.exp (-(2 * c * t)) := by
        rw [mul_assoc, mul_comm (Real.exp _) (Real.exp _), hexp_mul, mul_one]
    _ ≤ ‖r 0‖ ^ 2 * Real.exp (-(2 * c * t)) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le

/-- Loewner coercivity `(ρ/2) • 1 ≤ K` gives
`(ρ/2) ‖x‖² ≤ ⟪x, K x⟫` on Euclidean space. -/
theorem inner_toEuclideanLin_ge_of_loewner
    {K : Matrix (Fin n) (Fin n) ℝ} {ρ : ℝ}
    (hK : (ρ / 2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ K)
    (x : EuclideanSpace ℝ (Fin n)) :
    ρ / 2 * ‖x‖ ^ 2 ≤ ⟪x, Matrix.toEuclideanLin K x⟫_ℝ := by
  have h := quadForm_lb_of_loewner_coercive hK (WithLp.ofLp x)
  have hstar : (star (WithLp.ofLp x) : Fin n → ℝ) = WithLp.ofLp x := by
    funext i; simp
  have h1 : ⟪x, Matrix.toEuclideanLin K x⟫_ℝ =
      WithLp.ofLp x ⬝ᵥ (K *ᵥ WithLp.ofLp x) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, hstar, Matrix.ofLp_toEuclideanLin_apply,
      dotProduct_comm]
  have h2 : ‖x‖ ^ 2 = WithLp.ofLp x ⬝ᵥ WithLp.ofLp x := by
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, hstar]
  rw [h1, h2]
  exact h

/-! ### Per-neuron bound on the flow field -/

/-- `∑ i, |r i| ≤ √n · ‖r‖` on `EuclideanSpace ℝ (Fin n)`. -/
theorem sum_abs_le_sqrt_card_mul_norm (r : EuclideanSpace ℝ (Fin n)) :
    ∑ i, |r i| ≤ Real.sqrt n * ‖r‖ := by
  have hsq : (∑ i, |r i|) ^ 2 ≤ (n : ℝ) * ‖r‖ ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
      (f := fun i => |r i|)
    rw [EuclideanSpace.norm_sq_eq]
    simpa [Real.norm_eq_abs, sq_abs] using h
  have hnn : 0 ≤ ∑ i, |r i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  rw [← Real.sqrt_sq (norm_nonneg r), ← Real.sqrt_mul (Nat.cast_nonneg n)]
  exact (Real.le_sqrt hnn (by positivity)).2 hsq

/-- First block of the flow field, neuron `j`. -/
theorem gfFieldFullNet_fst_apply
    (σ : ℝ → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) (θ : Param d m) (j : Fin m) :
    (gfFieldFullNet σ b y xs θ).1 j =
      ∑ i, (y i - fullNet σ b θ (xs i)) *
        ((1 / Real.sqrt m) * σ (inner ℝ (θ.2 j) (xs i) + b j)) := by
  simp [gfFieldFullNet, Prod.fst_sum, Finset.sum_apply, gradFullNet]

/-- Second block of the flow field, neuron `j`. -/
theorem gfFieldFullNet_snd_apply
    (σ : ℝ → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) (θ : Param d m) (j : Fin m) :
    (gfFieldFullNet σ b y xs θ).2 j =
      ∑ i, (y i - fullNet σ b θ (xs i)) •
        (((1 / Real.sqrt m) * θ.1 j * deriv σ (inner ℝ (θ.2 j) (xs i) + b j)) • xs i) := by
  simp [gfFieldFullNet, Prod.snd_sum, Finset.sum_apply, gradFullNet]

/-- **Per-neuron flow-field bound (G2b).** If `|σ| ≤ M`, `|σ'| ≤ M'`,
`‖xs i‖ ≤ X` and `|a_j| ≤ A`, then the neuron-`j` block of the flow field
has norm at most `(1/√m) (M + A M' X) √n ‖r‖`. -/
theorem gfFieldFullNet_neuron_norm_le
    (σ : ℝ → ℝ) (b : Fin m → ℝ) (y : Fin n → ℝ)
    (xs : Fin n → EuclideanSpace ℝ (Fin d)) (θ : Param d m) (j : Fin m)
    {M M' X A : ℝ} (hσ_bdd : ∀ z, |σ z| ≤ M) (hσ'_bdd : ∀ z, |deriv σ z| ≤ M')
    (hX0 : 0 ≤ X) (hX : ∀ i, ‖xs i‖ ≤ X) (hA : |θ.1 j| ≤ A) :
    ‖((gfFieldFullNet σ b y xs θ).1 j, (gfFieldFullNet σ b y xs θ).2 j)‖ ≤
      (1 / Real.sqrt m) * (M + A * M' * X) *
        (Real.sqrt n * ‖residualFullNet σ b y xs θ‖) := by
  have hM : 0 ≤ M := (abs_nonneg _).trans (hσ_bdd 0)
  have hM' : 0 ≤ M' := (abs_nonneg _).trans (hσ'_bdd 0)
  have hA0 : 0 ≤ A := (abs_nonneg _).trans hA
  have hc : 0 ≤ 1 / Real.sqrt m := by positivity
  set S := ∑ i, |residualFullNet σ b y xs θ i| with hS
  have hSnn : 0 ≤ S := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hSle : S ≤ Real.sqrt n * ‖residualFullNet σ b y xs θ‖ :=
    sum_abs_le_sqrt_card_mul_norm _
  have habs : ∀ i, |y i - fullNet σ b θ (xs i)| = |residualFullNet σ b y xs θ i| := by
    intro i; rw [residualFullNet_apply, abs_sub_comm]
  have h1 : ‖(gfFieldFullNet σ b y xs θ).1 j‖ ≤ (1 / Real.sqrt m) * M * S := by
    rw [gfFieldFullNet_fst_apply, Real.norm_eq_abs]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [hS, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [abs_mul, habs, abs_mul, abs_of_nonneg hc]
    have := hσ_bdd (inner ℝ (θ.2 j) (xs i) + b j)
    have hr := abs_nonneg (residualFullNet σ b y xs θ i)
    nlinarith [mul_le_mul_of_nonneg_left this hc]
  have h2 : ‖(gfFieldFullNet σ b y xs θ).2 j‖ ≤ (1 / Real.sqrt m) * (A * M' * X) * S := by
    rw [gfFieldFullNet_snd_apply]
    refine (norm_sum_le _ _).trans ?_
    rw [hS, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, habs, abs_mul, abs_mul,
      abs_of_nonneg hc]
    have hs := hσ'_bdd (inner ℝ (θ.2 j) (xs i) + b j)
    have hx := hX i
    have hr := abs_nonneg (residualFullNet σ b y xs θ i)
    have hxn := norm_nonneg (xs i)
    have hq : |θ.1 j| * |deriv σ (inner ℝ (θ.2 j) (xs i) + b j)| * ‖xs i‖ ≤
        A * M' * X := by
      gcongr
    have hq' : 1 / Real.sqrt m * |θ.1 j| * |deriv σ (inner ℝ (θ.2 j) (xs i) + b j)| *
        ‖xs i‖ ≤ 1 / Real.sqrt m * (A * M' * X) := by
      have := mul_le_mul_of_nonneg_left hq hc
      linarith [show 1 / Real.sqrt m * |θ.1 j| * |deriv σ (inner ℝ (θ.2 j) (xs i) + b j)|
          * ‖xs i‖ = 1 / Real.sqrt m * (|θ.1 j| * |deriv σ (inner ℝ (θ.2 j) (xs i) + b j)|
          * ‖xs i‖) by ring]
    calc |residualFullNet σ b y xs θ i| *
          (1 / Real.sqrt m * |θ.1 j| * |deriv σ (inner ℝ (θ.2 j) (xs i) + b j)| * ‖xs i‖)
        ≤ |residualFullNet σ b y xs θ i| * (1 / Real.sqrt m * (A * M' * X)) :=
          mul_le_mul_of_nonneg_left hq' hr
      _ = 1 / Real.sqrt m * (A * M' * X) * |residualFullNet σ b y xs θ i| := by ring
  have hAMX : 0 ≤ A * M' * X := by positivity
  have hS' := mul_le_mul_of_nonneg_left hSle (by positivity :
    (0 : ℝ) ≤ 1 / Real.sqrt m * (M + A * M' * X))
  rw [Prod.norm_mk, max_le_iff]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hSnn (by positivity :
      (0 : ℝ) ≤ 1 / Real.sqrt m * (A * M' * X))]
  · nlinarith [mul_le_mul_of_nonneg_left hSnn (by positivity :
      (0 : ℝ) ≤ 1 / Real.sqrt m * M)]

/-! ### Per-neuron movement on `[0, s]` -/

/-- The continuous linear projection onto the neuron-`j` block. -/
noncomputable def neuronProj (j : Fin m) :
    Param d m →L[ℝ] ℝ × EuclideanSpace ℝ (Fin d) :=
  ((ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.fst ℝ (Fin m → ℝ) (Fin m → EuclideanSpace ℝ (Fin d)))).prod
    ((ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.snd ℝ (Fin m → ℝ) (Fin m → EuclideanSpace ℝ (Fin d))))

@[simp]
theorem neuronProj_apply (j : Fin m) (θ : Param d m) :
    neuronProj j θ = (θ.1 j, θ.2 j) := rfl

/-- **Per-neuron movement from exponential velocity decay (G2c).** If
`θ' = V` (right derivative) on `[0, s)` and every neuron block of `V t`
has norm at most `K₀ e^{-ρ t / 2}`, then every neuron moves by at most
`(2/ρ) K₀` on `[0, s]`. -/
theorem neuron_dist_le_of_deriv_exp_decay
    (θ V : ℝ → Param d m) (s : ℝ) (hcont : ContinuousOn θ (Icc 0 s))
    (hder : ∀ t ∈ Ico 0 s, HasDerivWithinAt θ (V t) (Ici t) t)
    {K₀ ρ : ℝ} (hρ : 0 < ρ) (hK₀ : 0 ≤ K₀)
    (hbound : ∀ t ∈ Ico 0 s, ∀ j,
      ‖((V t).1 j, (V t).2 j)‖ ≤ K₀ * Real.exp (-(ρ / 2 * t))) :
    ∀ t ∈ Icc 0 s, ∀ j,
      dist ((θ t).1 j, (θ t).2 j) ((θ 0).1 j, (θ 0).2 j) ≤ 2 / ρ * K₀ := by
  intro t ht j
  set f : ℝ → ℝ × EuclideanSpace ℝ (Fin d) :=
    fun u => neuronProj j (θ u) - neuronProj j (θ 0) with hf
  set B : ℝ → ℝ := fun u => 2 / ρ * K₀ * (1 - Real.exp (-(ρ / 2 * u))) with hB
  have hfcont : ContinuousOn f (Icc 0 s) :=
    ((neuronProj j).continuous.comp_continuousOn hcont).sub continuousOn_const
  have hfder : ∀ u ∈ Ico 0 s, HasDerivWithinAt f (neuronProj j (V u)) (Ici u) u := by
    intro u hu
    exact ((neuronProj j).hasFDerivAt.comp_hasDerivWithinAt u (hder u hu)).sub_const _
  have hBder : ∀ u, HasDerivAt B (K₀ * Real.exp (-(ρ / 2 * u))) u := by
    intro u
    have h1 : HasDerivAt (fun v : ℝ => -(ρ / 2 * v)) (-(ρ / 2)) u := by
      simpa using ((hasDerivAt_id u).const_mul (ρ / 2)).neg
    have h2 := ((Real.hasDerivAt_exp _).comp u h1).const_sub 1
    have h3 := h2.const_mul (2 / ρ * K₀)
    convert h3 using 1
    field_simp
  have h0 : ‖f 0‖ ≤ B 0 := by simp [hf, hB]
  have hmain := image_norm_le_of_norm_deriv_right_le_deriv_boundary hfcont hfder h0 hBder
    (fun u hu => by simpa using hbound u hu j) ht
  rw [dist_eq_norm]
  calc ‖((θ t).1 j, (θ t).2 j) - ((θ 0).1 j, (θ 0).2 j)‖ = ‖f t‖ := rfl
    _ ≤ B t := hmain
    _ ≤ 2 / ρ * K₀ := by
      have : 0 ≤ 2 / ρ * K₀ * Real.exp (-(ρ / 2 * t)) := by positivity
      simp only [hB]
      nlinarith

end ProbabilityTheory
