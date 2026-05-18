/-
LTFP §8.3 — ℓ₁-regularization (Lasso).

Bach (2024) §8.3, pp. 231-243. Lasso minimizes
`(1/n)‖y − Xβ‖² + λ‖β‖₁`. The closed-form analysis on a single
coordinate (soft thresholding) is the workhorse of the chapter; full
slow / fast rates analysis is partly vendored from `lean-rademacher`
in `LTFP.Foundations.LinearPredictorL1`.

This file lands the **soft-thresholding** operator and a one-line
identity, plus a wrapper sum-of-absolute-values `l1Norm`.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Filter.Extr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Polyrith
import LTFP.MathlibExt.Analysis.Subgradient.L1

namespace LTFP

variable {d : ℕ}

/-- §8.3 — ℓ₁ norm `‖θ‖₁ = ∑ᵢ |θᵢ|`. -/
noncomputable def l1Norm (θ : Fin d → ℝ) : ℝ := ∑ i, |θ i|

/-- §8.3 sanity lemma: the ℓ₁-norm of the zero vector is zero. -/
theorem l1Norm_zero : l1Norm (0 : Fin d → ℝ) = 0 := by
  unfold l1Norm
  simp

/-- §8.3 — Soft-thresholding operator at level `λ ≥ 0`:
    `S_λ(z) = sign(z) · max(|z| − λ, 0)`. The closed-form solution of
    the one-dimensional Lasso `argmin_β ½(z − β)² + λ|β|`. -/
noncomputable def softThreshold (lam z : ℝ) : ℝ :=
  if 0 ≤ z then max (z - lam) 0 else min (z + lam) 0

/-- §8.3 sanity lemma: soft-thresholding at level `0` is the identity. -/
theorem softThreshold_zero (z : ℝ) : softThreshold 0 z = z := by
  unfold softThreshold
  by_cases h : 0 ≤ z
  · simp [h]
  · push_neg at h
    have hz : z ≤ 0 := le_of_lt h
    simp [h.not_ge, hz]

/-- §8.3 — The ℓ₁ norm is nonnegative. -/
theorem l1Norm_nonneg (θ : Fin d → ℝ) : 0 ≤ l1Norm θ := by
  unfold l1Norm
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- §8.3 — Triangle inequality for the ℓ₁ norm. -/
theorem l1Norm_add_le (θ ψ : Fin d → ℝ) :
    l1Norm (θ + ψ) ≤ l1Norm θ + l1Norm ψ := by
  unfold l1Norm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun i _ => ?_)
  show |θ i + ψ i| ≤ |θ i| + |ψ i|
  exact abs_add_le _ _

/-- §8.3 — Absolute homogeneity of ℓ₁ norm with `c = -1`:
    `‖-θ‖₁ = ‖θ‖₁`. -/
theorem l1Norm_neg (θ : Fin d → ℝ) :
    l1Norm (-θ) = l1Norm θ := by
  unfold l1Norm
  refine Finset.sum_congr rfl (fun i _ => ?_)
  show |(-θ) i| = |θ i|
  rw [Pi.neg_apply, abs_neg]

/-- §8.3 — ℓ₁ norm equals zero only at the zero vector. -/
theorem l1Norm_eq_zero_of_zero : l1Norm (0 : Fin d → ℝ) = 0 := l1Norm_zero

/-- §8.3 — Soft thresholding at level `0` of zero is zero. -/
theorem softThreshold_zero_zero : softThreshold 0 0 = 0 := by
  rw [softThreshold_zero]

/-- §8.3 — ℓ₁ norm of a single-coordinate vector is just |z|. -/
theorem l1Norm_fin_one (z : Fin 1 → ℝ) : l1Norm z = |z 0| := by
  unfold l1Norm
  simp

/-- §8.3 — ℓ₁ norm of a sum is bounded by sum of ℓ₁ norms (alias). -/
theorem l1Norm_triangle (θ ψ : Fin d → ℝ) :
    l1Norm (θ + ψ) ≤ l1Norm θ + l1Norm ψ := l1Norm_add_le θ ψ

/-- §8.3 — Soft thresholding fixed point at threshold equals zero. -/
theorem softThreshold_at_lam (lam : ℝ) (hlam : 0 ≤ lam) :
    softThreshold lam lam = 0 := by
  unfold softThreshold
  rw [if_pos hlam, sub_self]
  exact max_self 0

/-- §8.2 — **Scalar Lasso KKT (soft-thresholding).**

    For the one-dimensional Lasso objective
    `f(b) = ½(b − c)² + λ|b|` with regularization level `λ ≥ 0`,
    the global minimizer over all of `ℝ` is the soft-threshold
    `S_λ(c) = softThreshold λ c`. This is the closed-form expression of
    the KKT conditions for the scalar Lasso (Bach 2024 §8.2, eq. 8.10):
    `0 ∈ (b⋆ − c) + λ ∂|b⋆|`, equivalently
    `b⋆ = sign(c)·max(|c|−λ, 0)`.

    The vector form `Xᵀ(Xβ⋆ − y) ∈ −λ ∂‖β⋆‖₁` reduces to the scalar
    statement coordinate-wise when `XᵀX = I`; the general subdifferential
    calculus for ℓ₁ is currently a Mathlib gap (see project notes for
    `lasso-kkt`). -/
theorem lasso_kkt_scalar (c lam : ℝ) (hlam : 0 ≤ lam) :
    IsMinOn (fun b => (b - c) ^ 2 / 2 + lam * |b|) Set.univ
      (softThreshold lam c) := by
  intro b _
  -- Goal: f(softThreshold lam c) ≤ f(b)
  show (softThreshold lam c - c) ^ 2 / 2 + lam * |softThreshold lam c|
        ≤ (b - c) ^ 2 / 2 + lam * |b|
  unfold softThreshold
  -- Resolve |b| via cases on the sign of b.
  rcases le_or_gt 0 b with hb | hb
  · -- b ≥ 0, so |b| = b
    have habs_b : |b| = b := abs_of_nonneg hb
    rw [habs_b]
    by_cases hc : 0 ≤ c
    · -- c ≥ 0
      rw [if_pos hc]
      rcases le_or_gt lam c with hlc | hlc
      · -- S = c - lam ≥ 0
        have hS : max (c - lam) 0 = c - lam := by
          have : 0 ≤ c - lam := by linarith
          exact max_eq_left this
        rw [hS]
        have habs_S : |c - lam| = c - lam := abs_of_nonneg (by linarith)
        rw [habs_S]
        nlinarith [sq_nonneg (b - (c - lam)), sq_nonneg b]
      · -- S = 0
        have hS : max (c - lam) 0 = 0 :=
          max_eq_right (by linarith)
        rw [hS]
        simp only [zero_sub, abs_zero, mul_zero, add_zero]
        nlinarith [sq_nonneg (b - c + lam), sq_nonneg b, mul_nonneg hlam hb]
    · -- c < 0
      push_neg at hc
      rw [if_neg hc.not_ge]
      rcases le_or_gt (c + lam) 0 with hcl | hcl
      · -- S = c + lam ≤ 0
        have hS : min (c + lam) 0 = c + lam := min_eq_left hcl
        rw [hS]
        have habs_S : |c + lam| = -(c + lam) := abs_of_nonpos hcl
        rw [habs_S]
        -- minimizer value: ½ lam² - lam(c + lam) = -lam c - lam²/2
        nlinarith [sq_nonneg (b - c - lam), sq_nonneg b,
                   mul_nonneg hlam hb]
      · -- S = 0
        have hS : min (c + lam) 0 = 0 := min_eq_right (le_of_lt hcl)
        rw [hS]
        simp only [zero_sub, abs_zero, mul_zero, add_zero]
        nlinarith [sq_nonneg (b - c), sq_nonneg b, mul_nonneg hlam hb]
  · -- b < 0, so |b| = -b
    have habs_b : |b| = -b := abs_of_neg hb
    rw [habs_b]
    by_cases hc : 0 ≤ c
    · -- c ≥ 0
      rw [if_pos hc]
      rcases le_or_gt lam c with hlc | hlc
      · -- S = c - lam ≥ 0
        have hS : max (c - lam) 0 = c - lam := by
          have : 0 ≤ c - lam := by linarith
          exact max_eq_left this
        rw [hS]
        have habs_S : |c - lam| = c - lam := abs_of_nonneg (by linarith)
        rw [habs_S]
        nlinarith [sq_nonneg (b - c - lam), sq_nonneg (b - (c - lam)),
                   mul_nonneg hlam (neg_nonneg.mpr (le_of_lt hb)),
                   mul_nonneg hlam hc, sq_nonneg b]
      · -- S = 0
        have hS : max (c - lam) 0 = 0 :=
          max_eq_right (by linarith)
        rw [hS]
        simp only [zero_sub, abs_zero, mul_zero, add_zero]
        nlinarith [sq_nonneg (b - c - lam), sq_nonneg b,
                   mul_nonneg hlam hc, mul_nonneg hlam (neg_nonneg.mpr (le_of_lt hb))]
    · -- c < 0
      push_neg at hc
      rw [if_neg hc.not_ge]
      rcases le_or_gt (c + lam) 0 with hcl | hcl
      · -- S = c + lam ≤ 0
        have hS : min (c + lam) 0 = c + lam := min_eq_left hcl
        rw [hS]
        have habs_S : |c + lam| = -(c + lam) := abs_of_nonpos hcl
        rw [habs_S]
        nlinarith [sq_nonneg (b - (c + lam)),
                   mul_nonneg hlam (neg_nonneg.mpr (le_of_lt hb))]
      · -- S = 0
        have hS : min (c + lam) 0 = 0 := min_eq_right (le_of_lt hcl)
        rw [hS]
        simp only [zero_sub, abs_zero, mul_zero, add_zero]
        nlinarith [sq_nonneg (b - c), sq_nonneg b,
                   mul_nonneg hlam (neg_nonneg.mpr (le_of_lt hb))]

/-! ### Abstract Lasso KKT optimality

For the regularized objective `F(β) = f(β) + λ · ‖β‖₁`, where `f` is
convex with a subgradient `w` at `β̂`, the point `β̂` is a global
minimizer whenever there exists an `ℓ¹` subgradient `g` of `β̂` such
that the *KKT certificate* `w + λ · g = 0` holds.

This abstract form discharges the Lasso optimality system (Bach 2024,
§8.2) once `f` is instantiated as the squared loss
`f(β) = ½(1/n)‖y − Xβ‖²` and `w` as its gradient
`(1/n) Xᵀ(Xβ̂ − y)`. The subdifferential calculus for `ℓ¹` is supplied
by `LTFP.MathlibExt.Analysis.Subgradient.L1`.
-/

open LTFP.MathlibExt.Analysis in
/-- §8.2 — **Abstract Lasso KKT sufficiency.**

    Let `f : (Fin d → ℝ) → ℝ` admit a subgradient `w` at `β̂`, i.e.
    `f(β) ≥ f(β̂) + ⟨w, β − β̂⟩` for every `β`. Let `g` be an
    `ℓ¹` subgradient of `β̂` (`IsL1Subgradient β̂ g`). If `λ ≥ 0` and
    the **KKT stationarity condition** `wᵢ + λ · gᵢ = 0` holds
    coordinatewise, then `β̂` is a global minimizer of
    `F(β) = f(β) + λ · ‖β‖₁`.

    This is the textbook first-order optimality system for the Lasso
    (Bach 2024 §8.2, eq. 8.10): `0 ∈ ∇f(β̂) + λ · ∂‖β̂‖₁`. Specializing
    `f` to the squared loss recovers the classical statement
    `Xᵀ(Xβ̂ − y)/n ∈ −λ · ∂‖β̂‖₁`. -/
theorem lasso_kkt_abstract
    {f : (Fin d → ℝ) → ℝ} {βhat w g : Fin d → ℝ} {lam : ℝ}
    (hlam : 0 ≤ lam)
    (hf : ∀ β, f β ≥ f βhat + ∑ i, w i * (β i - βhat i))
    (hg : IsL1Subgradient βhat g)
    (hKKT : ∀ i, w i + lam * g i = 0) :
    IsMinOn (fun β => f β + lam * l1Norm β) Set.univ βhat := by
  intro β _
  show f βhat + lam * l1Norm βhat ≤ f β + lam * l1Norm β
  -- Convex lower bound on `f`.
  have hf_lb : f βhat + ∑ i, w i * (β i - βhat i) ≤ f β := hf β
  -- Subgradient inequality coordinatewise.
  have h_sub : ∀ i, |βhat i| + g i * (β i - βhat i) ≤ |β i| := by
    intro i
    have hi : IsAbsSubgradient (βhat i) (g i) := hg i
    exact hi (β i)
  -- Sum to get the ℓ¹ subgradient inequality.
  have h_l1 : l1Norm βhat + ∑ i, g i * (β i - βhat i) ≤ l1Norm β := by
    unfold l1Norm
    have hsum : ∑ i, (|βhat i| + g i * (β i - βhat i)) ≤ ∑ i, |β i| :=
      Finset.sum_le_sum (fun i _ => h_sub i)
    have heq : ∑ i, (|βhat i| + g i * (β i - βhat i))
        = (∑ i, |βhat i|) + ∑ i, g i * (β i - βhat i) := by
      rw [Finset.sum_add_distrib]
    linarith
  -- Multiply by `lam ≥ 0`.
  have h_l1_lam : lam * (l1Norm βhat + ∑ i, g i * (β i - βhat i))
        ≤ lam * l1Norm β :=
    mul_le_mul_of_nonneg_left h_l1 hlam
  -- KKT certificate: the cross term cancels exactly.
  have hKKT_sum : ∑ i, (w i + lam * g i) * (β i - βhat i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [hKKT i, zero_mul]
  have hexpand : ∑ i, (w i + lam * g i) * (β i - βhat i)
      = (∑ i, w i * (β i - βhat i))
        + lam * ∑ i, g i * (β i - βhat i) := by
    have h1 : ∑ i, (w i + lam * g i) * (β i - βhat i)
        = (∑ i, w i * (β i - βhat i))
          + ∑ i, lam * g i * (β i - βhat i) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    have h2 : ∑ i, lam * g i * (β i - βhat i)
        = lam * ∑ i, g i * (β i - βhat i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    rw [h1, h2]
  have hcross : (∑ i, w i * (β i - βhat i))
              + lam * ∑ i, g i * (β i - βhat i) = 0 := by
    rw [← hexpand]; exact hKKT_sum
  -- Combine: f βhat + λ‖βhat‖₁ ≤ f β + λ‖β‖₁.
  -- Expand h_l1_lam: λ‖βhat‖₁ + λ ⟨g, β−βhat⟩ ≤ λ‖β‖₁.
  have h_l1_lam' :
      lam * l1Norm βhat + lam * ∑ i, g i * (β i - βhat i)
        ≤ lam * l1Norm β := by
    have := h_l1_lam
    rw [mul_add] at this
    exact this
  linarith

end LTFP
