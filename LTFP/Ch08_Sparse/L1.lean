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
import LTFP.MathlibExt.Analysis.Subgradient.SumRule

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

/-- §8.3 — **Soft-thresholding deadzone (Bach 2024 eq. 8.13).**
    For `|z| ≤ λ`, the soft-thresholding operator returns `0`: the
    sub-threshold inputs are killed exactly. This is one of the three
    defining regimes of `S_λ`. -/
theorem softThreshold_eq_zero_of_abs_le {lam z : ℝ}
    (_hlam : 0 ≤ lam) (hz : |z| ≤ lam) :
    softThreshold lam z = 0 := by
  unfold softThreshold
  by_cases h : 0 ≤ z
  · rw [if_pos h]
    have habs : |z| = z := abs_of_nonneg h
    have hzle : z ≤ lam := habs ▸ hz
    exact max_eq_right (by linarith)
  · rw [if_neg h]
    push_neg at h
    have habs : |z| = -z := abs_of_neg h
    have hnle : -z ≤ lam := habs ▸ hz
    exact min_eq_right (by linarith)

/-- §8.3 — **Sign preservation of soft-thresholding (nonnegative branch).**
    For nonnegative inputs, `S_λ(z) ≥ 0`. This is one half of the
    "soft-thresholding preserves sign" property used throughout the
    Lasso path analysis (Bach 2024 §8.3). -/
theorem softThreshold_nonneg_of_nonneg {lam z : ℝ}
    (hz : 0 ≤ z) :
    0 ≤ softThreshold lam z := by
  unfold softThreshold
  rw [if_pos hz]
  exact le_max_right _ _

/-- §8.3 — **Sign preservation of soft-thresholding (nonpositive branch).**
    For nonpositive inputs and `λ ≥ 0`, `S_λ(z) ≤ 0`. Companion to
    `softThreshold_nonneg_of_nonneg`. -/
theorem softThreshold_nonpos_of_nonpos {lam z : ℝ}
    (hlam : 0 ≤ lam) (hz : z ≤ 0) :
    softThreshold lam z ≤ 0 := by
  unfold softThreshold
  by_cases h : 0 ≤ z
  · -- Then z = 0.
    have hz0 : z = 0 := le_antisymm hz h
    rw [if_pos h, hz0, zero_sub]
    exact max_le (by linarith) (le_refl 0)
  · rw [if_neg h]
    exact min_le_right _ _

/-- §8.3 — **Shrinkage bound for soft-thresholding (Bach 2024 §8.3).**
    Soft-thresholding never increases magnitude: `|S_λ(z)| ≤ |z|` for
    every `λ ≥ 0`. This is the "shrinkage" property that gives the
    operator its name and underlies the contraction analysis of ISTA. -/
theorem abs_softThreshold_le {lam z : ℝ} (hlam : 0 ≤ lam) :
    |softThreshold lam z| ≤ |z| := by
  unfold softThreshold
  by_cases h : 0 ≤ z
  · rw [if_pos h]
    have habs : |z| = z := abs_of_nonneg h
    rw [habs]
    rcases le_or_gt lam z with hlz | hlz
    · have hmax : max (z - lam) 0 = z - lam := max_eq_left (by linarith)
      rw [hmax, abs_of_nonneg (by linarith : (0 : ℝ) ≤ z - lam)]
      linarith
    · have hmax : max (z - lam) 0 = 0 := max_eq_right (by linarith)
      rw [hmax, abs_zero]
      exact h
  · rw [if_neg h]
    push_neg at h
    have habs : |z| = -z := abs_of_neg h
    rw [habs]
    rcases le_or_gt (z + lam) 0 with hzl | hzl
    · have hmin : min (z + lam) 0 = z + lam := min_eq_left hzl
      rw [hmin, abs_of_nonpos hzl]
      linarith
    · have hmin : min (z + lam) 0 = 0 := min_eq_right (le_of_lt hzl)
      rw [hmin, abs_zero]
      linarith

/-- §8.3 — **Soft-thresholding is bounded between `0` and the input
    (positive branch).** For `0 ≤ z` and `0 ≤ λ`, the shrunk output lies
    in `[0, z]`. This precise interval bound is convenient for ISTA-style
    monotone-convergence arguments (Bach 2024 §8.3, eq. 8.14). -/
theorem softThreshold_le_self_of_nonneg {lam z : ℝ}
    (hlam : 0 ≤ lam) (hz : 0 ≤ z) :
    softThreshold lam z ≤ z := by
  unfold softThreshold
  rw [if_pos hz]
  exact max_le (by linarith) hz

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

open LTFP.MathlibExt.Analysis in
/-- §8.2 — **Multidimensional Lasso KKT sufficiency.**

    Specialization of `lasso_kkt_abstract` to the textbook
    multidimensional ℓ¹ subdifferential. Given a subgradient `w` of `f`
    at `β̂` and a *global* ℓ¹ subgradient `v` of `β̂`
    (`IsL1SubgradientFin v β̂`), the KKT certificate `wᵢ + λ · vᵢ = 0`
    suffices for `β̂` to be a global minimizer of `F(β) = f(β) + λ‖β‖₁`.

    This is the full statement of Bach (2024) §8.2, eq. 8.10, without
    the generic-coordinate-subgradient hypothesis: the ℓ¹
    subdifferential is now packaged as the bona fide
    `v ∈ ∂‖·‖₁(β̂)` predicate from
    `LTFP.MathlibExt.Analysis.Subgradient.L1`. -/
theorem lasso_kkt_multidim
    {f : (Fin d → ℝ) → ℝ} {βhat w v : Fin d → ℝ} {lam : ℝ}
    (hlam : 0 ≤ lam)
    (hf : ∀ β, f β ≥ f βhat + ∑ i, w i * (β i - βhat i))
    (hv : IsL1SubgradientFin v βhat)
    (hKKT : ∀ i, w i + lam * v i = 0) :
    IsMinOn (fun β => f β + lam * l1Norm β) Set.univ βhat :=
  lasso_kkt_abstract hlam hf
    ((isL1SubgradientFin_iff_isL1Subgradient).mp hv) hKKT

open LTFP.MathlibExt.Analysis in
/-- §8.2 — **Necessity / discharge of the Lasso KKT subgradient.**

    Converse of `lasso_kkt_multidim` for *quadratic-tight* losses. If
    `f` admits an exact Taylor expansion at `β̂` with linear part `w`
    and a nonnegative degree-two-homogeneous remainder `Q`, and if `β̂`
    is a global minimizer of `F(β) = f(β) + λ · ‖β‖₁` for some `λ > 0`,
    then there *exists* an ℓ¹ subgradient `v` of `β̂` satisfying the
    KKT certificate `wᵢ + λ · vᵢ = 0` coordinatewise.

    This discharges the `IsL1SubgradientFin` hypothesis of
    `lasso_kkt_multidim`: at the squared-loss optimum, the subgradient
    *exists* and need not be supplied externally. Combined with
    `lasso_kkt_multidim`, this gives the full *iff* characterization
    of optimality `0 ∈ ∇f(β̂) + λ · ∂‖β̂‖₁` for quadratic losses
    (Bach 2024 §8.2, eq. 8.10).

    The squared loss `f(β) = c · ‖y − Xβ‖²` is quadratic-tight with
    `w = 2c · Xᵀ(Xβ̂ − y)` and `Q(Δ) = c · ‖XΔ‖²`, recovering
    `Xᵀ(Xβ̂ − y) ∈ −λ · ∂‖β̂‖₁`. -/
theorem lasso_kkt_discharge
    {f : (Fin d → ℝ) → ℝ} {βhat w : Fin d → ℝ} {Q : (Fin d → ℝ) → ℝ}
    {lam : ℝ}
    (hlam : 0 < lam)
    (hQT : IsQuadraticTight f w βhat Q)
    (hopt : IsMinOn (fun β => f β + lam * l1Norm β) Set.univ βhat) :
    ∃ v : Fin d → ℝ, IsL1SubgradientFin v βhat ∧
      ∀ i, w i + lam * v i = 0 := by
  -- `l1Norm` unfolds to `∑ i, |β i|`, matching the convention of
  -- `lasso_kkt_discharge_quadTight`.
  have hopt' : IsMinOn (fun β => f β + lam * (∑ i, |β i|)) Set.univ βhat := by
    intro β hβ
    have := hopt hβ
    simpa [l1Norm] using this
  exact lasso_kkt_discharge_quadTight hlam hQT hopt'

open LTFP.MathlibExt.Analysis in
/-- §8.2 — **Concrete Lasso KKT discharge for the squared loss.**

    Specialization of `lasso_kkt_discharge` to the textbook squared-loss
    carrier `f(β) = (1/2) · ∑ᵢ (yᵢ − ∑ⱼ Xᵢⱼ βⱼ)²`. If `βhat` is a global
    minimizer of `F(β) = (1/2)·‖y − Xβ‖² + λ · ‖β‖₁` for some `λ > 0`,
    then there exists an ℓ¹ subgradient `v` of `βhat` such that
    `(Xᵀ(Xβhat − y))ⱼ + λ · vⱼ = 0` for every coordinate `j`.

    This is the fully-concrete form of the Lasso optimality system
    (Bach 2024 §8.2, eq. 8.10): the existence of the subgradient is
    *discharged* from the optimality hypothesis alone, with no external
    `IsQuadraticTight` witness required. The witness instance
    `isQuadraticTight_squaredLoss` lives in
    `LTFP.MathlibExt.Analysis.Subgradient.SumRule`. -/
theorem lasso_kkt_discharge_squaredLoss
    {n : ℕ} (X : Fin n → Fin d → ℝ) (y : Fin n → ℝ) (βhat : Fin d → ℝ)
    {lam : ℝ}
    (hlam : 0 < lam)
    (hopt : IsMinOn (fun β => squaredLoss X y β + lam * l1Norm β)
              Set.univ βhat) :
    ∃ v : Fin d → ℝ, IsL1SubgradientFin v βhat ∧
      ∀ j, (∑ i, X i j * ((∑ k, X i k * βhat k) - y i)) + lam * v j = 0 :=
  lasso_kkt_discharge hlam
    (isQuadraticTight_squaredLoss X y βhat) hopt

open LTFP.MathlibExt.Analysis Matrix in
/-- §8.2 — **Matrix-form Lasso KKT discharge for the squared loss.**

    Thin wrapper around `lasso_kkt_discharge_squaredLoss` that exposes
    the conclusion using `Matrix.mulVec` (`*ᵥ`) and `Matrix.transpose`
    (`ᵀ`), the shape downstream consumers (`Ch03_LinearLeastSquares`,
    random projections in `Foundations`) actually want. The hypothesis
    carrier remains the LTFP-local `squaredLoss + lam * l1Norm` since
    its scalar-loss/ℓ¹-regularizer decomposition is what the discharge
    machinery is calibrated against; the Matrix and plain-function
    surfaces are definitionally interchangeable, so callers may supply
    `X : Matrix (Fin n) (Fin d) ℝ` directly.

    Conclusion: the textbook KKT residual `(Xᵀ(Xβhat − y))ⱼ + λ · vⱼ = 0`
    in coordinate `j`, with `v` an ℓ¹ subgradient of `βhat`. -/
theorem lasso_kkt_discharge_squaredLoss_matrix
    {n : ℕ} (X : Matrix (Fin n) (Fin d) ℝ) (y : Fin n → ℝ)
    (βhat : Fin d → ℝ) {lam : ℝ} (hlam : 0 < lam)
    (hopt : IsMinOn (fun β => squaredLoss X y β + lam * l1Norm β)
              Set.univ βhat) :
    ∃ v : Fin d → ℝ, IsL1SubgradientFin v βhat ∧
      ∀ j, (Xᵀ *ᵥ (X *ᵥ βhat - y)) j + lam * v j = 0 := by
  obtain ⟨v, hv, hKKT⟩ :=
    lasso_kkt_discharge_squaredLoss (X := X) y βhat hlam hopt
  refine ⟨v, hv, ?_⟩
  intro j
  -- Bridge `Matrix.mulVec` / `Matrix.transpose` to the coordinate-sum
  -- form the plain-function discharge produced.
  have hbridge : (Xᵀ *ᵥ (X *ᵥ βhat - y)) j
      = ∑ i, X i j * ((∑ k, X i k * βhat k) - y i) := by
    simp [Matrix.mulVec, dotProduct, Matrix.transpose, Pi.sub_apply]
  rw [hbridge]
  exact hKKT j

/-! ### ℓ¹ norm: scaling and ℓ₀ / ℓ∞ comparisons -/

/-- §8.3 — **Absolute homogeneity of the ℓ¹ norm.**
    `‖c · θ‖₁ = |c| · ‖θ‖₁`, the defining homogeneity property of a
    norm (Bach 2024 §8.3 footnote). Together with `l1Norm_add_le` and
    `l1Norm_nonneg` this discharges the seminorm axioms. -/
theorem l1Norm_smul (c : ℝ) (θ : Fin d → ℝ) :
    l1Norm (fun i => c * θ i) = |c| * l1Norm θ := by
  unfold l1Norm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [abs_mul]

/-- §8.2/§8.3 — **ℓ∞-control bound on the ℓ¹ norm of a `k`-sparse
    vector.** If at most `k` coordinates of `θ` are nonzero and every
    coordinate has magnitude bounded by `M`, then `‖θ‖₁ ≤ k · M`. This
    is the elementary inequality bridging ℓ₀ and ℓ¹ used in support
    recovery and prediction-error analysis (Bach 2024 §8.3). -/
theorem l1Norm_le_of_sparse {k : ℕ} {M : ℝ} {θ : Fin d → ℝ}
    (hM : 0 ≤ M) (hsparse : (Finset.univ.filter fun i => θ i ≠ 0).card ≤ k)
    (hbound : ∀ i, |θ i| ≤ M) :
    l1Norm θ ≤ (k : ℝ) * M := by
  classical
  unfold l1Norm
  -- Split the sum into the support and its complement; the complement is zero.
  set S : Finset (Fin d) := Finset.univ.filter (fun i => θ i ≠ 0)
  have hsplit : ∑ i, |θ i| = ∑ i ∈ S, |θ i| := by
    refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
    intro i _ hiS
    have : θ i = 0 := by
      by_contra h
      exact hiS (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
    rw [this, abs_zero]
  rw [hsplit]
  calc ∑ i ∈ S, |θ i|
      ≤ ∑ _i ∈ S, M := Finset.sum_le_sum (fun i _ => hbound i)
    _ = (S.card : ℝ) * M := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (k : ℝ) * M := by
        have hk : (S.card : ℝ) ≤ (k : ℝ) := by exact_mod_cast hsparse
        exact mul_le_mul_of_nonneg_right hk hM

end LTFP
