/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Extr
import Mathlib.Tactic.Linarith
import LTFP.MathlibExt.Analysis.Subgradient.L1

/-!
# Subdifferential sum rule and Lasso KKT discharge

This file develops the *easy half* of the convex-subdifferential sum
rule on `Fin d → ℝ` (Moreau–Rockafellar inclusion `∂f(x) + ∂g(x) ⊆
∂(f + g)(x)`) and the algebraic-Taylor specialization needed to
discharge the Lasso KKT subgradient existence at the squared-loss
optimum.

The setting is the concrete real Hilbert space `Fin d → ℝ` with the
standard dot product `⟨a, b⟩ = ∑ᵢ aᵢ bᵢ`, matching the convention of
`LTFP.Ch08_Sparse.L1` and `LTFP.MathlibExt.Analysis.Subgradient.L1`.

## Main definitions

* `IsSubgradient f g x` — the predicate `f y ≥ f x + ⟨g, y − x⟩` for
  every `y : Fin d → ℝ`. This is the concrete subdifferential
  predicate; on `Fin d → ℝ` it agrees with the inner-product form used
  throughout the convex-analysis literature.
* `IsQuadraticTight f w βhat Q` — structural witness that `f` admits an
  exact second-order Taylor expansion at `βhat` with linear part `w` and
  a nonnegative degree-two-homogeneous remainder `Q`. The squared loss
  fits this template without invoking Matrix machinery.

## Main results

* `IsSubgradient.add` — **easy half** of the sum rule: if `gf ∈ ∂f(x)`
  and `gg ∈ ∂g(x)`, then `gf + gg ∈ ∂(f + g)(x)`. This inclusion holds
  unconditionally.
* `IsSubgradient.smul_nonneg` — closure under nonnegative scalar
  multiplication: `λ ≥ 0 ⇒ λ·g ∈ ∂(λ·f)(x)`.
* `isSubgradient_l1Norm_iff` — bridge: a vector `v` is a subgradient of
  the ℓ¹ norm `l1Norm` at `β` (as `IsSubgradient`) iff it is an
  `IsL1SubgradientFin` of `β`.
* `ge_of_ge_sub_pos_mul` — archimedean cancellation lemma: a strict
  upper bound that depends linearly on a positive parameter can be
  driven to zero, recovering the limit conclusion algebraically.
* `lasso_kkt_discharge_quadTight` — **converse of `lasso_kkt_abstract`**
  for *quadratic-tight* losses: if `f` is quadratic-tight at `βhat` with
  linear part `w` and `βhat` minimizes `f + λ ‖·‖₁` (`λ > 0`), then there
  exists an ℓ¹ subgradient `v` of `βhat` with `w + λ v = 0` coordinatewise.
  This recovers the textbook optimality system `Xᵀ(Xβhat − y) ∈ −λ
  ∂‖βhat‖₁` (Bach 2024, §8.2, eq. 8.10) when `f` is the squared loss.

## Implementation notes

The *hard half* of the Moreau–Rockafellar sum rule (`∂(f + g)(x) ⊆ ∂f(x)
+ ∂g(x)` under continuity or finite-everywhere conditions) requires
relative-interior / conjugate-function infrastructure and is not
attempted here. The quadratic-tight discharge supplies the
application-specific shortcut that the Lasso KKT machinery needs,
avoiding the abstract result and any limit machinery.

The archimedean cancellation lemma `ge_of_ge_sub_pos_mul` plays the
algebraic role of the limit `t → 0⁺` in the directional-derivative
proof, making the discharge a finite-arithmetic argument.

Proposed Mathlib path: `Mathlib/Analysis/Convex/Subgradient/Basic.lean`.
PR #39168 covers the scalar absolute-value subgradient; the generic
`IsSubgradient` predicate and the easy-half sum rule are the natural
next step.

## References

* Jean-Jacques Moreau, *Fonctionnelles convexes*, Séminaire J. Leray,
  1966–67 (sum-rule original).
* R. T. Rockafellar, *Convex Analysis*, Princeton University Press,
  1970, §23.
* Jean-Baptiste Hiriart-Urruty and Claude Lemaréchal, *Convex Analysis
  and Minimization Algorithms I*, Springer, 1993, §VI.4.
* Francis Bach, *Learning Theory from First Principles*, MIT Press,
  2024, §8.2 (Lasso KKT).

## Tags

subgradient, subdifferential, sum rule, Moreau-Rockafellar, lasso, KKT
-/

namespace LTFP.MathlibExt.Analysis

open scoped BigOperators

variable {d : ℕ}

/-- A vector `g : Fin d → ℝ` is a *subgradient* of `f : (Fin d → ℝ) → ℝ`
at `x` if the subgradient inequality
`f y ≥ f x + ⟨g, y − x⟩ = f x + ∑ᵢ gᵢ (yᵢ − xᵢ)`
holds for every `y : Fin d → ℝ`. This is the standard convex
subdifferential predicate on the real Hilbert space `Fin d → ℝ`. -/
def IsSubgradient (f : (Fin d → ℝ) → ℝ) (g x : Fin d → ℝ) : Prop :=
  ∀ y : Fin d → ℝ, f y ≥ f x + ∑ i, g i * (y i - x i)

/-! ### Basic stability properties -/

/-- The zero function admits the zero vector as a subgradient at every
point. -/
theorem isSubgradient_zero (x : Fin d → ℝ) :
    IsSubgradient (fun _ : Fin d → ℝ => (0 : ℝ)) (fun _ => 0) x := by
  intro y
  simp

/-- **Easy half of the Moreau–Rockafellar sum rule.** If `gf` is a
subgradient of `f` at `x` and `gg` is a subgradient of `g` at `x`, then
`gf + gg` is a subgradient of the pointwise sum `f + g` at `x`. This
inclusion `∂f(x) + ∂g(x) ⊆ ∂(f + g)(x)` holds unconditionally. -/
theorem IsSubgradient.add
    {f g : (Fin d → ℝ) → ℝ} {gf gg x : Fin d → ℝ}
    (hf : IsSubgradient f gf x) (hg : IsSubgradient g gg x) :
    IsSubgradient (fun y => f y + g y) (fun i => gf i + gg i) x := by
  intro y
  have h1 : f y ≥ f x + ∑ i, gf i * (y i - x i) := hf y
  have h2 : g y ≥ g x + ∑ i, gg i * (y i - x i) := hg y
  have hsplit :
      ∑ i, (gf i + gg i) * (y i - x i)
        = (∑ i, gf i * (y i - x i)) + ∑ i, gg i * (y i - x i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [hsplit]
  linarith

/-- **Nonnegative scalar multiplication preserves subgradients.** If `g`
is a subgradient of `f` at `x` and `λ ≥ 0`, then `λ · g` is a
subgradient of the scaled function `λ · f` at `x`. -/
theorem IsSubgradient.smul_nonneg
    {f : (Fin d → ℝ) → ℝ} {g x : Fin d → ℝ} {lam : ℝ}
    (hlam : 0 ≤ lam) (hf : IsSubgradient f g x) :
    IsSubgradient (fun y => lam * f y) (fun i => lam * g i) x := by
  intro y
  have h := hf y
  have hsum :
      ∑ i, lam * g i * (y i - x i) = lam * ∑ i, g i * (y i - x i) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [hsum]
  have hmul := mul_le_mul_of_nonneg_left h hlam
  linarith

/-! ### Bridge to the ℓ¹ subdifferential -/

/-- **Bridge:** the ℓ¹ subgradient predicate `IsL1SubgradientFin` is
exactly the concrete `IsSubgradient` predicate applied to the ℓ¹ norm
`y ↦ ∑ᵢ |yᵢ|`. -/
theorem isSubgradient_l1Norm_iff
    {v β : Fin d → ℝ} :
    IsSubgradient (fun y : Fin d → ℝ => ∑ i, |y i|) v β ↔
      IsL1SubgradientFin v β :=
  isL1SubgradientFin_l1Norm.symm

/-! ### Archimedean cancellation -/

/-- **Archimedean cancellation lemma.** If `A ≥ B − t · C` holds for
every `t ∈ (0, 1]` and `C ≥ 0`, then `A ≥ B`. This is the algebraic
substitute for the limit `t → 0⁺` used in the proof of the
subdifferential sum rule for *differentiable* convex functions: a
linear-in-`t` perturbation that survives every positive `t` must be
identically zero. -/
theorem ge_of_ge_sub_pos_mul
    {A B C : ℝ} (hC : 0 ≤ C)
    (h : ∀ t : ℝ, 0 < t → t ≤ 1 → A ≥ B - t * C) :
    A ≥ B := by
  by_contra hlt
  push_neg at hlt
  -- hlt : A < B
  rcases lt_or_eq_of_le hC with hCpos | hC0
  · -- Generic case `C > 0`: pick `t` so that `t · C < B − A`, contradiction.
    set gap : ℝ := B - A with hgap_def
    have hgap_pos : 0 < gap := by
      rw [hgap_def]; linarith
    have h2C_pos : 0 < 2 * C := by linarith
    have hdiv_pos : 0 < gap / (2 * C) := div_pos hgap_pos h2C_pos
    set t : ℝ := min 1 (gap / (2 * C)) with ht_def
    have ht_pos : 0 < t := by
      rw [ht_def]
      exact lt_min zero_lt_one hdiv_pos
    have ht_le : t ≤ 1 := by
      rw [ht_def]; exact min_le_left _ _
    have ht_le_div : t ≤ gap / (2 * C) := by
      rw [ht_def]; exact min_le_right _ _
    have htC_eq : (gap / (2 * C)) * C = gap / 2 := by
      field_simp
    have htC_bound : t * C ≤ gap / 2 := by
      have step : t * C ≤ (gap / (2 * C)) * C :=
        mul_le_mul_of_nonneg_right ht_le_div (le_of_lt hCpos)
      linarith [htC_eq]
    have hineq : A ≥ B - t * C := h t ht_pos ht_le
    have : gap ≤ gap / 2 := by
      have h1 : B - A ≤ t * C := by linarith
      linarith [hgap_def]
    linarith
  · -- Degenerate case `C = 0`: take `t = 1`.
    have hC_eq : C = 0 := hC0.symm
    have hineq : A ≥ B - 1 * C := h 1 zero_lt_one (le_refl 1)
    rw [hC_eq] at hineq
    linarith

/-! ### Quadratic-tight subgradient and Lasso KKT discharge

A convex function `f : (Fin d → ℝ) → ℝ` is *quadratic-tight at `βhat` with
linear part `w` and remainder `Q`* if

* `f β = f βhat + ⟨w, β − βhat⟩ + Q(β − βhat)` for every `β`;
* `Q Δ ≥ 0` for every `Δ`;
* `Q (t · Δ) = t² · Q Δ` for every scalar `t` and every `Δ`.

This abstracts the **squared loss** `f(β) = c · ‖y − Xβ‖²` (with
`c ≥ 0`) without invoking the `Matrix` machinery: the exact Taylor
expansion
`c · ‖y − Xβ‖² = c · ‖y − Xβhat‖² + ⟨2c · Xᵀ(Xβhat − y), β − βhat⟩
              + c · ‖X(β − βhat)‖²`
fits the template with `w = 2c · Xᵀ(Xβhat − y)` and `Q(Δ) = c · ‖XΔ‖²`. -/

/-- Predicate: `f` admits an exact Taylor expansion at `βhat` with linear
part `w` and a nonnegative, degree-two-homogeneous remainder `Q`. -/
structure IsQuadraticTight
    (f : (Fin d → ℝ) → ℝ) (w βhat : Fin d → ℝ)
    (Q : (Fin d → ℝ) → ℝ) : Prop where
  /-- Exact Taylor identity. -/
  exact : ∀ β, f β = f βhat + (∑ i, w i * (β i - βhat i)) + Q (β - βhat)
  /-- The remainder is nonnegative. -/
  nonneg : ∀ Δ : Fin d → ℝ, 0 ≤ Q Δ
  /-- Quadratic homogeneity: `Q(t · Δ) = t² · Q(Δ)`. -/
  homog : ∀ (t : ℝ) (Δ : Fin d → ℝ), Q (fun i => t * Δ i) = t ^ 2 * Q Δ

/-- A quadratic-tight function is convex with linear part `w` as a
subgradient at `βhat`. -/
theorem IsQuadraticTight.isSubgradient
    {f : (Fin d → ℝ) → ℝ} {w βhat : Fin d → ℝ} {Q : (Fin d → ℝ) → ℝ}
    (hQT : IsQuadraticTight f w βhat Q) :
    IsSubgradient f w βhat := by
  intro β
  have heq := hQT.exact β
  have hQnn := hQT.nonneg (β - βhat)
  linarith

/-- **Helper: convexity of the ℓ¹ norm along a convex combination.** For
`t ∈ [0, 1]` and any two points `βhat, y : Fin d → ℝ`, the ℓ¹ norm of the
convex combination `βhat + t (y − βhat)` is bounded by the convex combination
of ℓ¹ norms:
`∑ᵢ |βhatᵢ + t(yᵢ − βhatᵢ)| ≤ (1 − t) ∑ᵢ |βhatᵢ| + t ∑ᵢ |yᵢ|`. -/
private theorem l1Norm_convex_path
    (βhat y : Fin d → ℝ) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∑ i, |βhat i + t * (y i - βhat i)|
      ≤ (1 - t) * (∑ i, |βhat i|) + t * ∑ i, |y i| := by
  have hsum_split :
      (1 - t) * (∑ i, |βhat i|) + t * ∑ i, |y i|
        = ∑ i, ((1 - t) * |βhat i| + t * |y i|) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [hsum_split]
  refine Finset.sum_le_sum (fun i _ => ?_)
  -- Goal: |βhat i + t (y i − βhat i)| ≤ (1 − t)|βhat i| + t |y i|
  -- Rewrite βhat i + t (y i − βhat i) = (1 − t) βhat i + t y i.
  have hrw : βhat i + t * (y i - βhat i) = (1 - t) * βhat i + t * y i := by ring
  rw [hrw]
  have h1t : 0 ≤ 1 - t := by linarith
  calc |(1 - t) * βhat i + t * y i|
      ≤ |(1 - t) * βhat i| + |t * y i| := abs_add_le _ _
    _ = (1 - t) * |βhat i| + t * |y i| := by
        rw [abs_mul, abs_mul, abs_of_nonneg h1t, abs_of_nonneg ht0]

/-- **Lasso KKT discharge for quadratic-tight losses.** If
`f : (Fin d → ℝ) → ℝ` is quadratic-tight at `βhat` with linear part `w`
and remainder `Q`, and if `βhat` is a global minimizer of
`β ↦ f β + λ · (∑ᵢ |βᵢ|)` for some `λ > 0`, then there exists an ℓ¹
subgradient `v` of `βhat` such that the KKT certificate
`w i + λ · v i = 0` holds coordinatewise.

This is the **converse of `lasso_kkt_abstract`** for quadratic losses,
yielding the textbook optimality system
`Xᵀ(Xβhat − y) ∈ −λ · ∂‖βhat‖₁` (Bach 2024 §8.2, eq. 8.10) when `f` is the
squared loss.

The candidate subgradient is `v := −w / λ`. The proof leverages the
exact Taylor identity to convert the minimum inequality into a
scaled-perturbation bound, then closes via `ge_of_ge_sub_pos_mul` — the
algebraic substitute for the directional-derivative limit. -/
theorem lasso_kkt_discharge_quadTight
    {f : (Fin d → ℝ) → ℝ} {w βhat : Fin d → ℝ} {Q : (Fin d → ℝ) → ℝ}
    {lam : ℝ}
    (hlam : 0 < lam)
    (hQT : IsQuadraticTight f w βhat Q)
    (hopt : IsMinOn (fun β => f β + lam * (∑ i, |β i|)) Set.univ βhat) :
    ∃ v : Fin d → ℝ, IsL1SubgradientFin v βhat ∧
      ∀ i, w i + lam * v i = 0 := by
  -- Candidate ℓ¹ subgradient: v := -w / lam.
  refine ⟨fun i => - w i / lam, ?_, ?_⟩
  · -- IsL1SubgradientFin (- w / lam) βhat
    rw [isL1SubgradientFin_l1Norm]
    intro y
    -- Shorthand sums.
    set S₁ : ℝ := ∑ i, |y i| with hS₁_def
    set S₂ : ℝ := ∑ i, |βhat i| with hS₂_def
    set L  : ℝ := ∑ i, w i * (y i - βhat i) with hL_def
    set C  : ℝ := Q (y - βhat) with hC_def
    have hCnn : 0 ≤ C := hQT.nonneg _
    -- Goal: S₁ ≥ S₂ + ∑ i, (- w i / lam) * (y i - βhat i)
    -- Reduce to the lam-scaled form: lam * S₁ ≥ lam * S₂ - L.
    have hlam_ne : lam ≠ 0 := ne_of_gt hlam
    -- The goal is `S₁ ≥ S₂ + ∑ i, (-w i / lam) * (y i - βhat i)`. We prove the
    -- equivalent lam-scaled form `lam * S₁ ≥ lam * S₂ - L` and reduce back.
    have hRHS_sum_eq :
        ∑ i, (- w i / lam) * (y i - βhat i) = - (L / lam) := by
      have hterm : ∀ i, (- w i / lam) * (y i - βhat i)
          = -((w i * (y i - βhat i)) / lam) := by
        intro i
        have : (- w i / lam) * (y i - βhat i) = (-(w i * (y i - βhat i))) / lam := by
          field_simp
        rw [this, neg_div]
      calc ∑ i, (- w i / lam) * (y i - βhat i)
          = ∑ i, -((w i * (y i - βhat i)) / lam) :=
            Finset.sum_congr rfl (fun i _ => hterm i)
        _ = -(∑ i, (w i * (y i - βhat i)) / lam) := by
            rw [← Finset.sum_neg_distrib]
        _ = -((∑ i, w i * (y i - βhat i)) / lam) := by
            rw [Finset.sum_div]
        _ = -(L / lam) := by rw [← hL_def]
    rw [hRHS_sum_eq]
    -- Goal: S₁ ≥ S₂ + - (L / lam), equivalently lam * S₁ ≥ lam * S₂ - L.
    suffices hscaled : lam * S₁ ≥ lam * S₂ - L by
      have hkey : S₁ - S₂ ≥ - (L / lam) := by
        have h1 : lam * (S₁ - S₂) ≥ - L := by ring_nf; linarith
        have h2 : (lam * (S₁ - S₂)) / lam ≥ (- L) / lam :=
          div_le_div_of_nonneg_right h1 (le_of_lt hlam)
        have hsimp : (lam * (S₁ - S₂)) / lam = S₁ - S₂ := by field_simp
        rw [hsimp] at h2
        have : (-L) / lam = - (L / lam) := by ring
        linarith [this.le, this.ge]
      linarith
    -- Prove `hscaled` via scaled perturbation `β_t := βhat + t (y - βhat)`.
    apply ge_of_ge_sub_pos_mul hCnn
    intro t ht_pos ht_le
    -- β_t i = βhat i + t * (y i - βhat i)
    set β_t : Fin d → ℝ := fun i => βhat i + t * (y i - βhat i) with hβ_t_def
    -- Optimality at β_t.
    have hopt_t :
        f βhat + lam * (∑ i, |βhat i|)
          ≤ f β_t + lam * (∑ i, |β_t i|) := hopt (Set.mem_univ β_t)
    -- Exact Taylor of f at β_t.
    have hf_t :
        f β_t = f βhat + (∑ i, w i * (β_t i - βhat i)) + Q (β_t - βhat) := hQT.exact β_t
    -- The linear part of Taylor in direction β_t - βhat = t · (y - βhat).
    have hβ_t_diff : ∀ i, β_t i - βhat i = t * (y i - βhat i) := by
      intro i; simp [hβ_t_def]
    have hlin_t : ∑ i, w i * (β_t i - βhat i) = t * L := by
      rw [hL_def, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hβ_t_diff]; ring
    -- The quadratic part: β_t - βhat = t • (y - βhat), so Q(β_t - βhat) = t² · C.
    have hβ_t_sub_eq : (β_t - βhat) = (fun i => t * ((y - βhat) i)) := by
      funext i
      show β_t i - βhat i = t * ((y - βhat) i)
      rw [hβ_t_diff i, Pi.sub_apply]
    have hquad_t : Q (β_t - βhat) = t ^ 2 * C := by
      rw [hβ_t_sub_eq, hC_def, hQT.homog]
    -- Convex bound for the ℓ¹ part.
    have hl1_t :
        ∑ i, |β_t i| ≤ (1 - t) * S₂ + t * S₁ := by
      rw [hS₁_def, hS₂_def]
      exact l1Norm_convex_path βhat y (le_of_lt ht_pos) ht_le
    -- Multiply by lam ≥ 0.
    have hlam_l1 :
        lam * (∑ i, |β_t i|) ≤ lam * ((1 - t) * S₂ + t * S₁) :=
      mul_le_mul_of_nonneg_left hl1_t (le_of_lt hlam)
    -- Assemble: f β_t + lam * ∑ |β_t i| upper bound.
    have hUB :
        f β_t + lam * (∑ i, |β_t i|)
          ≤ f βhat + t * L + t ^ 2 * C
            + lam * ((1 - t) * S₂ + t * S₁) := by
      have hf_t' : f β_t = f βhat + t * L + t ^ 2 * C := by
        rw [hf_t, hlin_t, hquad_t]
      linarith
    -- Combine with optimality.
    have hkey :
        f βhat + lam * S₂
          ≤ f βhat + t * L + t ^ 2 * C
            + lam * ((1 - t) * S₂ + t * S₁) := by
      have hS₂_rw : (∑ i, |βhat i|) = S₂ := rfl
      linarith
    -- Cancel f βhat; expand lam * ((1-t) S₂ + t S₁).
    have hexp :
        lam * ((1 - t) * S₂ + t * S₁) = lam * S₂ - t * lam * S₂ + t * lam * S₁ := by
      ring
    have hkey' :
        lam * S₂ ≤ t * L + t ^ 2 * C + lam * S₂ - t * lam * S₂ + t * lam * S₁ := by
      linarith [hkey, hexp.le, hexp.ge]
    -- Subtract lam * S₂; divide by t > 0.
    have hkey2 :
        0 ≤ t * L + t ^ 2 * C - t * lam * S₂ + t * lam * S₁ := by
      linarith
    -- 0 ≤ t * (L + t * C - lam * S₂ + lam * S₁), and t > 0, so the bracket ≥ 0.
    have hkey3 :
        0 ≤ L + t * C - lam * S₂ + lam * S₁ := by
      have hfact :
          t * L + t ^ 2 * C - t * lam * S₂ + t * lam * S₁
            = t * (L + t * C - lam * S₂ + lam * S₁) := by ring
      have : 0 ≤ t * (L + t * C - lam * S₂ + lam * S₁) := by
        linarith [hkey2, hfact.le, hfact.ge]
      have ht_pos' : (0 : ℝ) < t := ht_pos
      nlinarith
    -- Rearrange: lam * S₁ ≥ lam * S₂ - L - t * C.
    linarith
  · -- KKT: w i + lam * (- w i / lam) = 0
    intro i
    have hlam_ne : lam ≠ 0 := ne_of_gt hlam
    field_simp
    ring

end LTFP.MathlibExt.Analysis
