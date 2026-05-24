/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.OrderClosed
import LTFP.MathlibExt.MatrixAnalysis.CStarRpowConcave

/-!
# Operator concavity of `CFC.log` on the strictly positive cone

This file proves that the operator logarithm `CFC.log : A → A` is operator
concave on the set of strictly positive elements of a unital C⋆-algebra `A`.

This discharges the second TODO item in
`Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog/Order.lean`
(the first item — that `log` is operator monotone — is `CFC.log_monotoneOn`).

## Main results

* `CFC.log_concaveOn` : the map `a ↦ CFC.log a` is operator concave on
  `{a : A | IsStrictlyPositive a}` in any unital C⋆-algebra `A`.

## Proof strategy

We use the well-known integral / pointwise representation

```
CFC.log a = lim_{p → 0⁺} p⁻¹ • (a ^ p - 1)
```

(`CFC.tendsto_cfc_rpow_sub_one_log` in Mathlib), pass through the
continuity of the continuous functional calculus, and combine three
ingredients:

1. **Convexity of the domain.** The strictly positive cone is convex —
   for `t ∈ (0, 1)`, `t • a + (1 - t) • b` is strictly positive whenever
   `a, b` are, by `IsStrictlyPositive.smul` and
   `IsStrictlyPositive.add_nonneg`.

2. **Concavity of the approximants.** For `p ∈ (0, 1)`, the function
   `a ↦ p⁻¹ • (a ^ p - 1)` is operator concave on the positive cone (and
   hence on the strictly positive cone). This uses
   `CFC.concaveOn_rpow` (Piece B, just landed in
   `CStarRpowConcave.lean`), together with `ConcaveOn.add_const` and
   `ConcaveOn.smul`.

3. **Closedness of concavity under pointwise limits.** The set of
   functions `f : A → A` that are concave on a fixed convex set `s` is
   closed in the product topology. This is the concavity analogue of
   `isClosed_monotoneOn` from Mathlib.

The overall structure mirrors `CFC.log_monotoneOn` at
`Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog/Order.lean`.
-/

@[expose] public section

namespace LTFP.MathlibExt.MatrixAnalysis

open scoped Topology
open Set Filter

/-! ## Piece C.1: closedness of concavity under pointwise limits -/

section ConcaveOnClosed

variable {E : Type*} {β : Type*}
variable [AddCommMonoid E] [Module ℝ E]
variable [TopologicalSpace β] [AddCommMonoid β] [Module ℝ β]
  [PartialOrder β] [OrderClosedTopology β]
  [ContinuousAdd β] [ContinuousConstSMul ℝ β]

/-- The set of functions concave on a fixed convex set `s` is closed
in the product (pointwise convergence) topology. Concavity analogue of
`isClosed_monotoneOn`. -/
theorem isClosed_concaveOn {s : Set E} (hs : Convex ℝ s) :
    IsClosed {f : E → β | ConcaveOn ℝ s f} := by
  simp only [isClosed_iff_clusterPt, clusterPt_principal_iff_frequently]
  intro g hg
  refine ⟨hs, ?_⟩
  intro x hx y hy a b ha hb hab
  -- Pointwise convergence at the three relevant inputs.
  have hmain (z) : Tendsto (fun f' : E → β => f' z) (𝓝 g) (𝓝 (g z)) :=
    continuousAt_apply z _
  -- The left-hand and right-hand sides are continuous functions of `f`.
  have hlhs : Tendsto (fun f' : E → β => a • f' x + b • f' y) (𝓝 g)
      (𝓝 (a • g x + b • g y)) :=
    ((hmain x).const_smul a).add ((hmain y).const_smul b)
  have hrhs : Tendsto (fun f' : E → β => f' (a • x + b • y)) (𝓝 g)
      (𝓝 (g (a • x + b • y))) := hmain _
  -- Each concave function satisfies the inequality; pass to the limit.
  refine le_of_tendsto_of_tendsto_of_frequently hlhs hrhs ?_
  refine hg.mono ?_
  intro f' hf'
  exact hf'.2 hx hy ha hb hab

end ConcaveOnClosed

/-! ## Piece C.2: convexity of the strictly positive cone -/

namespace CFC

section ConvexStrictlyPositive

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The set of strictly positive elements of a unital C⋆-algebra is convex
(in fact, an open convex cone). -/
theorem convex_setOf_isStrictlyPositive :
    Convex ℝ {a : A | IsStrictlyPositive a} := by
  intro a ha b hb t u ht hu htu
  -- Goal: IsStrictlyPositive (t • a + u • b).
  simp only [Set.mem_setOf_eq] at ha hb ⊢
  -- Split on whether t > 0 or t = 0.
  rcases ht.lt_or_eq with ht0 | ht0
  · -- t > 0: `t • a` is strictly positive, and `u • b` is nonneg, so sum is strictly positive.
    have h1 : IsStrictlyPositive (t • a) := IsStrictlyPositive.smul ht0 ha
    have h2 : (0 : A) ≤ u • b := smul_nonneg hu hb.nonneg
    exact h1.add_nonneg h2
  · -- t = 0: then u = 1, so the sum is `0 + 1 • b = b`.
    subst ht0
    have hu1 : u = 1 := by linarith
    subst hu1
    simpa using hb

end ConvexStrictlyPositive

/-! ## Piece D.1: concavity of the approximants for `p ∈ (0, 1)` -/

section LogApproxConcave

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- For `p ∈ (0, 1)`, the function `a ↦ p⁻¹ • (a ^ p - 1)` is operator
concave on the positive cone. This is the approximant for `CFC.log`
provided by `CFC.tendsto_cfc_rpow_sub_one_log`. -/
private lemma concaveOn_log_approx_Ici {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1) :
    ConcaveOn ℝ (Ici (0 : A)) (fun a : A => p⁻¹ • (a ^ p - 1 : A)) := by
  -- Step 1: `a ^ p` is concave on `Ici 0` (Piece B).
  have h_rpow : ConcaveOn ℝ (Ici (0 : A)) (fun a : A => a ^ p) :=
    LTFP.MathlibExt.MatrixAnalysis.CFC.concaveOn_rpow
      ⟨le_of_lt hp.1, le_of_lt hp.2⟩
  -- Step 2: `a ^ p - 1 = a ^ p + (-1)` is concave (subtracting a constant).
  have h_sub : ConcaveOn ℝ (Ici (0 : A)) (fun a : A => a ^ p - 1) := by
    have := h_rpow.add_const (-1 : A)
    refine this.congr ?_
    intro a _
    simp [sub_eq_add_neg]
  -- Step 3: scaling by `p⁻¹ ≥ 0` preserves concavity.
  have hp_inv_nn : (0 : ℝ) ≤ p⁻¹ := le_of_lt (inv_pos.mpr hp.1)
  exact h_sub.smul hp_inv_nn

end LogApproxConcave

/-! ## Piece D.2: passage to limit — operator concavity of `CFC.log` -/

section LogConcave

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Classical in
/-- **Operator concavity of `CFC.log`.**

The continuous functional calculus logarithm is operator concave on the
strictly positive cone of any unital C⋆-algebra `A`.

This discharges the corresponding TODO item in
`Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog/Order.lean`. -/
theorem log_concaveOn :
    ConcaveOn ℝ {a : A | IsStrictlyPositive a} (CFC.log : A → A) := by
  /- Proof outline (mirrors `CFC.log_monotoneOn`):

     We have `CFC.log a = lim_{p → 0⁺} cfc (fun x => p⁻¹ * (x ^ p - 1)) a`
     by `tendsto_cfc_rpow_sub_one_log`. Each approximant
     `a ↦ p⁻¹ • (a ^ p - 1)` is concave on the strictly positive cone
     (via Piece B + `add_const` + `smul`). The set of concave functions
     is closed under pointwise limits (Piece C.1), so the limit
     `CFC.log` is concave. -/
  let s : Set A := {a : A | IsStrictlyPositive a}
  have hs : Convex ℝ s := convex_setOf_isStrictlyPositive
  -- Auxiliary family `f p : A → A` extended to `0` off `s`.
  let f (p : ℝ) : A → A :=
    fun a => if a ∈ s then cfc (A := A) (fun x => p⁻¹ * (x ^ p - 1)) a else 0
  let g : A → A := fun a => if a ∈ s then CFC.log (A := A) a else 0
  -- `g` agrees with `CFC.log` on `s`.
  have hg_eq : s.EqOn g (CFC.log : A → A) := by
    intro a ha
    simp [g, ha]
  -- Reduce to showing `g` is concave on `s`.
  refine ConcaveOn.congr ?_ hg_eq
  -- Apply closedness under limits on the filter `𝓝[>] 0`.
  have h_closed : IsClosed {h : A → A | ConcaveOn ℝ s h} :=
    isClosed_concaveOn (E := A) (β := A) hs
  -- Tendsto: pointwise convergence of `f p → g` as `p → 0⁺`.
  have h_tendsto : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 g) := by
    rw [tendsto_pi_nhds]
    intro a
    by_cases ha : a ∈ s
    · have hmem : IsStrictlyPositive a := ha
      have h_mathlib := CFC.tendsto_cfc_rpow_sub_one_log hmem
      have h_eq : ∀ p, cfc (fun x => p⁻¹ * (x ^ p - 1)) a = f p a := by
        intro p
        simp [f, ha]
      have hg_a : g a = CFC.log a := by simp [g, ha]
      rw [hg_a]
      exact h_mathlib.congr h_eq
    · have h_const : ∀ p, f p a = 0 := by intro p; simp [f, ha]
      have hg_a : g a = 0 := by simp [g, ha]
      rw [hg_a]
      simp only [h_const]
      exact tendsto_const_nhds
  -- Eventually: for `p ∈ (0, 1)`, `f p` is concave on `s`.
  have h_eventually : ∀ᶠ p in 𝓝[>] (0 : ℝ), f p ∈ {h : A → A | ConcaveOn ℝ s h} := by
    have h₁ : ∀ᶠ (p : ℝ) in 𝓝[>] 0, 0 < p ∧ p < 1 :=
      nhdsGT_basis 0 |>.mem_of_mem zero_lt_one
    filter_upwards [h₁] with p ⟨hp_pos, hp_lt⟩
    show ConcaveOn ℝ s (f p)
    -- On `s`, `f p` equals `a ↦ p⁻¹ • (a ^ p - 1)`.
    have hf_eq : s.EqOn (fun a : A => p⁻¹ • (a ^ p - 1)) (f p) := by
      intro a ha
      have hmem : IsStrictlyPositive a := ha
      simp only [f, ha, ↓reduceIte, ← smul_eq_mul]
      rw [cfc_smul _ (hf := by fun_prop (disch := grind -abstractProof)),
          cfc_sub _ _ (hf := by fun_prop (disch := grind -abstractProof)),
          cfc_const_one .., CFC.rpow_eq_cfc_real ..]
    have hp_mem : p ∈ Ioo (0 : ℝ) 1 := ⟨hp_pos, hp_lt⟩
    have h_approx_Ici := concaveOn_log_approx_Ici (A := A) hp_mem
    have hs_sub : s ⊆ Ici (0 : A) := fun a ha => ha.nonneg
    have h_approx_s : ConcaveOn ℝ s (fun a : A => p⁻¹ • (a ^ p - 1 : A)) :=
      h_approx_Ici.subset hs_sub hs
    exact h_approx_s.congr hf_eq
  exact h_closed.mem_of_tendsto h_tendsto h_eventually

end LogConcave

end CFC

end LTFP.MathlibExt.MatrixAnalysis
