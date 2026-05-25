/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.Convex.Function
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Partial supremum of a jointly concave function is concave

For `f : Y × X → ℝ` jointly concave on `T ×ˢ S` (`T` convex), the partial
supremum
`g : X → ℝ`, `g x := sSup ((fun P => f (P, x)) '' T)`
is concave on `S` (under a boundedness hypothesis ensuring the supremum is
finite and a nonemptiness hypothesis ensuring it is well-defined).

This is a standard convex-analysis result needed for variational / duality
arguments such as the Legendre–Fenchel transform and the Lindblad–Effros
bridge in operator theory.

## Main result

* `ConcaveOn.partial_sSup_concave` — partial supremum is concave on `S`.

## Proof outline

For `x₁, x₂ ∈ S` and a convex combination `a • x₁ + b • x₂` with
`a + b = 1`, the ε-argument is:

* for any `ε > 0`, pick `P₁, P₂ ∈ T` with
  `g x₁ ≤ f(P₁, x₁) + ε` and `g x₂ ≤ f(P₂, x₂) + ε`;
* by convexity of `T`, `a • P₁ + b • P₂ ∈ T`;
* by joint concavity of `f`,
  `a · f(P₁, x₁) + b · f(P₂, x₂) ≤ f(a • P₁ + b • P₂, a • x₁ + b • x₂)`;
* the RHS is bounded by `g (a • x₁ + b • x₂)`;
* combining with `a + b = 1` gives
  `a · g x₁ + b · g x₂ ≤ g (a • x₁ + b • x₂) + ε`;
* `le_of_forall_pos_le_add` removes `ε`.
-/

namespace ConcaveOn

variable {Y X : Type*} [AddCommGroup Y] [Module ℝ Y] [AddCommGroup X] [Module ℝ X]

/-- The partial supremum of a jointly concave real-valued function over a
convex parameter set is concave in the remaining variable.

Concretely, for `f : Y × X → ℝ` jointly concave on `T ×ˢ S` with `T` convex
and nonempty, the function
`g x := sSup ((fun P => f (P, x)) '' T)`
is concave on `S`, provided that for each `x ∈ S` the section
`{f (P, x) | P ∈ T}` is bounded above.

This is the standard convex-analysis fact that "partial supremum of jointly
concave is concave" — the concave dual of the convex statement
"partial infimum of jointly convex is convex". -/
theorem partial_sSup_concave
    {T : Set Y} {S : Set X} {f : Y × X → ℝ}
    (hf : ConcaveOn ℝ (T ×ˢ S) f)
    (hT : Convex ℝ T) (hS : Convex ℝ S) (hT_ne : T.Nonempty)
    (hbdd : ∀ x ∈ S, BddAbove ((fun P : Y => f (P, x)) '' T)) :
    ConcaveOn ℝ S (fun x => sSup ((fun P : Y => f (P, x)) '' T)) := by
  set g : X → ℝ := fun x => sSup ((fun P : Y => f (P, x)) '' T) with hg_def
  refine ⟨hS, ?_⟩
  intro x₁ hx₁ x₂ hx₂ a b ha hb hab
  -- We use the ε-argument: show
  --   `a • g x₁ + b • g x₂ ≤ g (a • x₁ + b • x₂) + ε`  for every `ε > 0`.
  -- `S` is convex, so the convex combination lies in `S`.
  have hx_comb : a • x₁ + b • x₂ ∈ S := hS hx₁ hx₂ ha hb hab
  -- The image set used to define `g (a • x₁ + b • x₂)` is nonempty and
  -- bounded above.
  have h_im_ne : ((fun P : Y => f (P, a • x₁ + b • x₂)) '' T).Nonempty := by
    obtain ⟨P, hP⟩ := hT_ne
    exact ⟨_, P, hP, rfl⟩
  have h_im_bdd : BddAbove ((fun P : Y => f (P, a • x₁ + b • x₂)) '' T) :=
    hbdd _ hx_comb
  -- Use `le_of_forall_pos_le_add` to reduce to the ε-witness step.
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  -- Pick witnesses `P₁, P₂ ∈ T` realising the suprema up to `ε`.
  -- For `g x₁`: `g x₁ - ε < g x₁`, so some `v ∈ image` satisfies
  -- `g x₁ - ε < v = f (P₁, x₁)`.
  have hε1 : g x₁ - ε < g x₁ := by linarith
  have hε2 : g x₂ - ε < g x₂ := by linarith
  have h_im_ne₁ : ((fun P : Y => f (P, x₁)) '' T).Nonempty := by
    obtain ⟨P, hP⟩ := hT_ne; exact ⟨_, P, hP, rfl⟩
  have h_im_ne₂ : ((fun P : Y => f (P, x₂)) '' T).Nonempty := by
    obtain ⟨P, hP⟩ := hT_ne; exact ⟨_, P, hP, rfl⟩
  obtain ⟨v₁, hv₁_mem, hv₁⟩ := exists_lt_of_lt_csSup h_im_ne₁ hε1
  obtain ⟨v₂, hv₂_mem, hv₂⟩ := exists_lt_of_lt_csSup h_im_ne₂ hε2
  obtain ⟨P₁, hP₁, rfl⟩ := hv₁_mem
  obtain ⟨P₂, hP₂, rfl⟩ := hv₂_mem
  -- The convex combination `a • P₁ + b • P₂` lies in `T`.
  have hPcomb : a • P₁ + b • P₂ ∈ T := hT hP₁ hP₂ ha hb hab
  -- Apply joint concavity of `f` at the product convex combination.
  have hmem₁ : (P₁, x₁) ∈ T ×ˢ S := Set.mk_mem_prod hP₁ hx₁
  have hmem₂ : (P₂, x₂) ∈ T ×ˢ S := Set.mk_mem_prod hP₂ hx₂
  have h_joint :
      a • f (P₁, x₁) + b • f (P₂, x₂) ≤
        f (a • (P₁, x₁) + b • (P₂, x₂)) :=
    hf.2 hmem₁ hmem₂ ha hb hab
  -- Rewrite the joint inequality using the smul/add laws on pairs.
  have h_prod_eq :
      a • (P₁, x₁) + b • (P₂, x₂) =
        (a • P₁ + b • P₂, a • x₁ + b • x₂) := by
    simp [Prod.smul_mk, Prod.mk_add_mk]
  rw [h_prod_eq] at h_joint
  -- The RHS of `h_joint` is bounded by the sup that defines
  -- `g (a • x₁ + b • x₂)`.
  have h_le_g : f (a • P₁ + b • P₂, a • x₁ + b • x₂) ≤
      g (a • x₁ + b • x₂) := by
    apply le_csSup h_im_bdd
    exact ⟨a • P₁ + b • P₂, hPcomb, rfl⟩
  -- Chain together: combine the ε-bounds and joint concavity.
  -- `smul` on `ℝ` is multiplication, so `a • r = a * r`.
  -- Goal: `a • g x₁ + b • g x₂ ≤ g (a • x₁ + b • x₂) + ε`.
  have h_lhs : a • g x₁ + b • g x₂ ≤
      a • (f (P₁, x₁) + ε) + b • (f (P₂, x₂) + ε) := by
    have h1 : g x₁ ≤ f (P₁, x₁) + ε := by linarith
    have h2 : g x₂ ≤ f (P₂, x₂) + ε := by linarith
    have ha' : (0 : ℝ) ≤ a := ha
    have hb' : (0 : ℝ) ≤ b := hb
    -- Convert smul to mul.
    show a * g x₁ + b * g x₂ ≤ a * (f (P₁, x₁) + ε) + b * (f (P₂, x₂) + ε)
    have ka := mul_le_mul_of_nonneg_left h1 ha'
    have kb := mul_le_mul_of_nonneg_left h2 hb'
    linarith
  -- Simplify the RHS of `h_lhs`.
  have h_rhs_eq :
      a • (f (P₁, x₁) + ε) + b • (f (P₂, x₂) + ε) =
        (a • f (P₁, x₁) + b • f (P₂, x₂)) + ε := by
    show a * (f (P₁, x₁) + ε) + b * (f (P₂, x₂) + ε) =
          (a * f (P₁, x₁) + b * f (P₂, x₂)) + ε
    have hab' : a + b = 1 := hab
    have : a * ε + b * ε = ε := by
      have : (a + b) * ε = 1 * ε := by rw [hab']
      linarith [this]
    linarith [this]
  rw [h_rhs_eq] at h_lhs
  -- Now `a • g x₁ + b • g x₂ ≤ (a • f(P₁,x₁) + b • f(P₂,x₂)) + ε`.
  -- Combine with joint concavity and the sup upper bound.
  calc a • g x₁ + b • g x₂
      ≤ (a • f (P₁, x₁) + b • f (P₂, x₂)) + ε := h_lhs
    _ ≤ f (a • P₁ + b • P₂, a • x₁ + b • x₂) + ε := by linarith
    _ ≤ g (a • x₁ + b • x₂) + ε := by linarith

end ConcaveOn
