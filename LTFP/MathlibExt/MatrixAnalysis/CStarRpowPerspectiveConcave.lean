/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.MatrixAnalysis.CStarEffrosNormalizer

/-!
# Joint operator concavity of the `rpow` operator perspective

This file assembles the joint operator concavity of the `rpow` operator
perspective `CFC.rpowPerspective p` on its natural domain
`{(a, b) : A × A | 0 ≤ a ∧ IsStrictlyPositive b}` for `p ∈ [0, 1]`.
This is the operator-perspective formulation of **Effros's joint
concavity theorem** (B6 L3 Sub-Part 6.5), which is the C⋆-algebraic
generalization of the classical Lieb concavity statement
`(A, B) ↦ Tr(K* A^p K B^(1-p))` to the operator-valued perspective.

## Main result

* `CFC.concaveOn_rpowPerspective`: for any `p ∈ [0, 1]` and any unital
  C⋆-algebra `A`,

  ```
  ConcaveOn ℝ {z : A × A | 0 ≤ z.1 ∧ IsStrictlyPositive z.2}
    (fun z => CFC.rpowPerspective p z.1 z.2)
  ```

## Proof structure

The two ingredients are:

* The **two-state Hansen–Pedersen Jensen inequality** (B6 L3
  Sub-Part 6.2,
  `CFC.sum_star_mul_rpow_mul_le_rpow_sum_star_mul`): for `p ∈ [0, 1]`,
  `0 ≤ x₁, x₂`, and `star v₁ * v₁ + star v₂ * v₂ = 1`,

  ```
  star v₁ * x₁^p * v₁ + star v₂ * x₂^p * v₂ ≤
    (star v₁ * x₁ * v₁ + star v₂ * x₂ * v₂)^p.
  ```

* The three **Effros normalizer identities** (B6 L3 Sub-Part 6.4,
  `CStarEffrosNormalizer.lean`). With

  ```
  b  := t • b₁ + u • b₂
  vᵢ := (Real.sqrt weightᵢ : ℂ) • (bᵢ ^ (1/2) * b ^ (-1/2))
  xᵢ := bᵢ ^ (-1/2) * aᵢ * bᵢ ^ (-1/2)
  ```

  they assert (a) `star v₁ * v₁ + star v₂ * v₂ = 1`,
  (b) `star v₁ * x₁ * v₁ + star v₂ * x₂ * v₂ = b^(-1/2) * (t • a₁ + u • a₂) * b^(-1/2)`,
  and (c) outer conjugation by `b^(1/2)` of the LHS sum of `(a)` with
  `xᵢ^p` in place of `xᵢ` produces `t • g_p(a₁, b₁) + u • g_p(a₂, b₂)`.

The proof of `concaveOn_rpowPerspective` then runs as follows.

**Boundary cases** (`t = 0` or `u = 0`): since `t + u = 1`, one weight
is `1` and the other is `0`; the inequality reduces to
`f z ≤ f z`, immediate.

**Interior case** (`0 < t, 0 < u`): apply the Hansen–Pedersen
inequality to `(xᵢ, vᵢ)`, then conjugate the resulting operator
inequality by the strictly positive element `b^(1/2)` (preserves the
order). The LHS becomes
`t • g_p(a₁, b₁) + u • g_p(a₂, b₂)` by identity (c); the RHS becomes
`g_p(t • a₁ + u • a₂, b)` after substituting identity (b) into the
`rpow` argument and unfolding `CFC.rpowPerspective`.

## References

* Effros, "A matrix convexity approach to some celebrated quantum
  inequalities", *Proc. Natl. Acad. Sci. USA* 106 (2009), 1006–1008.
* Hansen and Pedersen, "Jensen's operator inequality", *Bull. London
  Math. Soc.* 35 (2003), 553–564.
* Lieb, "Convex trace functions and the Wigner–Yanase–Dyson
  conjecture", *Adv. Math.* 11 (1973), 267–288.
* Pusz–Woronowicz, "Functional calculus for sesquilinear forms and the
  purification map", *Rep. Math. Phys.* 8 (1975), 159–170.
-/

@[expose] public section

namespace CFC

section RpowPerspectiveConcave

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Joint operator concavity of the `rpow` operator perspective
(Effros's joint concavity theorem, B6 L3 Sub-Part 6.5).**

For any `p ∈ [0, 1]` and any unital C⋆-algebra `A`, the operator
`rpow` perspective

```
g_p(a, b) := b ^ (1/2) · ((b ^ (-1/2) · a · b ^ (-1/2)) ^ p) · b ^ (1/2)
```

is jointly operator concave on its natural domain
`{(a, b) : A × A | 0 ≤ a ∧ IsStrictlyPositive b}`.

This is the operator-perspective formulation of Lieb concavity. The
proof combines the two-state Hansen–Pedersen Jensen inequality
(`CFC.sum_star_mul_rpow_mul_le_rpow_sum_star_mul`, B6 L3 Sub-Part 6.2)
with three algebraic identities for the Effros normalizers (B6 L3
Sub-Part 6.4). -/
theorem concaveOn_rpowPerspective
    {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    ConcaveOn ℝ {z : A × A | 0 ≤ z.1 ∧ IsStrictlyPositive z.2}
      (fun z => CFC.rpowPerspective p z.1 z.2) := by
  refine ⟨CFC.convex_rpowPerspective_domain, ?_⟩
  rintro ⟨a₁, b₁⟩ hz₁ ⟨a₂, b₂⟩ hz₂ t u ht hu htu
  obtain ⟨ha₁, hb₁⟩ : 0 ≤ a₁ ∧ IsStrictlyPositive b₁ := hz₁
  obtain ⟨ha₂, hb₂⟩ : 0 ≤ a₂ ∧ IsStrictlyPositive b₂ := hz₂
  -- Goal: `t • g_p(a₁, b₁) + u • g_p(a₂, b₂) ≤ g_p(t • a₁ + u • a₂, t • b₁ + u • b₂)`.
  -- Split on whether the weights are strictly positive or one is zero.
  rcases eq_or_lt_of_le ht with ht0 | htpos
  · -- Boundary: `t = 0`, so `u = 1` (from `t + u = 1`).
    subst ht0
    have hu1 : u = 1 := by linarith
    subst hu1
    -- Goal collapses to `g_p(a₂, b₂) ≤ g_p(a₂, b₂)`.
    simp
  rcases eq_or_lt_of_le hu with hu0 | hupos
  · -- Boundary: `u = 0`, so `t = 1`.
    subst hu0
    have ht1 : t = 1 := by linarith
    subst ht1
    simp
  -- Interior case: `0 < t` and `0 < u`.
  -- Set up the Effros data: `b := t • b₁ + u • b₂`, normalizers `v₁, v₂`,
  -- normalized inputs `x₁, x₂`.
  set b : A := t • b₁ + u • b₂ with hb_def
  set x₁ : A := b₁ ^ (-(1 / 2) : ℝ) * a₁ * b₁ ^ (-(1 / 2) : ℝ) with hx₁_def
  set x₂ : A := b₂ ^ (-(1 / 2) : ℝ) * a₂ * b₂ ^ (-(1 / 2) : ℝ) with hx₂_def
  set v₁ : A := (Real.sqrt t : ℂ) • (b₁ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))
    with hv₁_def
  set v₂ : A := (Real.sqrt u : ℂ) • (b₂ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))
    with hv₂_def
  -- Nonnegativity of the normalized inputs `xᵢ = star (bᵢ^(-1/2)) * aᵢ * bᵢ^(-1/2)`.
  have hsa_b₁_neg : IsSelfAdjoint (b₁ ^ (-(1 / 2) : ℝ)) :=
    IsSelfAdjoint.of_nonneg rpow_nonneg
  have hsa_b₂_neg : IsSelfAdjoint (b₂ ^ (-(1 / 2) : ℝ)) :=
    IsSelfAdjoint.of_nonneg rpow_nonneg
  have hx₁_nn : 0 ≤ x₁ := by
    have h_eq : b₁ ^ (-(1 / 2) : ℝ) * a₁ * b₁ ^ (-(1 / 2) : ℝ) =
        star (b₁ ^ (-(1 / 2) : ℝ)) * a₁ * b₁ ^ (-(1 / 2) : ℝ) := by
      rw [hsa_b₁_neg.star_eq]
    rw [hx₁_def, h_eq]
    exact star_left_conjugate_nonneg ha₁ _
  have hx₂_nn : 0 ≤ x₂ := by
    have h_eq : b₂ ^ (-(1 / 2) : ℝ) * a₂ * b₂ ^ (-(1 / 2) : ℝ) =
        star (b₂ ^ (-(1 / 2) : ℝ)) * a₂ * b₂ ^ (-(1 / 2) : ℝ) := by
      rw [hsa_b₂_neg.star_eq]
    rw [hx₂_def, h_eq]
    exact star_left_conjugate_nonneg ha₂ _
  -- Effros normalizer partition of unity (Sub-Part 6.4.a).
  have hpartition : star v₁ * v₁ + star v₂ * v₂ = 1 := by
    rw [hv₁_def, hv₂_def, hb_def]
    exact CFC.effros_normalizers_partition hb₁ hb₂ htpos hupos htu
  -- Hansen–Pedersen Jensen inequality (Sub-Part 6.2) on `(xᵢ, vᵢ)`.
  have hHP :
      star v₁ * (x₁ ^ p) * v₁ + star v₂ * (x₂ ^ p) * v₂ ≤
        (star v₁ * x₁ * v₁ + star v₂ * x₂ * v₂) ^ p :=
    LTFP.MathlibExt.MatrixAnalysis.CFC.sum_star_mul_rpow_mul_le_rpow_sum_star_mul
      hp hx₁_nn hx₂_nn hpartition
  -- Effros normalized-input sum identity (Sub-Part 6.4.b).
  have hsum :
      star v₁ * x₁ * v₁ + star v₂ * x₂ * v₂ =
        b ^ (-(1 / 2) : ℝ) * (t • a₁ + u • a₂) * b ^ (-(1 / 2) : ℝ) := by
    rw [hv₁_def, hv₂_def, hx₁_def, hx₂_def, hb_def]
    exact CFC.effros_normalized_input_sum ha₁ ha₂ hb₁ hb₂ htpos hupos
  rw [hsum] at hHP
  -- Conjugate both sides by the positive `b^(1/2)`.
  have hb_half_nn : (0 : A) ≤ b ^ (1 / 2 : ℝ) := rpow_nonneg
  have hHP_conj :
      b ^ (1 / 2 : ℝ) *
          (star v₁ * (x₁ ^ p) * v₁ + star v₂ * (x₂ ^ p) * v₂) *
          b ^ (1 / 2 : ℝ) ≤
        b ^ (1 / 2 : ℝ) *
          (b ^ (-(1 / 2) : ℝ) * (t • a₁ + u • a₂) * b ^ (-(1 / 2) : ℝ)) ^ p *
          b ^ (1 / 2 : ℝ) :=
    conjugate_le_conjugate_of_nonneg hHP hb_half_nn
  -- Rewrite the LHS via Sub-Part 6.4.c: the conjugated sum is
  -- `t • g_p(a₁, b₁) + u • g_p(a₂, b₂)`.
  have hLHS_eq :
      b ^ (1 / 2 : ℝ) *
          (star v₁ * (x₁ ^ p) * v₁ + star v₂ * (x₂ ^ p) * v₂) *
          b ^ (1 / 2 : ℝ) =
        t • CFC.rpowPerspective p a₁ b₁ + u • CFC.rpowPerspective p a₂ b₂ := by
    rw [hv₁_def, hv₂_def, hx₁_def, hx₂_def, hb_def]
    exact
      CFC.effros_conjugate_sum_rpow_eq_sum_rpowPerspective
        ha₁ ha₂ hb₁ hb₂ htpos hupos
  -- The RHS unfolds to `CFC.rpowPerspective p (t • a₁ + u • a₂) b` by definition.
  have hRHS_eq :
      b ^ (1 / 2 : ℝ) *
          (b ^ (-(1 / 2) : ℝ) * (t • a₁ + u • a₂) * b ^ (-(1 / 2) : ℝ)) ^ p *
          b ^ (1 / 2 : ℝ) =
        CFC.rpowPerspective p (t • a₁ + u • a₂) b := by
    simp [CFC.rpowPerspective]
  rw [hLHS_eq, hRHS_eq] at hHP_conj
  -- Note: the `Prod` smul unpacks as `(t • a₁ + u • a₂, t • b₁ + u • b₂)`.
  -- Goal: `t • g_p(a₁, b₁) + u • g_p(a₂, b₂) ≤ g_p(t • a₁ + u • a₂, t • b₁ + u • b₂)`.
  change _ ≤ CFC.rpowPerspective p (t • a₁ + u • a₂) (t • b₁ + u • b₂)
  exact hHP_conj

end RpowPerspectiveConcave

end CFC
