/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.Convex.Basic
import LTFP.MathlibExt.MatrixAnalysis.CStarLogConcave
import LTFP.MathlibExt.MatrixAnalysis.CStarRpowConcave

/-!
# Operator `rpow` perspective and its natural domain

This file introduces the **operator `rpow` perspective**

```
g_p(a, b) := b ^ (1/2) * ((b ^ (-1/2) * a * b ^ (-1/2)) ^ p) * b ^ (1/2)
```

defined on pairs `(a, b)` of elements of a unital C⋆-algebra `A` with
`0 ≤ a` and `b` strictly positive. This is the C⋆-algebraic generalization
of Pusz–Woronowicz's operator perspective of the scalar function
`x ↦ x ^ p`, and it is the function whose joint operator convexity /
concavity is the content of **Effros's joint concavity theorem** (the
operator-perspective formulation of Lieb concavity).

For `p ∈ [0, 1]`, the perspective `g_p` is jointly operator concave in
`(a, b)` on its natural domain `D := {(a, b) | 0 ≤ a ∧ IsStrictlyPositive b}`;
for `p ∈ [-1, 0] ∪ [1, 2]`, it is jointly operator convex. The proof of
the joint concavity / convexity will be carried out in B6 L3 Sub-Part 6.5
using the two-state Hansen–Pedersen Jensen inequality
(`LTFP.MathlibExt.MatrixAnalysis.CFC.sum_star_mul_rpow_mul_le_rpow_sum_star_mul`,
Sub-Part 6.2) and the operator-monotonicity of `b ↦ b ^ (1/2)` /
`b ↦ b ^ (-1/2)`. The present file lays the groundwork:

* It pins down the *definition* of `CFC.rpowPerspective` so downstream
  files can refer to a single normalized formula.
* It proves the *convexity of the natural domain* `D`, which is the
  hypothesis a `ConvexOn` / `ConcaveOn` statement about `g_p` will need.

## Main declarations

* `CFC.rpowPerspective p a b` — the operator `rpow` perspective at
  exponent `p : ℝ` of the pair `(a, b) : A × A`.
* `CFC.convex_rpowPerspective_domain` — the natural domain
  `{(a, b) : A × A | 0 ≤ a ∧ IsStrictlyPositive b}` of
  `CFC.rpowPerspective` is convex.

## Proof strategy for `convex_rpowPerspective_domain`

The domain factors as the product of two convex sets:

* `{a : A | 0 ≤ a} = Set.Ici (0 : A)`, convex by `convex_Ici`.
* `{b : A | IsStrictlyPositive b}`, convex by
  `LTFP.MathlibExt.MatrixAnalysis.CFC.convex_setOf_isStrictlyPositive`
  (already established in `CStarLogConcave.lean`, Piece C.2).

`Convex.prod` then assembles the product, and the set
`{z : A × A | 0 ≤ z.1 ∧ IsStrictlyPositive z.2}` is definitionally equal
to `(Set.Ici 0) ×ˢ {b | IsStrictlyPositive b}`.

## References

* Effros, "A matrix convexity approach to some celebrated quantum
  inequalities", *Proc. Natl. Acad. Sci. USA* 106 (2009), 1006–1008.
* Pusz–Woronowicz, "Functional calculus for sesquilinear forms and the
  purification map", *Rep. Math. Phys.* 8 (1975), 159–170.
-/

@[expose] public section

namespace CFC

section RpowPerspective

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The **operator `rpow` perspective** at exponent `p : ℝ` of a pair
`(a, b)` of elements of a unital C⋆-algebra `A`. Concretely,

```
g_p(a, b) := b ^ (1/2) · ((b ^ (-1/2) · a · b ^ (-1/2)) ^ p) · b ^ (1/2).
```

For `0 ≤ a` and `b` strictly positive (the natural domain), this is the
C⋆-algebraic generalization of Pusz–Woronowicz's operator perspective of
the scalar function `x ↦ x ^ p`. Its joint operator concavity (for
`p ∈ [0, 1]`) is the content of Effros's joint concavity theorem, which
will be discharged in B6 L3 Sub-Part 6.5 from the two-state
Hansen–Pedersen Jensen inequality. -/
noncomputable def rpowPerspective (p : ℝ) (a b : A) : A :=
  b ^ (1 / 2 : ℝ) *
    ((b ^ (-(1 / 2) : ℝ) * a * b ^ (-(1 / 2) : ℝ)) ^ p) *
  b ^ (1 / 2 : ℝ)

/-- The natural domain `{(a, b) : A × A | 0 ≤ a ∧ IsStrictlyPositive b}`
of `CFC.rpowPerspective` is convex.

The proof factors the domain as the product of the closed positive cone
`Set.Ici (0 : A)` (convex by `convex_Ici`) with the open cone of strictly
positive elements (convex by
`LTFP.MathlibExt.MatrixAnalysis.CFC.convex_setOf_isStrictlyPositive`),
and applies `Convex.prod`. -/
lemma convex_rpowPerspective_domain :
    Convex ℝ {z : A × A | 0 ≤ z.1 ∧ IsStrictlyPositive z.2} := by
  -- The domain coincides with the Cartesian product
  -- `Set.Ici (0 : A) ×ˢ {b | IsStrictlyPositive b}`.
  have hset :
      {z : A × A | 0 ≤ z.1 ∧ IsStrictlyPositive z.2}
        = (Set.Ici (0 : A)) ×ˢ {b : A | IsStrictlyPositive b} := by
    ext ⟨a, b⟩
    simp [Set.mem_Ici, Set.mem_prod]
  rw [hset]
  -- First factor: `Set.Ici 0` is convex.
  have h1 : Convex ℝ (Set.Ici (0 : A)) := convex_Ici (0 : A)
  -- Second factor: strictly positive cone is convex (Piece C.2).
  have h2 : Convex ℝ {b : A | IsStrictlyPositive b} :=
    LTFP.MathlibExt.MatrixAnalysis.CFC.convex_setOf_isStrictlyPositive
  exact h1.prod h2

end RpowPerspective

end CFC
