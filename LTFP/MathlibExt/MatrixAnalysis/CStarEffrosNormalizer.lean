/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.MatrixAnalysis.CStarFin2HansenPedersen
import LTFP.MathlibExt.MatrixAnalysis.CStarRpowPerspective

/-!
# Effros normalizer identities

This file establishes three algebraic identities for the **Effros
normalizers** associated to a convex combination of strictly positive
elements in a unital C⋆-algebra. These identities are the algebraic
substrate of Effros's joint concavity theorem (B6 L3 Sub-Part 6.5) and
isolate three reusable building blocks:

1. The Effros normalizers form a partition of unity
   (`star v₁ * v₁ + star v₂ * v₂ = 1`).
2. The compression of the normalized inputs `xᵢ` by the normalizers
   recovers the normalized "mixed" input.
3. Outer conjugation of the compressed `xᵢ^p` by `b ^ (1/2)` recovers
   the weighted sum of `rpow` perspectives.

Concretely, given two strictly positive elements `b₁, b₂` of a unital
C⋆-algebra `A` and strictly positive weights `t, u ∈ ℝ` with
`t + u = 1`, set

```
b  := t • b₁ + u • b₂                       (also strictly positive)
v₁ := (Real.sqrt t : ℂ) • (b₁ ^ (1/2) * b ^ (-1/2))
v₂ := (Real.sqrt u : ℂ) • (b₂ ^ (1/2) * b ^ (-1/2))
xᵢ := bᵢ ^ (-1/2) * aᵢ * bᵢ ^ (-1/2)        (for 0 ≤ aᵢ)
```

The three lemmas below establish:

* `CFC.effros_normalizers_partition`:
  `star v₁ * v₁ + star v₂ * v₂ = 1`.

* `CFC.effros_normalized_input_sum`:
  `star v₁ * x₁ * v₁ + star v₂ * x₂ * v₂
     = b ^ (-1/2) * (t • a₁ + u • a₂) * b ^ (-1/2)`.

* `CFC.effros_conjugate_sum_rpow_eq_sum_rpowPerspective`:
  conjugating the sum `star v₁ * x₁^p * v₁ + star v₂ * x₂^p * v₂`
  by `b ^ (1/2)` on both sides recovers
  `t • CFC.rpowPerspective p a₁ b₁ + u • CFC.rpowPerspective p a₂ b₂`.

## Implementation notes

* We use **strictly positive** weights `0 < t, 0 < u` instead of
  `0 ≤ t, 0 ≤ u` because the Effros construction requires both
  `t • b₁` and `u • b₂` to be strictly positive (so that the convex
  combination `b := t • b₁ + u • b₂` is strictly positive). The
  boundary case `t = 0` (or `u = 0`) corresponds to a degenerate
  perspective and is handled separately in downstream applications of
  the joint-concavity inequality.

* The complex scalar `(Real.sqrt t : ℂ)` is converted to a real
  scalar via `Complex.coe_smul`, which is *definitionally* `t • x` on
  any `ℂ`-module. This keeps the proofs short and avoids juggling
  star-of-complex-coercion.

## References

* Effros, "A matrix convexity approach to some celebrated quantum
  inequalities", *Proc. Natl. Acad. Sci. USA* 106 (2009), 1006–1008.
-/

@[expose] public section

namespace CFC

section EffrosNormalizer

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-! ### Strict positivity of the convex combination -/

/-- The convex combination `t • b₁ + u • b₂` of two strictly positive
elements with strictly positive real weights is again strictly
positive. -/
private lemma isStrictlyPositive_convex_combination
    {b₁ b₂ : A} (hb₁ : IsStrictlyPositive b₁) (hb₂ : IsStrictlyPositive b₂)
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    IsStrictlyPositive (t • b₁ + u • b₂) := by
  have h₁ : IsStrictlyPositive (t • b₁) := IsStrictlyPositive.smul ht hb₁
  have h₂ : (0 : A) ≤ u • b₂ := smul_nonneg hu.le hb₂.nonneg
  exact h₁.add_nonneg h₂

/-! ### Real-scalar simplification for `Real.sqrt` coercions -/

omit [PartialOrder A] [StarOrderedRing A] in
/-- For `0 ≤ t : ℝ` and `x` in a `ℂ`-module, the scalar product
`(Real.sqrt t : ℂ) • (Real.sqrt t : ℂ) • x` collapses to `(t : ℂ) • x`.
We state this in `smul` form to match the `(Real.sqrt t : ℂ) • _`
patterns appearing in the Effros normalizers. -/
private lemma sqrt_smul_sqrt_smul {t : ℝ} (ht : 0 ≤ t) (x : A) :
    (Real.sqrt t : ℂ) • (Real.sqrt t : ℂ) • x = (t : ℂ) • x := by
  rw [smul_smul, ← Complex.ofReal_mul, Real.mul_self_sqrt ht]

/-! ### Lemma 6.4.a: partition of unity -/

/-- **Effros normalizers form a partition of unity.**

For strictly positive elements `b₁, b₂` and strictly positive weights
`t, u` with `t + u = 1`, the elements

```
v₁ := (Real.sqrt t : ℂ) • (b₁ ^ (1/2) * b ^ (-1/2))
v₂ := (Real.sqrt u : ℂ) • (b₂ ^ (1/2) * b ^ (-1/2))
```

(where `b := t • b₁ + u • b₂`) satisfy
`star v₁ * v₁ + star v₂ * v₂ = 1`. -/
theorem effros_normalizers_partition
    {b₁ b₂ : A} (hb₁ : IsStrictlyPositive b₁) (hb₂ : IsStrictlyPositive b₂)
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) (_htu : t + u = 1) :
    let b := t • b₁ + u • b₂
    star ((Real.sqrt t : ℂ) • (b₁ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) *
        ((Real.sqrt t : ℂ) • (b₁ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) +
      star ((Real.sqrt u : ℂ) • (b₂ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) *
        ((Real.sqrt u : ℂ) • (b₂ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) = 1 := by
  -- Introduce the local `let` binding `b := t • b₁ + u • b₂`.
  intro b
  have hb : IsStrictlyPositive b :=
    isStrictlyPositive_convex_combination hb₁ hb₂ ht hu
  -- Self-adjointness of all rpow factors.
  have hsa_b_neg : IsSelfAdjoint (b ^ (-(1 / 2) : ℝ)) :=
    IsSelfAdjoint.of_nonneg rpow_nonneg
  have hsa_b₁ : IsSelfAdjoint (b₁ ^ (1 / 2 : ℝ)) :=
    IsSelfAdjoint.of_nonneg rpow_nonneg
  have hsa_b₂ : IsSelfAdjoint (b₂ ^ (1 / 2 : ℝ)) :=
    IsSelfAdjoint.of_nonneg rpow_nonneg
  -- Compute `star v₁ * v₁` and `star v₂ * v₂` in terms of `b^(-1/2) * (s • bᵢ) * b^(-1/2)`.
  have hv₁ :
      star ((Real.sqrt t : ℂ) • (b₁ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) *
          ((Real.sqrt t : ℂ) • (b₁ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) =
        b ^ (-(1 / 2) : ℝ) * (t • b₁) * b ^ (-(1 / 2) : ℝ) := by
    -- Distribute `star` and `smul` over `mul`.
    rw [star_smul, star_mul, hsa_b_neg.star_eq, hsa_b₁.star_eq,
      Complex.star_def, Complex.conj_ofReal,
      smul_mul_assoc, mul_smul_comm, sqrt_smul_sqrt_smul ht.le]
    -- Reassemble: `b^(-1/2) * (b₁^(1/2) * b₁^(1/2)) * b^(-1/2) = b^(-1/2) * b₁ * b^(-1/2)`,
    -- and `t • (b^(-1/2) * b₁ * b^(-1/2)) = b^(-1/2) * (t • b₁) * b^(-1/2)`.
    have hmul :
        b ^ (-(1 / 2) : ℝ) * b₁ ^ (1 / 2 : ℝ) *
            (b₁ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ)) =
          b ^ (-(1 / 2) : ℝ) * b₁ * b ^ (-(1 / 2) : ℝ) := by
      have hsum :
          b₁ ^ (1 / 2 : ℝ) * b₁ ^ (1 / 2 : ℝ) = b₁ := by
        rw [← rpow_add hb₁.isUnit]
        norm_num
        exact rpow_one b₁
      calc
        b ^ (-(1 / 2) : ℝ) * b₁ ^ (1 / 2 : ℝ) *
            (b₁ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))
            = b ^ (-(1 / 2) : ℝ) *
                (b₁ ^ (1 / 2 : ℝ) * b₁ ^ (1 / 2 : ℝ)) * b ^ (-(1 / 2) : ℝ) := by
              noncomm_ring
        _ = b ^ (-(1 / 2) : ℝ) * b₁ * b ^ (-(1 / 2) : ℝ) := by rw [hsum]
    rw [hmul]
    -- Goal: `(t : ℂ) • (b^(-1/2) * b₁ * b^(-1/2)) = b^(-1/2) * (t • b₁) * b^(-1/2)`.
    rw [show (t : ℂ) • (b ^ (-(1 / 2) : ℝ) * b₁ * b ^ (-(1 / 2) : ℝ))
            = b ^ (-(1 / 2) : ℝ) * ((t : ℂ) • b₁) * b ^ (-(1 / 2) : ℝ) from by
          calc
            (t : ℂ) • (b ^ (-(1 / 2) : ℝ) * b₁ * b ^ (-(1 / 2) : ℝ))
                = (t : ℂ) • (b ^ (-(1 / 2) : ℝ) * (b₁ * b ^ (-(1 / 2) : ℝ))) := by
                  rw [mul_assoc]
            _ = b ^ (-(1 / 2) : ℝ) * ((t : ℂ) • (b₁ * b ^ (-(1 / 2) : ℝ))) := by
                  rw [mul_smul_comm]
            _ = b ^ (-(1 / 2) : ℝ) * (((t : ℂ) • b₁) * b ^ (-(1 / 2) : ℝ)) := by
                  rw [smul_mul_assoc]
            _ = b ^ (-(1 / 2) : ℝ) * ((t : ℂ) • b₁) * b ^ (-(1 / 2) : ℝ) := by
                  rw [← mul_assoc],
        Complex.coe_smul]
  have hv₂ :
      star ((Real.sqrt u : ℂ) • (b₂ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) *
          ((Real.sqrt u : ℂ) • (b₂ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) =
        b ^ (-(1 / 2) : ℝ) * (u • b₂) * b ^ (-(1 / 2) : ℝ) := by
    rw [star_smul, star_mul, hsa_b_neg.star_eq, hsa_b₂.star_eq,
      Complex.star_def, Complex.conj_ofReal,
      smul_mul_assoc, mul_smul_comm, sqrt_smul_sqrt_smul hu.le]
    have hmul :
        b ^ (-(1 / 2) : ℝ) * b₂ ^ (1 / 2 : ℝ) *
            (b₂ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ)) =
          b ^ (-(1 / 2) : ℝ) * b₂ * b ^ (-(1 / 2) : ℝ) := by
      have hsum :
          b₂ ^ (1 / 2 : ℝ) * b₂ ^ (1 / 2 : ℝ) = b₂ := by
        rw [← rpow_add hb₂.isUnit]
        norm_num
        exact rpow_one b₂
      calc
        b ^ (-(1 / 2) : ℝ) * b₂ ^ (1 / 2 : ℝ) *
            (b₂ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))
            = b ^ (-(1 / 2) : ℝ) *
                (b₂ ^ (1 / 2 : ℝ) * b₂ ^ (1 / 2 : ℝ)) * b ^ (-(1 / 2) : ℝ) := by
              noncomm_ring
        _ = b ^ (-(1 / 2) : ℝ) * b₂ * b ^ (-(1 / 2) : ℝ) := by rw [hsum]
    rw [hmul]
    rw [show (u : ℂ) • (b ^ (-(1 / 2) : ℝ) * b₂ * b ^ (-(1 / 2) : ℝ))
            = b ^ (-(1 / 2) : ℝ) * ((u : ℂ) • b₂) * b ^ (-(1 / 2) : ℝ) from by
          calc
            (u : ℂ) • (b ^ (-(1 / 2) : ℝ) * b₂ * b ^ (-(1 / 2) : ℝ))
                = (u : ℂ) • (b ^ (-(1 / 2) : ℝ) * (b₂ * b ^ (-(1 / 2) : ℝ))) := by
                  rw [mul_assoc]
            _ = b ^ (-(1 / 2) : ℝ) * ((u : ℂ) • (b₂ * b ^ (-(1 / 2) : ℝ))) := by
                  rw [mul_smul_comm]
            _ = b ^ (-(1 / 2) : ℝ) * (((u : ℂ) • b₂) * b ^ (-(1 / 2) : ℝ)) := by
                  rw [smul_mul_assoc]
            _ = b ^ (-(1 / 2) : ℝ) * ((u : ℂ) • b₂) * b ^ (-(1 / 2) : ℝ) := by
                  rw [← mul_assoc],
        Complex.coe_smul]
  -- Sum and apply `conjugate_rpow_neg_one_half` to `b`.
  rw [hv₁, hv₂]
  rw [show b ^ (-(1 / 2) : ℝ) * (t • b₁) * b ^ (-(1 / 2) : ℝ)
        + b ^ (-(1 / 2) : ℝ) * (u • b₂) * b ^ (-(1 / 2) : ℝ)
        = b ^ (-(1 / 2) : ℝ) * (t • b₁ + u • b₂) * b ^ (-(1 / 2) : ℝ) by
        rw [mul_add, add_mul]]
  -- `b = t • b₁ + u • b₂` definitionally via the `let` binding.
  exact CFC.conjugate_rpow_neg_one_half b

/-! ### Lemma 6.4.b: normalized-input compression -/

/-- **Compression of normalized inputs by the Effros normalizers.**

For `0 ≤ aᵢ` and strictly positive `bᵢ`, set the normalized inputs
`xᵢ := bᵢ ^ (-1/2) * aᵢ * bᵢ ^ (-1/2)` and the Effros normalizers
`vᵢ := (Real.sqrt weightᵢ : ℂ) • (bᵢ ^ (1/2) * b ^ (-1/2))` where
`b := t • b₁ + u • b₂`. Then

```
star v₁ * x₁ * v₁ + star v₂ * x₂ * v₂
  = b ^ (-1/2) * (t • a₁ + u • a₂) * b ^ (-1/2).
```

In particular, the right-hand side is the normalized "mixed" input
associated to the convex combination of `(a₁, a₂)`. -/
theorem effros_normalized_input_sum
    {a₁ a₂ b₁ b₂ : A} (_ha₁ : 0 ≤ a₁) (_ha₂ : 0 ≤ a₂)
    (hb₁ : IsStrictlyPositive b₁) (hb₂ : IsStrictlyPositive b₂)
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    let b := t • b₁ + u • b₂
    let x₁ := b₁ ^ (-(1 / 2) : ℝ) * a₁ * b₁ ^ (-(1 / 2) : ℝ)
    let x₂ := b₂ ^ (-(1 / 2) : ℝ) * a₂ * b₂ ^ (-(1 / 2) : ℝ)
    star ((Real.sqrt t : ℂ) • (b₁ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) *
        x₁ *
        ((Real.sqrt t : ℂ) • (b₁ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) +
      star ((Real.sqrt u : ℂ) • (b₂ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) *
        x₂ *
        ((Real.sqrt u : ℂ) • (b₂ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) =
      b ^ (-(1 / 2) : ℝ) * (t • a₁ + u • a₂) * b ^ (-(1 / 2) : ℝ) := by
  intro b x₁ x₂
  -- Self-adjointness of all rpow factors.
  have hsa_b_neg : IsSelfAdjoint (b ^ (-(1 / 2) : ℝ)) :=
    IsSelfAdjoint.of_nonneg rpow_nonneg
  have hsa_b₁ : IsSelfAdjoint (b₁ ^ (1 / 2 : ℝ)) :=
    IsSelfAdjoint.of_nonneg rpow_nonneg
  have hsa_b₂ : IsSelfAdjoint (b₂ ^ (1 / 2 : ℝ)) :=
    IsSelfAdjoint.of_nonneg rpow_nonneg
  -- Reduce `b₁^(1/2) * (b₁^(-1/2) * a₁ * b₁^(-1/2)) * b₁^(1/2) = a₁`.
  have hcancel₁ :
      b₁ ^ (1 / 2 : ℝ) * (b₁ ^ (-(1 / 2) : ℝ) * a₁ * b₁ ^ (-(1 / 2) : ℝ)) *
          b₁ ^ (1 / 2 : ℝ) = a₁ := by
    have h1 : b₁ ^ (1 / 2 : ℝ) * b₁ ^ (-(1 / 2) : ℝ) = 1 := by
      rw [← rpow_add hb₁.isUnit]; norm_num; exact rpow_zero b₁
    have h2 : b₁ ^ (-(1 / 2) : ℝ) * b₁ ^ (1 / 2 : ℝ) = 1 := by
      rw [← rpow_add hb₁.isUnit]; norm_num; exact rpow_zero b₁
    calc
      b₁ ^ (1 / 2 : ℝ) * (b₁ ^ (-(1 / 2) : ℝ) * a₁ * b₁ ^ (-(1 / 2) : ℝ)) *
          b₁ ^ (1 / 2 : ℝ)
          = (b₁ ^ (1 / 2 : ℝ) * b₁ ^ (-(1 / 2) : ℝ)) * a₁ *
              (b₁ ^ (-(1 / 2) : ℝ) * b₁ ^ (1 / 2 : ℝ)) := by noncomm_ring
      _ = 1 * a₁ * 1 := by rw [h1, h2]
      _ = a₁ := by rw [mul_one, one_mul]
  have hcancel₂ :
      b₂ ^ (1 / 2 : ℝ) * (b₂ ^ (-(1 / 2) : ℝ) * a₂ * b₂ ^ (-(1 / 2) : ℝ)) *
          b₂ ^ (1 / 2 : ℝ) = a₂ := by
    have h1 : b₂ ^ (1 / 2 : ℝ) * b₂ ^ (-(1 / 2) : ℝ) = 1 := by
      rw [← rpow_add hb₂.isUnit]; norm_num; exact rpow_zero b₂
    have h2 : b₂ ^ (-(1 / 2) : ℝ) * b₂ ^ (1 / 2 : ℝ) = 1 := by
      rw [← rpow_add hb₂.isUnit]; norm_num; exact rpow_zero b₂
    calc
      b₂ ^ (1 / 2 : ℝ) * (b₂ ^ (-(1 / 2) : ℝ) * a₂ * b₂ ^ (-(1 / 2) : ℝ)) *
          b₂ ^ (1 / 2 : ℝ)
          = (b₂ ^ (1 / 2 : ℝ) * b₂ ^ (-(1 / 2) : ℝ)) * a₂ *
              (b₂ ^ (-(1 / 2) : ℝ) * b₂ ^ (1 / 2 : ℝ)) := by noncomm_ring
      _ = 1 * a₂ * 1 := by rw [h1, h2]
      _ = a₂ := by rw [mul_one, one_mul]
  -- Expand `star v₁ * x₁ * v₁`.
  have hv₁ :
      star ((Real.sqrt t : ℂ) • (b₁ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) *
          x₁ *
          ((Real.sqrt t : ℂ) • (b₁ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) =
        b ^ (-(1 / 2) : ℝ) * (t • a₁) * b ^ (-(1 / 2) : ℝ) := by
    simp only [x₁]
    rw [star_smul, star_mul, hsa_b_neg.star_eq, hsa_b₁.star_eq,
      Complex.star_def, Complex.conj_ofReal,
      smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
      sqrt_smul_sqrt_smul ht.le]
    -- After distribution, the inner product is
    -- `(b^(-1/2) * b₁^(1/2)) * (b₁^(-1/2) * a₁ * b₁^(-1/2)) * (b₁^(1/2) * b^(-1/2))`.
    have hmul :
        b ^ (-(1 / 2) : ℝ) * b₁ ^ (1 / 2 : ℝ) *
            (b₁ ^ (-(1 / 2) : ℝ) * a₁ * b₁ ^ (-(1 / 2) : ℝ)) *
            (b₁ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ)) =
          b ^ (-(1 / 2) : ℝ) * a₁ * b ^ (-(1 / 2) : ℝ) := by
      calc
        b ^ (-(1 / 2) : ℝ) * b₁ ^ (1 / 2 : ℝ) *
            (b₁ ^ (-(1 / 2) : ℝ) * a₁ * b₁ ^ (-(1 / 2) : ℝ)) *
            (b₁ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))
            = b ^ (-(1 / 2) : ℝ) *
                (b₁ ^ (1 / 2 : ℝ) *
                  (b₁ ^ (-(1 / 2) : ℝ) * a₁ * b₁ ^ (-(1 / 2) : ℝ)) *
                  b₁ ^ (1 / 2 : ℝ)) *
                b ^ (-(1 / 2) : ℝ) := by noncomm_ring
        _ = b ^ (-(1 / 2) : ℝ) * a₁ * b ^ (-(1 / 2) : ℝ) := by rw [hcancel₁]
    rw [hmul]
    rw [show (t : ℂ) • (b ^ (-(1 / 2) : ℝ) * a₁ * b ^ (-(1 / 2) : ℝ))
            = b ^ (-(1 / 2) : ℝ) * ((t : ℂ) • a₁) * b ^ (-(1 / 2) : ℝ) from by
          calc
            (t : ℂ) • (b ^ (-(1 / 2) : ℝ) * a₁ * b ^ (-(1 / 2) : ℝ))
                = (t : ℂ) • (b ^ (-(1 / 2) : ℝ) * (a₁ * b ^ (-(1 / 2) : ℝ))) := by
                  rw [mul_assoc]
            _ = b ^ (-(1 / 2) : ℝ) * ((t : ℂ) • (a₁ * b ^ (-(1 / 2) : ℝ))) := by
                  rw [mul_smul_comm]
            _ = b ^ (-(1 / 2) : ℝ) * (((t : ℂ) • a₁) * b ^ (-(1 / 2) : ℝ)) := by
                  rw [smul_mul_assoc]
            _ = b ^ (-(1 / 2) : ℝ) * ((t : ℂ) • a₁) * b ^ (-(1 / 2) : ℝ) := by
                  rw [← mul_assoc],
        Complex.coe_smul]
  have hv₂ :
      star ((Real.sqrt u : ℂ) • (b₂ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) *
          x₂ *
          ((Real.sqrt u : ℂ) • (b₂ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) =
        b ^ (-(1 / 2) : ℝ) * (u • a₂) * b ^ (-(1 / 2) : ℝ) := by
    simp only [x₂]
    rw [star_smul, star_mul, hsa_b_neg.star_eq, hsa_b₂.star_eq,
      Complex.star_def, Complex.conj_ofReal,
      smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
      sqrt_smul_sqrt_smul hu.le]
    have hmul :
        b ^ (-(1 / 2) : ℝ) * b₂ ^ (1 / 2 : ℝ) *
            (b₂ ^ (-(1 / 2) : ℝ) * a₂ * b₂ ^ (-(1 / 2) : ℝ)) *
            (b₂ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ)) =
          b ^ (-(1 / 2) : ℝ) * a₂ * b ^ (-(1 / 2) : ℝ) := by
      calc
        b ^ (-(1 / 2) : ℝ) * b₂ ^ (1 / 2 : ℝ) *
            (b₂ ^ (-(1 / 2) : ℝ) * a₂ * b₂ ^ (-(1 / 2) : ℝ)) *
            (b₂ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))
            = b ^ (-(1 / 2) : ℝ) *
                (b₂ ^ (1 / 2 : ℝ) *
                  (b₂ ^ (-(1 / 2) : ℝ) * a₂ * b₂ ^ (-(1 / 2) : ℝ)) *
                  b₂ ^ (1 / 2 : ℝ)) *
                b ^ (-(1 / 2) : ℝ) := by noncomm_ring
        _ = b ^ (-(1 / 2) : ℝ) * a₂ * b ^ (-(1 / 2) : ℝ) := by rw [hcancel₂]
    rw [hmul]
    rw [show (u : ℂ) • (b ^ (-(1 / 2) : ℝ) * a₂ * b ^ (-(1 / 2) : ℝ))
            = b ^ (-(1 / 2) : ℝ) * ((u : ℂ) • a₂) * b ^ (-(1 / 2) : ℝ) from by
          calc
            (u : ℂ) • (b ^ (-(1 / 2) : ℝ) * a₂ * b ^ (-(1 / 2) : ℝ))
                = (u : ℂ) • (b ^ (-(1 / 2) : ℝ) * (a₂ * b ^ (-(1 / 2) : ℝ))) := by
                  rw [mul_assoc]
            _ = b ^ (-(1 / 2) : ℝ) * ((u : ℂ) • (a₂ * b ^ (-(1 / 2) : ℝ))) := by
                  rw [mul_smul_comm]
            _ = b ^ (-(1 / 2) : ℝ) * (((u : ℂ) • a₂) * b ^ (-(1 / 2) : ℝ)) := by
                  rw [smul_mul_assoc]
            _ = b ^ (-(1 / 2) : ℝ) * ((u : ℂ) • a₂) * b ^ (-(1 / 2) : ℝ) := by
                  rw [← mul_assoc],
        Complex.coe_smul]
  rw [hv₁, hv₂]
  rw [mul_add, add_mul]

/-! ### Lemma 6.4.c: outer conjugation recovers the weighted perspective sum -/

/-- **Outer conjugation by `b ^ (1/2)` recovers the weighted perspective sum.**

For `0 ≤ aᵢ` and strictly positive `bᵢ`, the standard normalized
inputs `xᵢ := bᵢ ^ (-1/2) * aᵢ * bᵢ ^ (-1/2)` and Effros normalizers
`vᵢ := (Real.sqrt weightᵢ : ℂ) • (bᵢ ^ (1/2) * b ^ (-1/2))` satisfy

```
b ^ (1/2) * (star v₁ * x₁^p * v₁ + star v₂ * x₂^p * v₂) * b ^ (1/2)
  = t • rpowPerspective p a₁ b₁ + u • rpowPerspective p a₂ b₂.
```

This is the key algebraic identity that, combined with the
Hansen-Pedersen Jensen inequality (B6 L3 Sub-Part 6.2), yields the
joint operator concavity / convexity of `CFC.rpowPerspective` in B6
L3 Sub-Part 6.5. -/
theorem effros_conjugate_sum_rpow_eq_sum_rpowPerspective
    {p : ℝ} {a₁ a₂ b₁ b₂ : A} (_ha₁ : 0 ≤ a₁) (_ha₂ : 0 ≤ a₂)
    (hb₁ : IsStrictlyPositive b₁) (hb₂ : IsStrictlyPositive b₂)
    {t u : ℝ} (ht : 0 < t) (hu : 0 < u) :
    let b := t • b₁ + u • b₂
    let x₁ := b₁ ^ (-(1 / 2) : ℝ) * a₁ * b₁ ^ (-(1 / 2) : ℝ)
    let x₂ := b₂ ^ (-(1 / 2) : ℝ) * a₂ * b₂ ^ (-(1 / 2) : ℝ)
    b ^ (1 / 2 : ℝ) *
        (star ((Real.sqrt t : ℂ) • (b₁ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) *
            (x₁ ^ p) *
            ((Real.sqrt t : ℂ) • (b₁ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) +
          star ((Real.sqrt u : ℂ) • (b₂ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) *
            (x₂ ^ p) *
            ((Real.sqrt u : ℂ) • (b₂ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ)))) *
        b ^ (1 / 2 : ℝ) =
      t • CFC.rpowPerspective p a₁ b₁ + u • CFC.rpowPerspective p a₂ b₂ := by
  intro b x₁ x₂
  -- Self-adjointness of all rpow factors.
  have hsa_b_neg : IsSelfAdjoint (b ^ (-(1 / 2) : ℝ)) :=
    IsSelfAdjoint.of_nonneg rpow_nonneg
  have hsa_b₁_half : IsSelfAdjoint (b₁ ^ (1 / 2 : ℝ)) :=
    IsSelfAdjoint.of_nonneg rpow_nonneg
  have hsa_b₂_half : IsSelfAdjoint (b₂ ^ (1 / 2 : ℝ)) :=
    IsSelfAdjoint.of_nonneg rpow_nonneg
  -- Cancellation identities: `b^(1/2) * b^(-1/2) = 1` and its mirror.
  have hb_cancel_right : b ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ) = 1 := by
    have hb : IsStrictlyPositive b :=
      isStrictlyPositive_convex_combination hb₁ hb₂ ht hu
    rw [← rpow_add hb.isUnit]; norm_num; exact rpow_zero b
  have hb_cancel_left : b ^ (-(1 / 2) : ℝ) * b ^ (1 / 2 : ℝ) = 1 := by
    have hb : IsStrictlyPositive b :=
      isStrictlyPositive_convex_combination hb₁ hb₂ ht hu
    rw [← rpow_add hb.isUnit]; norm_num; exact rpow_zero b
  -- The key per-index identity (i = 1):
  -- `b^(1/2) * (star v₁ * x₁^p * v₁) * b^(1/2) = t • rpowPerspective p a₁ b₁`.
  have hkey₁ :
      b ^ (1 / 2 : ℝ) *
          (star ((Real.sqrt t : ℂ) • (b₁ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) *
              (x₁ ^ p) *
              ((Real.sqrt t : ℂ) • (b₁ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ)))) *
          b ^ (1 / 2 : ℝ) =
        t • CFC.rpowPerspective p a₁ b₁ := by
    -- We use the partial result from 6.4.b applied to `x₁^p`: namely,
    -- `star v₁ * (x₁^p) * v₁ = b^(-1/2) * (t • (b₁^(1/2) * x₁^p * b₁^(1/2))) * b^(-1/2)`.
    -- Conjugating by `b^(1/2)` outside cancels the `b^(±1/2)` factors.
    have hcalc :
        star ((Real.sqrt t : ℂ) • (b₁ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) *
            (x₁ ^ p) *
            ((Real.sqrt t : ℂ) • (b₁ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) =
          b ^ (-(1 / 2) : ℝ) *
            (t • (b₁ ^ (1 / 2 : ℝ) * (x₁ ^ p) * b₁ ^ (1 / 2 : ℝ))) *
            b ^ (-(1 / 2) : ℝ) := by
      rw [star_smul, star_mul, hsa_b_neg.star_eq, hsa_b₁_half.star_eq,
        Complex.star_def, Complex.conj_ofReal]
      -- Compute LHS as `(sqrt t • (b^(-1/2) * b₁^(1/2))) * x₁^p * (sqrt t • (b₁^(1/2) * b^(-1/2)))`.
      -- Collect both scalars to t and reassemble.
      calc
        (Real.sqrt t : ℂ) • (b ^ (-(1 / 2) : ℝ) * b₁ ^ (1 / 2 : ℝ)) *
            (x₁ ^ p) *
            ((Real.sqrt t : ℂ) • (b₁ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ)))
            = ((Real.sqrt t : ℂ) * (Real.sqrt t : ℂ)) •
                (b ^ (-(1 / 2) : ℝ) * b₁ ^ (1 / 2 : ℝ) *
                  (x₁ ^ p) *
                  (b₁ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) := by
              rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul]
        _ = (t : ℂ) •
                (b ^ (-(1 / 2) : ℝ) * b₁ ^ (1 / 2 : ℝ) *
                  (x₁ ^ p) *
                  (b₁ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) := by
              rw [← Complex.ofReal_mul, Real.mul_self_sqrt ht.le]
        _ = t • (b ^ (-(1 / 2) : ℝ) * b₁ ^ (1 / 2 : ℝ) *
                  (x₁ ^ p) *
                  (b₁ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) := by
              rw [Complex.coe_smul]
        _ = t • (b ^ (-(1 / 2) : ℝ) *
                  (b₁ ^ (1 / 2 : ℝ) * (x₁ ^ p) * b₁ ^ (1 / 2 : ℝ)) *
                  b ^ (-(1 / 2) : ℝ)) := by
              congr 1
              noncomm_ring
        _ = b ^ (-(1 / 2) : ℝ) *
                (t • (b₁ ^ (1 / 2 : ℝ) * (x₁ ^ p) * b₁ ^ (1 / 2 : ℝ))) *
                b ^ (-(1 / 2) : ℝ) := by
              rw [← smul_mul_assoc, mul_smul_comm]
    rw [hcalc]
    -- Now goal: `b^(1/2) * (b^(-1/2) * (t • (...)) * b^(-1/2)) * b^(1/2) = t • rpowPerspective p a₁ b₁`.
    have hconjugate :
        b ^ (1 / 2 : ℝ) *
            (b ^ (-(1 / 2) : ℝ) *
              (t • (b₁ ^ (1 / 2 : ℝ) * (x₁ ^ p) * b₁ ^ (1 / 2 : ℝ))) *
              b ^ (-(1 / 2) : ℝ)) *
            b ^ (1 / 2 : ℝ) =
          t • (b₁ ^ (1 / 2 : ℝ) * (x₁ ^ p) * b₁ ^ (1 / 2 : ℝ)) := by
      calc
        b ^ (1 / 2 : ℝ) *
            (b ^ (-(1 / 2) : ℝ) *
              (t • (b₁ ^ (1 / 2 : ℝ) * (x₁ ^ p) * b₁ ^ (1 / 2 : ℝ))) *
              b ^ (-(1 / 2) : ℝ)) *
            b ^ (1 / 2 : ℝ)
            = (b ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ)) *
                (t • (b₁ ^ (1 / 2 : ℝ) * (x₁ ^ p) * b₁ ^ (1 / 2 : ℝ))) *
                (b ^ (-(1 / 2) : ℝ) * b ^ (1 / 2 : ℝ)) := by noncomm_ring
        _ = 1 * (t • (b₁ ^ (1 / 2 : ℝ) * (x₁ ^ p) * b₁ ^ (1 / 2 : ℝ))) * 1 := by
              rw [hb_cancel_right, hb_cancel_left]
        _ = t • (b₁ ^ (1 / 2 : ℝ) * (x₁ ^ p) * b₁ ^ (1 / 2 : ℝ)) := by
              rw [mul_one, one_mul]
    rw [hconjugate]
    -- Unfold `rpowPerspective` and `x₁`.
    simp only [CFC.rpowPerspective, x₁]
  -- Per-index identity (i = 2), by symmetry.
  have hkey₂ :
      b ^ (1 / 2 : ℝ) *
          (star ((Real.sqrt u : ℂ) • (b₂ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) *
              (x₂ ^ p) *
              ((Real.sqrt u : ℂ) • (b₂ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ)))) *
          b ^ (1 / 2 : ℝ) =
        u • CFC.rpowPerspective p a₂ b₂ := by
    have hcalc :
        star ((Real.sqrt u : ℂ) • (b₂ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) *
            (x₂ ^ p) *
            ((Real.sqrt u : ℂ) • (b₂ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) =
          b ^ (-(1 / 2) : ℝ) *
            (u • (b₂ ^ (1 / 2 : ℝ) * (x₂ ^ p) * b₂ ^ (1 / 2 : ℝ))) *
            b ^ (-(1 / 2) : ℝ) := by
      rw [star_smul, star_mul, hsa_b_neg.star_eq, hsa_b₂_half.star_eq,
        Complex.star_def, Complex.conj_ofReal]
      calc
        (Real.sqrt u : ℂ) • (b ^ (-(1 / 2) : ℝ) * b₂ ^ (1 / 2 : ℝ)) *
            (x₂ ^ p) *
            ((Real.sqrt u : ℂ) • (b₂ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ)))
            = ((Real.sqrt u : ℂ) * (Real.sqrt u : ℂ)) •
                (b ^ (-(1 / 2) : ℝ) * b₂ ^ (1 / 2 : ℝ) *
                  (x₂ ^ p) *
                  (b₂ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) := by
              rw [smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul]
        _ = (u : ℂ) •
                (b ^ (-(1 / 2) : ℝ) * b₂ ^ (1 / 2 : ℝ) *
                  (x₂ ^ p) *
                  (b₂ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) := by
              rw [← Complex.ofReal_mul, Real.mul_self_sqrt hu.le]
        _ = u • (b ^ (-(1 / 2) : ℝ) * b₂ ^ (1 / 2 : ℝ) *
                  (x₂ ^ p) *
                  (b₂ ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ))) := by
              rw [Complex.coe_smul]
        _ = u • (b ^ (-(1 / 2) : ℝ) *
                  (b₂ ^ (1 / 2 : ℝ) * (x₂ ^ p) * b₂ ^ (1 / 2 : ℝ)) *
                  b ^ (-(1 / 2) : ℝ)) := by
              congr 1
              noncomm_ring
        _ = b ^ (-(1 / 2) : ℝ) *
                (u • (b₂ ^ (1 / 2 : ℝ) * (x₂ ^ p) * b₂ ^ (1 / 2 : ℝ))) *
                b ^ (-(1 / 2) : ℝ) := by
              rw [← smul_mul_assoc, mul_smul_comm]
    rw [hcalc]
    have hconjugate :
        b ^ (1 / 2 : ℝ) *
            (b ^ (-(1 / 2) : ℝ) *
              (u • (b₂ ^ (1 / 2 : ℝ) * (x₂ ^ p) * b₂ ^ (1 / 2 : ℝ))) *
              b ^ (-(1 / 2) : ℝ)) *
            b ^ (1 / 2 : ℝ) =
          u • (b₂ ^ (1 / 2 : ℝ) * (x₂ ^ p) * b₂ ^ (1 / 2 : ℝ)) := by
      calc
        b ^ (1 / 2 : ℝ) *
            (b ^ (-(1 / 2) : ℝ) *
              (u • (b₂ ^ (1 / 2 : ℝ) * (x₂ ^ p) * b₂ ^ (1 / 2 : ℝ))) *
              b ^ (-(1 / 2) : ℝ)) *
            b ^ (1 / 2 : ℝ)
            = (b ^ (1 / 2 : ℝ) * b ^ (-(1 / 2) : ℝ)) *
                (u • (b₂ ^ (1 / 2 : ℝ) * (x₂ ^ p) * b₂ ^ (1 / 2 : ℝ))) *
                (b ^ (-(1 / 2) : ℝ) * b ^ (1 / 2 : ℝ)) := by noncomm_ring
        _ = 1 * (u • (b₂ ^ (1 / 2 : ℝ) * (x₂ ^ p) * b₂ ^ (1 / 2 : ℝ))) * 1 := by
              rw [hb_cancel_right, hb_cancel_left]
        _ = u • (b₂ ^ (1 / 2 : ℝ) * (x₂ ^ p) * b₂ ^ (1 / 2 : ℝ)) := by
              rw [mul_one, one_mul]
    rw [hconjugate]
    simp only [CFC.rpowPerspective, x₂]
  -- Distribute the outer `b^(1/2) * _ * b^(1/2)` over the inner sum.
  rw [mul_add, add_mul, hkey₁, hkey₂]

end EffrosNormalizer

end CFC
