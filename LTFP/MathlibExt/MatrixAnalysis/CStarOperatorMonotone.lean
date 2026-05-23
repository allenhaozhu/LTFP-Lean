/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Order

/-!
# Operator-monotone powers on nonnegative CStarMatrix type copies

This file records a finite-matrix-facing wrapper around Mathlib's C⋆-algebra
operator-monotonicity theorem for powers `t ↦ t ^ p`, `p ∈ [0, 1]`.

The existing universal `OperatorMonotone` predicate for `Matrix n n 𝕜`
quantifies over all Hermitian matrices, with no positivity/domain hypothesis.
That predicate is intentionally not used for `Real.rpow`, since `Real.rpow`
is not monotone on all of `ℝ`.

Also includes the strictly-positive-cone variant
`CStarOperatorMonotoneOnStrictlyPos` and the corresponding `Real.log`
instance via `CFC.log_monotoneOn`.
-/

namespace LTFP.MathlibExt.MatrixAnalysis

universe uA un

/-! ### CStarAlgebra-level lift

Abstract CStarAlgebra-cone operator-monotone predicates parallel to the
finite `CStarMatrix` wrappers below. These are direct CFC wrappers around
`CFC.monotone_rpow` and `CFC.log_monotoneOn` lifted to a `CStarAlgebra`-
level predicate, so downstream callers can quantify over arbitrary unital
C⋆-algebras (not just finite `CStarMatrix n n A`). Distinct from the
finite `CStarOperatorMonotoneOnNonneg` below — no name collision.
-/

/-- A real function is operator monotone on the nonnegative cone of every unital
C⋆-algebra if real CFC by that function preserves spectral order there. -/
def CStarAlgebraOperatorMonotoneOnNonneg (f : ℝ → ℝ) : Prop :=
  ∀ {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A],
    MonotoneOn (fun a : A => cfc f a) {a | 0 ≤ a}

/-- `t ↦ t ^ p` is operator monotone on the nonnegative cone of every unital
C⋆-algebra for `p ∈ [0, 1]`. -/
theorem cStarAlgebraOperatorMonotoneOnNonneg_rpow {p : ℝ} (hp : p ∈ Set.Icc 0 1) :
    CStarAlgebraOperatorMonotoneOnNonneg.{uA} (fun t : ℝ => t ^ p) := by
  intro A _ _ _ a ha b hb hab
  change cfc (fun t : ℝ => t ^ p) a ≤ cfc (fun t : ℝ => t ^ p) b
  rw [← CFC.rpow_eq_cfc_real (a := a) (y := p) ha,
    ← CFC.rpow_eq_cfc_real (a := b) (y := p) hb]
  exact CFC.monotone_rpow (A := A) hp hab

/-- A real function is operator monotone on the strictly-positive cone of every
unital C⋆-algebra if real CFC by that function preserves spectral order there. -/
def CStarAlgebraOperatorMonotoneOnStrictlyPos (f : ℝ → ℝ) : Prop :=
  ∀ {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A],
    MonotoneOn (fun a : A => cfc f a) {a | IsStrictlyPositive a}

/-- The natural logarithm is operator monotone on the strictly-positive cone of
every unital C⋆-algebra, via Mathlib's `CFC.log_monotoneOn`. -/
theorem cStarAlgebraOperatorMonotoneOnStrictlyPos_log :
    CStarAlgebraOperatorMonotoneOnStrictlyPos.{uA} Real.log := by
  intro A _ _ _ a ha b hb hab
  change cfc Real.log a ≤ cfc Real.log b
  exact CFC.log_monotoneOn (A := A) ha hb hab

/-! ### Finite `CStarMatrix` wrappers -/

/-- A real function is operator monotone on the nonnegative cone of finite
`CStarMatrix` type copies if real CFC by that function preserves spectral order
there. -/
def CStarOperatorMonotoneOnNonneg (f : ℝ → ℝ) : Prop :=
  ∀ {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {n : Type un} [Fintype n] [DecidableEq n],
    MonotoneOn (fun M : CStarMatrix n n A => cfc f M) {M | 0 ≤ M}

/-- `t ↦ t ^ p` is operator monotone on the nonnegative cone of finite
`CStarMatrix` type copies for `p ∈ [0, 1]`. -/
theorem cStarOperatorMonotoneOnNonneg_rpow {p : ℝ} (hp : p ∈ Set.Icc 0 1) :
    CStarOperatorMonotoneOnNonneg.{uA, un} (fun t : ℝ => t ^ p) := by
  intro A _ _ _ n _ _ M hM N hN hMN
  change cfc (fun t : ℝ => t ^ p) M ≤ cfc (fun t : ℝ => t ^ p) N
  rw [← CFC.rpow_eq_cfc_real (a := M) (y := p) hM,
    ← CFC.rpow_eq_cfc_real (a := N) (y := p) hN]
  exact CFC.monotone_rpow (A := CStarMatrix n n A) hp hMN

/-- A real function is operator monotone on the strictly-positive cone of finite
`CStarMatrix` type copies if real CFC by that function preserves spectral order
on strictly-positive matrices. -/
def CStarOperatorMonotoneOnStrictlyPos (f : ℝ → ℝ) : Prop :=
  ∀ {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {n : Type un} [Fintype n] [DecidableEq n],
    MonotoneOn (fun M : CStarMatrix n n A => cfc f M)
      {M | IsStrictlyPositive M}

/-- The natural logarithm `Real.log` is operator monotone on the strictly-positive
cone of finite `CStarMatrix` type copies, via Mathlib's `CFC.log_monotoneOn`. -/
theorem cStarOperatorMonotoneOnStrictlyPos_log :
    CStarOperatorMonotoneOnStrictlyPos.{uA, un} Real.log := by
  intro A _ _ _ n _ _ M hM N hN hMN
  -- `CFC.log` unfolds to `cfc Real.log`; `CFC.log_monotoneOn` gives the conclusion.
  change cfc Real.log M ≤ cfc Real.log N
  exact CFC.log_monotoneOn (A := CStarMatrix n n A) hM hN hMN

/-- `Real.sqrt` is operator monotone on the nonnegative cone of finite
`CStarMatrix` type copies, as the `p = 1/2` instance of
`cStarOperatorMonotoneOnNonneg_rpow` via the unconditional identity
`Real.sqrt x = x ^ (1/2)`. -/
theorem cStarOperatorMonotoneOnNonneg_sqrt :
    CStarOperatorMonotoneOnNonneg.{uA, un} Real.sqrt := by
  intro A _ _ _ n _ _ M hM N hN hMN
  have hsqrt : (Real.sqrt : ℝ → ℝ) = fun t : ℝ => t ^ (1 / (2 : ℝ)) := by
    funext t; exact Real.sqrt_eq_rpow t
  change cfc Real.sqrt M ≤ cfc Real.sqrt N
  rw [hsqrt]
  exact cStarOperatorMonotoneOnNonneg_rpow.{uA, un}
    (by norm_num : (1 / (2 : ℝ)) ∈ Set.Icc (0 : ℝ) 1) hM hN hMN

/-! ### L2 layer: operator concavity on `CStarMatrix`

Mirror predicate of `CStarOperatorMonotoneOnNonneg` for operator concavity.
The full Löwner integral representation linking operator-concave with
operator-monotone is multi-month upstream Mathlib work and is NOT proved
here. This file currently records the predicate together with the two
trivial affine instances (constant, identity) so the L2 API has
non-vacuous content and a tested scaffold. Concrete instances such as
`Real.log` and `Real.rpow` for `p ∈ [0, 1]` are blocked on pinned Mathlib
(`80732f7660`, 2026-01-09), which carries only TODO comments — see
`Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/ExpLog/Order.lean`
("Show that the log is operator concave") and
`Mathlib/Analysis/SpecialFunctions/ContinuousFunctionalCalculus/Rpow/IntegralRepresentation.lean`
(the integral representation is described as "useful for showing rpow is
operator concave", but the operator-concavity lemma itself is not stated).
-/

/-- A real function is operator concave on the nonnegative cone of finite
`CStarMatrix` type copies if for all `t ∈ [0, 1]` and nonnegative `M N`,
the CFC values satisfy
`t • cfc f M + (1 - t) • cfc f N ≤ cfc f (t • M + (1 - t) • N)`.

Mirror of `CStarOperatorMonotoneOnNonneg`. Convex combinations of
nonnegative elements are nonnegative in a `StarOrderedRing`, so the
midpoint stays in the cone. -/
def CStarOperatorConcaveOnNonneg (f : ℝ → ℝ) : Prop :=
  ∀ {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {n : Type un} [Fintype n] [DecidableEq n]
    (M N : CStarMatrix n n A) (_hM : 0 ≤ M) (_hN : 0 ≤ N)
    (t : ℝ) (_ht : t ∈ Set.Icc (0:ℝ) 1),
    t • cfc f M + (1 - t) • cfc f N ≤ cfc f (t • M + (1 - t) • N)

/-- Constants are operator concave on the nonnegative cone of `CStarMatrix`
type copies (with equality).

Both sides reduce to `c • 1` after `cfc_const` and `t + (1 - t) = 1`. -/
theorem cStarOperatorConcaveOnNonneg_const (c : ℝ) :
    CStarOperatorConcaveOnNonneg.{uA, un} (fun _ => c) := by
  intro A _ _ _ n _ _ M N hM hN t ht
  -- Nonnegativity is preserved under nonneg-scalar combinations.
  have ht0 : (0 : ℝ) ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have h1mt : (0 : ℝ) ≤ 1 - t := by linarith
  have hsum : (0 : CStarMatrix n n A) ≤ t • M + (1 - t) • N :=
    add_nonneg (smul_nonneg ht0 hM) (smul_nonneg h1mt hN)
  rw [cfc_const (R := ℝ) c M, cfc_const (R := ℝ) c N,
      cfc_const (R := ℝ) c (t • M + (1 - t) • N), ← add_smul]
  have ht_sum : t + (1 - t) = 1 := by ring
  rw [ht_sum, one_smul]

/-- The identity is operator concave on the nonnegative cone of `CStarMatrix`
type copies (with equality — affine in `t`). -/
theorem cStarOperatorConcaveOnNonneg_id :
    CStarOperatorConcaveOnNonneg.{uA, un} id := by
  intro A _ _ _ n _ _ M N hM hN t ht
  have ht0 : (0 : ℝ) ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have h1mt : (0 : ℝ) ≤ 1 - t := by linarith
  have hsum : (0 : CStarMatrix n n A) ≤ t • M + (1 - t) • N :=
    add_nonneg (smul_nonneg ht0 hM) (smul_nonneg h1mt hN)
  rw [cfc_id (R := ℝ) M, cfc_id (R := ℝ) N,
      cfc_id (R := ℝ) (t • M + (1 - t) • N)]

end LTFP.MathlibExt.MatrixAnalysis
