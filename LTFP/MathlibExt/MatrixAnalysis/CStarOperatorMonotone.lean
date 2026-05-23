/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
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

/-- `Real.sqrt` is operator monotone on the nonnegative cone of every unital
C⋆-algebra, as the `p = 1/2` instance of
`cStarAlgebraOperatorMonotoneOnNonneg_rpow` via the unconditional identity
`Real.sqrt x = x ^ (1/2)`. -/
theorem cStarAlgebraOperatorMonotoneOnNonneg_sqrt :
    CStarAlgebraOperatorMonotoneOnNonneg.{uA} Real.sqrt := by
  intro A _ _ _ a ha b hb hab
  have hsqrt : (Real.sqrt : ℝ → ℝ) = fun t : ℝ => t ^ (1 / (2 : ℝ)) := by
    funext t; exact Real.sqrt_eq_rpow t
  change cfc Real.sqrt a ≤ cfc Real.sqrt b
  rw [hsqrt]
  exact cStarAlgebraOperatorMonotoneOnNonneg_rpow.{uA}
    (by norm_num : (1 / (2 : ℝ)) ∈ Set.Icc (0 : ℝ) 1) ha hb hab

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

/-- A real function is operator antitone on the strictly-positive cone of every
unital C⋆-algebra if real CFC by that function reverses spectral order there. -/
def CStarAlgebraOperatorAntitoneOnStrictlyPos (f : ℝ → ℝ) : Prop :=
  ∀ {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A],
    AntitoneOn (fun a : A => cfc f a) {a | IsStrictlyPositive a}

/-- Löwner inversion: `t ↦ t ^ (-1 : ℝ)` is operator antitone on the
strictly-positive cone of every unital C⋆-algebra. Classical result, lifted from
Mathlib's `CStarAlgebra.rpow_neg_one_le_rpow_neg_one`. -/
theorem cStarAlgebraOperatorAntitoneOnStrictlyPos_rpow_neg_one :
    CStarAlgebraOperatorAntitoneOnStrictlyPos.{uA} (fun t : ℝ => t ^ (-1 : ℝ)) := by
  intro A _ _ _ a ha b hb hab
  -- `AntitoneOn` flips: goal is `cfc f b ≤ cfc f a`.
  change cfc (fun t : ℝ => t ^ (-1 : ℝ)) b ≤ cfc (fun t : ℝ => t ^ (-1 : ℝ)) a
  rw [← CFC.rpow_eq_cfc_real (a := b) (y := -1) hb.nonneg,
    ← CFC.rpow_eq_cfc_real (a := a) (y := -1) ha.nonneg]
  exact CStarAlgebra.rpow_neg_one_le_rpow_neg_one (A := A) hab ha

/-- `t ↦ 1 - (1 + t)⁻¹` is operator monotone on the nonnegative cone of every
unital C⋆-algebra. Lifted from Mathlib's
`CFC.monotoneOn_one_sub_one_add_inv_real` (stated in `cfcₙ` form) via the
zero-at-zero bridge `cfcₙ_eq_cfc`: the function vanishes at `0` (since
`1 - (1 + 0)⁻¹ = 0`), and is continuous on the quasispectrum of any
nonnegative element (denominator `1 + t > 0` for `t ≥ 0`). -/
theorem cStarAlgebraOperatorMonotoneOnNonneg_one_sub_one_add_inv :
    CStarAlgebraOperatorMonotoneOnNonneg.{uA} (fun t : ℝ => 1 - (1 + t)⁻¹) := by
  intro A _ _ _ a (ha : 0 ≤ a) b (hb : 0 ≤ b) hab
  change cfc (fun t : ℝ => 1 - (1 + t)⁻¹) a ≤ cfc (fun t : ℝ => 1 - (1 + t)⁻¹) b
  have hf0 : (fun t : ℝ => 1 - (1 + t)⁻¹) 0 = 0 := by norm_num
  have hcont_a : ContinuousOn (fun t : ℝ => 1 - (1 + t)⁻¹) (quasispectrum ℝ a) := by
    refine continuousOn_const.sub ?_
    refine (continuousOn_const.add continuousOn_id).inv₀ ?_
    intro x hx
    have hx_nn : 0 ≤ x := quasispectrum_nonneg_of_nonneg a ha x hx
    simp only [id]
    linarith
  have hcont_b : ContinuousOn (fun t : ℝ => 1 - (1 + t)⁻¹) (quasispectrum ℝ b) := by
    refine continuousOn_const.sub ?_
    refine (continuousOn_const.add continuousOn_id).inv₀ ?_
    intro x hx
    have hx_nn : 0 ≤ x := quasispectrum_nonneg_of_nonneg b hb x hx
    simp only [id]
    linarith
  rw [← cfcₙ_eq_cfc (a := a) (f := fun t : ℝ => 1 - (1 + t)⁻¹) hcont_a hf0,
      ← cfcₙ_eq_cfc (a := b) (f := fun t : ℝ => 1 - (1 + t)⁻¹) hcont_b hf0]
  exact CFC.monotoneOn_one_sub_one_add_inv_real (A := A) ha hb hab

/-- `t ↦ -Real.log t` is operator antitone on the strictly-positive cone of every
unital C⋆-algebra, via negation of `cStarAlgebraOperatorMonotoneOnStrictlyPos_log`:
`cfc (fun t => -Real.log t) x = -cfc Real.log x` by `cfc_neg`, and monotonicity of
`Real.log` then gives the reversed inequality after `neg_le_neg`. -/
theorem cStarAlgebraOperatorAntitoneOnStrictlyPos_neg_log :
    CStarAlgebraOperatorAntitoneOnStrictlyPos.{uA} (fun t : ℝ => -Real.log t) := by
  intro A _ _ _ a ha b hb hab
  -- `AntitoneOn` flips: goal is `cfc f b ≤ cfc f a`.
  change cfc (fun t : ℝ => -Real.log t) b ≤ cfc (fun t : ℝ => -Real.log t) a
  rw [cfc_neg (R := ℝ) Real.log b, cfc_neg (R := ℝ) Real.log a]
  exact neg_le_neg
    (cStarAlgebraOperatorMonotoneOnStrictlyPos_log.{uA} (A := A) ha hb hab)

/-! #### Algebraic combinators at the CStarAlgebra level

Basic compositional combinators on the CStarAlgebra-level operator-monotonicity
predicates, mirroring the analogous combinators on the universal
`OperatorMonotone` predicate (over `Matrix n n 𝕜`). These allow downstream
callers to chain pointwise CFC lemmas without reproving the cone preservation
each time.
-/

/-- The identity function is operator monotone on the nonnegative cone of every
unital C⋆-algebra: `cfc id` reduces to the identity by `cfc_id'`, so the goal
is just `a ≤ b`. -/
theorem cStarAlgebraOperatorMonotoneOnNonneg_id :
    CStarAlgebraOperatorMonotoneOnNonneg.{uA} (fun t : ℝ => t) := by
  intro A _ _ _ a ha b hb hab
  change cfc (fun t : ℝ => t) a ≤ cfc (fun t : ℝ => t) b
  rw [cfc_id' ℝ a, cfc_id' ℝ b]
  exact hab

/-- A constant function is (trivially) operator monotone on the nonnegative cone
of every unital C⋆-algebra: `cfc (fun _ => c) a = algebraMap ℝ A c` by
`cfc_const`, and both sides equal that same algebra-map image, so the inequality
holds reflexively. -/
theorem cStarAlgebraOperatorMonotoneOnNonneg_const (c : ℝ) :
    CStarAlgebraOperatorMonotoneOnNonneg.{uA} (fun _ : ℝ => c) := by
  intro A _ _ _ a ha b hb _
  change cfc (fun _ : ℝ => c) a ≤ cfc (fun _ : ℝ => c) b
  rw [cfc_const (R := ℝ) c a, cfc_const (R := ℝ) c b]

/-- Sum of two operator-monotone functions (on the nonnegative cone of every
unital C⋆-algebra) is operator monotone. Uses `cfc_add` to split the CFC, then
adds the two pointwise inequalities. Requires continuity of both summands on the
spectrum of each element, auto-discharged by `cfc_cont_tac` when the assumption
is supplied. -/
theorem CStarAlgebraOperatorMonotoneOnNonneg.add {f g : ℝ → ℝ}
    (hf : CStarAlgebraOperatorMonotoneOnNonneg.{uA} f)
    (hg : CStarAlgebraOperatorMonotoneOnNonneg.{uA} g)
    (hf_cont : Continuous f) (hg_cont : Continuous g) :
    CStarAlgebraOperatorMonotoneOnNonneg.{uA} (fun t => f t + g t) := by
  intro A _ _ _ a ha b hb hab
  change cfc (fun t => f t + g t) a ≤ cfc (fun t => f t + g t) b
  rw [cfc_add (R := ℝ) f g (a := a) hf_cont.continuousOn hg_cont.continuousOn,
      cfc_add (R := ℝ) f g (a := b) hf_cont.continuousOn hg_cont.continuousOn]
  exact add_le_add (hf ha hb hab) (hg ha hb hab)

/-- Nonneg scalar multiple of an operator-monotone function (on the nonnegative
cone of every unital C⋆-algebra) is operator monotone. Uses `cfc_const_mul` to
factor the scalar through the CFC, then `smul_le_smul_of_nonneg_left` to
preserve order. -/
theorem CStarAlgebraOperatorMonotoneOnNonneg.const_smul {f : ℝ → ℝ}
    (hf : CStarAlgebraOperatorMonotoneOnNonneg.{uA} f)
    (hf_cont : Continuous f) {c : ℝ} (hc : 0 ≤ c) :
    CStarAlgebraOperatorMonotoneOnNonneg.{uA} (fun t => c * f t) := by
  intro A _ _ _ a ha b hb hab
  change cfc (fun t => c * f t) a ≤ cfc (fun t => c * f t) b
  rw [cfc_const_mul (R := ℝ) c f a hf_cont.continuousOn,
      cfc_const_mul (R := ℝ) c f b hf_cont.continuousOn]
  exact smul_le_smul_of_nonneg_left (hf ha hb hab) hc

/-- Negation of an operator-monotone function (on the strictly-positive cone of
every unital C⋆-algebra) is operator antitone. Mirrors the
`cStarAlgebraOperatorAntitoneOnStrictlyPos_neg_log` construction at the
combinator level. -/
theorem CStarAlgebraOperatorMonotoneOnStrictlyPos.neg {f : ℝ → ℝ}
    (hf : CStarAlgebraOperatorMonotoneOnStrictlyPos.{uA} f) :
    CStarAlgebraOperatorAntitoneOnStrictlyPos.{uA} (fun t => -f t) := by
  intro A _ _ _ a ha b hb hab
  -- `AntitoneOn` flips: goal is `cfc (-f) b ≤ cfc (-f) a`.
  change cfc (fun t => -f t) b ≤ cfc (fun t => -f t) a
  rw [cfc_neg (R := ℝ) f b, cfc_neg (R := ℝ) f a]
  exact neg_le_neg (hf ha hb hab)

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

/-- A real function is operator antitone on the strictly-positive cone of finite
`CStarMatrix` type copies if real CFC by that function reverses spectral order
on strictly-positive matrices. -/
def CStarOperatorAntitoneOnStrictlyPos (f : ℝ → ℝ) : Prop :=
  ∀ {A : Type uA} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    {n : Type un} [Fintype n] [DecidableEq n],
    AntitoneOn (fun M : CStarMatrix n n A => cfc f M)
      {M | IsStrictlyPositive M}

/-- Löwner inversion on finite `CStarMatrix`: `t ↦ t ^ (-1 : ℝ)` is operator
antitone on the strictly-positive cone, via
`CStarAlgebra.rpow_neg_one_le_rpow_neg_one`. -/
theorem cStarOperatorAntitoneOnStrictlyPos_rpow_neg_one :
    CStarOperatorAntitoneOnStrictlyPos.{uA, un} (fun t : ℝ => t ^ (-1 : ℝ)) := by
  intro A _ _ _ n _ _ M hM N hN hMN
  -- `AntitoneOn` flips: goal is `cfc f N ≤ cfc f M`.
  change cfc (fun t : ℝ => t ^ (-1 : ℝ)) N ≤ cfc (fun t : ℝ => t ^ (-1 : ℝ)) M
  rw [← CFC.rpow_eq_cfc_real (a := N) (y := -1) hN.nonneg,
    ← CFC.rpow_eq_cfc_real (a := M) (y := -1) hM.nonneg]
  exact CStarAlgebra.rpow_neg_one_le_rpow_neg_one (A := CStarMatrix n n A) hMN hM

/-- Finite-`CStarMatrix` analog of
`cStarAlgebraOperatorMonotoneOnNonneg_one_sub_one_add_inv`: `t ↦ 1 - (1 + t)⁻¹`
is operator monotone on the nonnegative cone of `CStarMatrix n n A`, via the
`cfcₙ_eq_cfc` zero-at-zero bridge from `CFC.monotoneOn_one_sub_one_add_inv_real`. -/
theorem cStarOperatorMonotoneOnNonneg_one_sub_one_add_inv :
    CStarOperatorMonotoneOnNonneg.{uA, un} (fun t : ℝ => 1 - (1 + t)⁻¹) := by
  intro A _ _ _ n _ _ M (hM : 0 ≤ M) N (hN : 0 ≤ N) hMN
  change cfc (fun t : ℝ => 1 - (1 + t)⁻¹) M ≤ cfc (fun t : ℝ => 1 - (1 + t)⁻¹) N
  have hf0 : (fun t : ℝ => 1 - (1 + t)⁻¹) 0 = 0 := by norm_num
  have hcont_M : ContinuousOn (fun t : ℝ => 1 - (1 + t)⁻¹) (quasispectrum ℝ M) := by
    refine continuousOn_const.sub ?_
    refine (continuousOn_const.add continuousOn_id).inv₀ ?_
    intro x hx
    have hx_nn : 0 ≤ x := quasispectrum_nonneg_of_nonneg M hM x hx
    simp only [id]
    linarith
  have hcont_N : ContinuousOn (fun t : ℝ => 1 - (1 + t)⁻¹) (quasispectrum ℝ N) := by
    refine continuousOn_const.sub ?_
    refine (continuousOn_const.add continuousOn_id).inv₀ ?_
    intro x hx
    have hx_nn : 0 ≤ x := quasispectrum_nonneg_of_nonneg N hN x hx
    simp only [id]
    linarith
  rw [← cfcₙ_eq_cfc (a := M) (f := fun t : ℝ => 1 - (1 + t)⁻¹) hcont_M hf0,
      ← cfcₙ_eq_cfc (a := N) (f := fun t : ℝ => 1 - (1 + t)⁻¹) hcont_N hf0]
  exact CFC.monotoneOn_one_sub_one_add_inv_real (A := CStarMatrix n n A) hM hN hMN

/-- Finite-`CStarMatrix` analog of
`cStarAlgebraOperatorAntitoneOnStrictlyPos_neg_log`: `t ↦ -Real.log t` is operator
antitone on the strictly-positive cone of `CStarMatrix n n A`, via `cfc_neg`
together with `cStarOperatorMonotoneOnStrictlyPos_log`. -/
theorem cStarOperatorAntitoneOnStrictlyPos_neg_log :
    CStarOperatorAntitoneOnStrictlyPos.{uA, un} (fun t : ℝ => -Real.log t) := by
  intro A _ _ _ n _ _ M hM N hN hMN
  -- `AntitoneOn` flips: goal is `cfc f N ≤ cfc f M`.
  change cfc (fun t : ℝ => -Real.log t) N ≤ cfc (fun t : ℝ => -Real.log t) M
  rw [cfc_neg (R := ℝ) Real.log N, cfc_neg (R := ℝ) Real.log M]
  exact neg_le_neg
    (cStarOperatorMonotoneOnStrictlyPos_log.{uA, un} (A := A) (n := n) hM hN hMN)

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
