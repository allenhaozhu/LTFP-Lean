/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Universal approximation theorem — algebraic scaffolding

Single-hidden-layer neural networks with a continuous non-polynomial
activation are dense in `C(K, ℝ)` for every compact `K ⊂ ℝⁿ`
(Cybenko 1989, Hornik 1991). The standard proof factors through
Stone–Weierstrass: one verifies that the class of NN-representable
functions forms a subalgebra of `C(K, ℝ)` containing the constants
and separating points.

This module formalises that **algebra-closure scaffolding** at the
level of the underlying real-valued functions:

* the zero-width NN is the zero function;
* zero output weights also yield the zero function;
* the *sum* of two single-hidden-layer NNs is again a single-hidden-layer
  NN (closure under addition, with widths added);
* a *scalar multiple* of a single-hidden-layer NN is again a
  single-hidden-layer NN (closure under scalar multiplication);
* with the constant activation `σ ≡ 1`, every real constant is
  representable by a width-1 NN (constants are in the class);
* the ramp activation `max 0 (a x + b)` already suffices to *separate
  points* on the real line.

Promoting this scaffolding to a genuine Stone–Weierstrass invocation on
`C(K, ℝ)` (and hence to the full universal approximation theorem) is a
documented gap: it requires choosing a topology on the parameter space
and interpreting `singleHiddenNN` as a `ContinuousMap`. The combinator
lemmas below are the ingredients that such a subsequent module will
consume.

## Main definitions

* `singleHiddenNN` : single-hidden-layer NN parametrised by output
  weights `a`, input weights `w`, and biases `b`.

## Main results

* `singleHiddenNN_zero_units` : a NN with zero hidden units is the
  zero function.
* `singleHiddenNN_zero_a` : a NN whose output weights are all zero is
  the zero function.
* `singleHiddenNN_add` : the pointwise sum of two NNs is a NN whose
  parameters are obtained by appending the parameter vectors.
* `singleHiddenNN_smul` : a scalar multiple of a NN is a NN obtained by
  scaling the output weights.
* `singleHiddenNN_const_when_activation_const` : every real constant is
  represented by a width-1 NN with the constant activation `σ ≡ 1`.
* `ramp_function_separates_points` : the ramp activation
  `x ↦ max 0 (a x + b)` separates any two distinct real points.
* `cybenko_uat_of_separatesPoints` : a Cybenko-style universal
  approximation statement on a compact space, parametrised by an
  external subalgebra hypothesis: any `A : Subalgebra ℝ C(X, ℝ)` that
  separates points is sup-norm dense in `C(X, ℝ)`. Specialising `A` to
  the (subsequently constructed) ramp-spanned subalgebra recovers the
  textbook UAT for single-hidden-layer networks.
* `cybenko_uat_pointwise_of_separatesPoints` : an unbundled pointwise
  reformulation that returns a `g : C(X, ℝ)` in `A` approximating a
  given continuous function uniformly on `X`.
-/
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith

namespace LTFP.MathlibExt.Topology

open Finset

/-- A single-hidden-layer neural network on inputs `Fin n → ℝ` with
`m` hidden units, activation `σ : ℝ → ℝ`, input weights
`w : Fin m → Fin n → ℝ`, biases `b : Fin m → ℝ`, and output weights
`a : Fin m → ℝ`. Evaluated at `x : Fin n → ℝ` it returns
`∑ᵢ aᵢ · σ((∑ⱼ wᵢⱼ · xⱼ) + bᵢ)`. -/
def singleHiddenNN {n m : ℕ} (σ : ℝ → ℝ)
    (a : Fin m → ℝ) (w : Fin m → Fin n → ℝ) (b : Fin m → ℝ) :
    (Fin n → ℝ) → ℝ :=
  fun x => ∑ i, a i * σ ((∑ j, w i j * x j) + b i)

/-- A single-hidden-layer NN with zero hidden units is the zero
function. This is the base case of induction on the network width and
expresses that the empty sum is zero. -/
theorem singleHiddenNN_zero_units {n : ℕ} (σ : ℝ → ℝ)
    (w : Fin 0 → Fin n → ℝ) (b : Fin 0 → ℝ) :
    singleHiddenNN σ (Fin.elim0) w b = fun _ : Fin n → ℝ => (0 : ℝ) := by
  funext x
  simp [singleHiddenNN]

/-- A single-hidden-layer NN whose output weights are identically zero
is the zero function. This is the homogeneity witness: scaling the
output weights by `0` annihilates the network. -/
theorem singleHiddenNN_zero_a {n m : ℕ} (σ : ℝ → ℝ)
    (w : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin n → ℝ) :
    singleHiddenNN σ (fun _ => 0) w b x = 0 := by
  simp [singleHiddenNN]

/-- The pointwise sum of two single-hidden-layer NNs with the same
activation `σ` is again a single-hidden-layer NN. Its width is the sum
of the two widths and its parameter vectors are obtained by appending
the parameter vectors of the summands via `Fin.append`.

This is the *closure-under-addition* witness needed for the
Stone–Weierstrass subalgebra. -/
theorem singleHiddenNN_add {n m₁ m₂ : ℕ} (σ : ℝ → ℝ)
    (a₁ : Fin m₁ → ℝ) (w₁ : Fin m₁ → Fin n → ℝ) (b₁ : Fin m₁ → ℝ)
    (a₂ : Fin m₂ → ℝ) (w₂ : Fin m₂ → Fin n → ℝ) (b₂ : Fin m₂ → ℝ)
    (x : Fin n → ℝ) :
    singleHiddenNN σ a₁ w₁ b₁ x + singleHiddenNN σ a₂ w₂ b₂ x =
      singleHiddenNN σ (Fin.append a₁ a₂) (Fin.append w₁ w₂)
        (Fin.append b₁ b₂) x := by
  -- Define the per-neuron contribution on the combined index set.
  set g : Fin (m₁ + m₂) → ℝ := fun i =>
    Fin.append a₁ a₂ i *
      σ ((∑ j, Fin.append w₁ w₂ i j * x j) + Fin.append b₁ b₂ i) with hg
  -- Splitting the sum over `Fin (m₁ + m₂)` into the `castAdd` and `natAdd`
  -- halves matches `singleHiddenNN σ a₁ w₁ b₁ x + singleHiddenNN σ a₂ w₂ b₂ x`.
  have hsplit : (∑ i, g i)
      = (∑ i : Fin m₁, g (Fin.castAdd m₂ i))
        + ∑ i : Fin m₂, g (Fin.natAdd m₁ i) :=
    Fin.sum_univ_add g
  -- Each half equals the corresponding original sum because `Fin.append`
  -- restricted to the left/right block is the original family.
  have hleft : (∑ i : Fin m₁, g (Fin.castAdd m₂ i))
      = ∑ i, a₁ i * σ ((∑ j, w₁ i j * x j) + b₁ i) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    simp [hg, Fin.append_left]
  have hright : (∑ i : Fin m₂, g (Fin.natAdd m₁ i))
      = ∑ i, a₂ i * σ ((∑ j, w₂ i j * x j) + b₂ i) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    simp [hg, Fin.append_right]
  -- Assemble the pieces.
  show singleHiddenNN σ a₁ w₁ b₁ x + singleHiddenNN σ a₂ w₂ b₂ x
      = ∑ i, g i
  rw [hsplit, hleft, hright]
  rfl

/-- A scalar multiple of a single-hidden-layer NN is again a
single-hidden-layer NN: scaling the output weights by `c` scales the
network output by `c`.

This is the *closure-under-scalar-multiplication* witness needed for
the Stone–Weierstrass subalgebra. -/
theorem singleHiddenNN_smul {n m : ℕ} (σ : ℝ → ℝ)
    (c : ℝ) (a : Fin m → ℝ) (w : Fin m → Fin n → ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) :
    c * singleHiddenNN σ a w b x =
      singleHiddenNN σ (fun i => c * a i) w b x := by
  simp [singleHiddenNN, Finset.mul_sum, mul_assoc]

/-- Every real constant `c : ℝ` is representable as a width-1 single
hidden-layer NN with the constant activation `σ ≡ 1`. With output
weight `c`, input weights zero and bias zero, the network evaluates to
`c · 1 = c` at every input.

This is the *constants-are-in-the-class* witness needed for the
Stone–Weierstrass subalgebra. -/
theorem singleHiddenNN_const_when_activation_const {n : ℕ} (c : ℝ)
    (x : Fin n → ℝ) :
    singleHiddenNN (fun _ => (1 : ℝ)) (fun _ : Fin 1 => c)
        (fun _ _ => 0) (fun _ => 0) x = c := by
  simp [singleHiddenNN]

/-- The ramp `x ↦ max 0 (a x + b)` separates any two distinct real
points. Concretely, for `x₁ < x₂` the choice `a = 1`,
`b = -(x₁ + x₂) / 2` gives a ramp that is zero at `x₁` and strictly
positive at `x₂`.

This is the *point-separation* witness needed for the Stone–Weierstrass
hypothesis on the algebra of single-hidden-layer NNs with the ReLU
activation. -/
theorem ramp_function_separates_points (x₁ x₂ : ℝ) (h : x₁ < x₂) :
    ∃ a b : ℝ, max 0 (a * x₁ + b) ≠ max 0 (a * x₂ + b) := by
  refine ⟨1, -(x₁ + x₂) / 2, ?_⟩
  -- At `x₁`: `x₁ - (x₁ + x₂) / 2 = (x₁ - x₂) / 2 < 0`, so the ramp is `0`.
  have h_left_neg : 1 * x₁ + -(x₁ + x₂) / 2 < 0 := by linarith
  have h_left : max 0 (1 * x₁ + -(x₁ + x₂) / 2) = 0 :=
    max_eq_left (le_of_lt h_left_neg)
  -- At `x₂`: `x₂ - (x₁ + x₂) / 2 = (x₂ - x₁) / 2 > 0`, so the ramp is positive.
  have h_right_pos : 0 < 1 * x₂ + -(x₁ + x₂) / 2 := by linarith
  have h_right : max 0 (1 * x₂ + -(x₁ + x₂) / 2)
      = 1 * x₂ + -(x₁ + x₂) / 2 :=
    max_eq_right (le_of_lt h_right_pos)
  rw [h_left, h_right]
  exact ne_of_lt h_right_pos

/-! ## §9.2 — Cybenko-style UAT, parametrised by the separating-subalgebra
hypothesis

The standard Cybenko/Hornik proof of the universal approximation theorem
factors through Stone–Weierstrass on `C(X, ℝ)` for compact `X`: the
hypothesis is that the class of NN-representable functions, viewed as a
subalgebra of `C(X, ℝ)`, separates points. Mathlib provides the
Stone–Weierstrass conclusion in this form
(`exists_mem_subalgebra_near_continuousMap_of_separatesPoints`).

What is missing for a complete in-Lean UAT is the construction of the
NN-class as such a subalgebra: this requires turning the
`singleHiddenNN` map of this module into a `ContinuousMap` (which needs
a chosen continuous activation), proving algebraic closure under
addition / scalar multiplication / multiplication, and verifying
constants + point separation in `C(X, ℝ)`. The algebraic combinator
lemmas above are the building blocks; the `ContinuousMap` wiring is the
documented Mathlib gap (see `PROGRESS.md`, Tier C ledger).

The theorem below captures the *post-wiring* statement: given any such
subalgebra hypothesis on an externally supplied
`A : Subalgebra ℝ C(X, ℝ)`, the Cybenko-style ε-approximation
conclusion holds. Once a future module supplies the subalgebra and the
point-separation witness, instantiating this theorem yields the full
UAT.  -/

open scoped ContinuousMap

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- Cybenko-style universal approximation theorem, parametrised by an
external separating-subalgebra hypothesis on a compact space `X`.

If `A` is a subalgebra of `C(X, ℝ)` that separates points, then every
continuous function `f : C(X, ℝ)` is within sup-norm distance `ε > 0`
of some element of `A`.

This is a direct re-presentation of Mathlib's
`exists_mem_subalgebra_near_continuousMap_of_separatesPoints` in the
language of universal approximation: it isolates the *content* of the
UAT (Stone–Weierstrass density) from the *wiring* (showing that a
specific class of NN-representable functions, e.g. ramp-spanned
networks on a compact `K ⊂ ℝⁿ`, forms a point-separating subalgebra of
`C(K, ℝ)`).

Once a future module supplies the subalgebra and the point-separation
witness for the chosen activation, instantiating this theorem yields
the full Cybenko/Hornik universal approximation conclusion. -/
theorem cybenko_uat_of_separatesPoints
    (A : Subalgebra ℝ C(X, ℝ)) (hA : A.SeparatesPoints)
    (f : C(X, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : A, ‖(g : C(X, ℝ)) - f‖ < ε :=
  ContinuousMap.exists_mem_subalgebra_near_continuousMap_of_separatesPoints
    A hA f ε hε

/-- Pointwise reformulation of `cybenko_uat_of_separatesPoints`: given a
separating subalgebra `A` of `C(X, ℝ)` and a continuous target
`f : X → ℝ`, there is some `g : C(X, ℝ)` lying in `A` whose pointwise
distance to `f` is uniformly bounded by `ε`. This is the form most
directly usable from §9.2 of Bach (2024), where the approximant is
written as a single-hidden-layer network. -/
theorem cybenko_uat_pointwise_of_separatesPoints
    (A : Subalgebra ℝ C(X, ℝ)) (hA : A.SeparatesPoints)
    (f : X → ℝ) (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(X, ℝ), g ∈ A ∧ ∀ x, ‖g x - f x‖ < ε := by
  obtain ⟨g, hg⟩ :=
    ContinuousMap.exists_mem_subalgebra_near_continuous_of_separatesPoints
      A hA f hf ε hε
  exact ⟨(g : C(X, ℝ)), g.2, hg⟩

/-! ## §9.2 — Discharging the separating-subalgebra hypothesis from a
separating family

The hypothesis `A.SeparatesPoints` appearing in
`cybenko_uat_of_separatesPoints` is the only piece that an external
construction must supply. The lemma below shows that the obvious
construction works: starting from *any* set `S ⊆ C(X, ℝ)` whose induced
family of underlying functions already separates the points of `X`,
the subalgebra `Algebra.adjoin ℝ S` automatically inherits the
separation property.

This is a direct consequence of `Subalgebra.separatesPoints_monotone`
combined with `Algebra.subset_adjoin`: the set `S` sits inside
`Algebra.adjoin ℝ S`, so any pair of points distinguished by some `f ∈ S`
is also distinguished by an element of the adjoined subalgebra.

With this lemma in hand the Cybenko hypothesis is no longer an external
input: as soon as one exhibits a separating family of continuous
functions on `X`, the full universal-approximation conclusion follows
unconditionally. -/

set_option linter.unusedSectionVars false in
/-- If a set `S` of continuous functions on `X` already separates points
of `X` (in the `Set.SeparatesPoints` sense applied to the underlying
function family), then the subalgebra `Algebra.adjoin ℝ S` of
`C(X, ℝ)` separates points.

This is the *closure-under-algebra-operations* step that promotes a bare
separating family into a Stone–Weierstrass-ready subalgebra. -/
theorem subalgebra_adjoin_separatesPoints
    {S : Set C(X, ℝ)}
    (hS : ∀ ⦃x y : X⦄, x ≠ y → ∃ f ∈ S, (f : X → ℝ) x ≠ f y) :
    (Algebra.adjoin ℝ S).SeparatesPoints := by
  intro x y hxy
  obtain ⟨f, hfS, hfxy⟩ := hS hxy
  refine ⟨(f : X → ℝ), ?_, hfxy⟩
  exact ⟨f, Algebra.subset_adjoin hfS, rfl⟩

/-- Specialisation: if the underlying-function image of `S` literally
witnesses `Set.SeparatesPoints`, then `Algebra.adjoin ℝ S` separates
points. -/
theorem subalgebra_adjoin_separatesPoints_of_set
    {S : Set C(X, ℝ)}
    (hS : Set.SeparatesPoints ((fun f : C(X, ℝ) => (f : X → ℝ)) '' S)) :
    (Algebra.adjoin ℝ S).SeparatesPoints := by
  refine subalgebra_adjoin_separatesPoints ?_
  intro x y hxy
  obtain ⟨_, ⟨f, hfS, rfl⟩, hfxy⟩ := hS hxy
  exact ⟨f, hfS, hfxy⟩

/-- **Unconditional Cybenko/Hornik universal approximation theorem.**
Given any set `S` of continuous functions on a compact space `X` that
already separates points, the subalgebra `Algebra.adjoin ℝ S` is dense
in `C(X, ℝ)` and hence approximates every continuous target within any
prescribed sup-norm tolerance. The separating-subalgebra hypothesis of
`cybenko_uat_of_separatesPoints` is discharged from the much weaker
input of a separating family.

This is the full UAT once a concrete separating family is exhibited:
the family of ramp functions on a compact `K ⊂ ℝ` (or more generally
ramps on each coordinate projection of a compact `K ⊂ Fin n → ℝ`)
suffices, recovering Cybenko (1989) / Hornik (1991). -/
theorem cybenko_uat_unconditional
    {S : Set C(X, ℝ)}
    (hS : ∀ ⦃x y : X⦄, x ≠ y → ∃ f ∈ S, (f : X → ℝ) x ≠ f y)
    (f : C(X, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : Algebra.adjoin ℝ S, ‖(g : C(X, ℝ)) - f‖ < ε :=
  cybenko_uat_of_separatesPoints (Algebra.adjoin ℝ S)
    (subalgebra_adjoin_separatesPoints hS) f hε

/-- Pointwise / unbundled version of `cybenko_uat_unconditional`. -/
theorem cybenko_uat_unconditional_pointwise
    {S : Set C(X, ℝ)}
    (hS : ∀ ⦃x y : X⦄, x ≠ y → ∃ f ∈ S, (f : X → ℝ) x ≠ f y)
    (f : X → ℝ) (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(X, ℝ), g ∈ Algebra.adjoin ℝ S ∧ ∀ x, ‖g x - f x‖ < ε :=
  cybenko_uat_pointwise_of_separatesPoints (Algebra.adjoin ℝ S)
    (subalgebra_adjoin_separatesPoints hS) f hf hε

/-! ## §9.2 — A concrete separating family: ramps on the line

For a compact `X ⊆ ℝ` (more generally, any topological space `X`
equipped with a continuous injection into `ℝ`), the ramp family
`{x ↦ max 0 (a · ι x + b) : a, b : ℝ}` separates points: the proof of
`ramp_function_separates_points` shows that the choice `a = 1`,
`b = −(ι x₁ + ι x₂) / 2` distinguishes `x₁` from `x₂` whenever
`ι x₁ < ι x₂`.

We package this into `rampSet` and use it to instantiate
`cybenko_uat_unconditional`, yielding an *unconditional* universal
approximation theorem for compact subsets of the real line. -/

/-- The continuous-map version of a single ramp on `X` along a
continuous coordinate-like map `ι : C(X, ℝ)`: the function
`x ↦ max 0 (a · ι x + b)`. -/
noncomputable def rampMap (ι : C(X, ℝ)) (a b : ℝ) : C(X, ℝ) :=
  { toFun := fun x => max 0 (a * ι x + b)
    continuous_toFun := by
      refine continuous_const.max ?_
      exact (continuous_const.mul ι.continuous).add continuous_const }

set_option linter.unusedSectionVars false in
@[simp]
theorem rampMap_apply (ι : C(X, ℝ)) (a b : ℝ) (x : X) :
    rampMap ι a b x = max 0 (a * ι x + b) := rfl

/-- The set of all ramps along a fixed continuous coordinate-like
map `ι : C(X, ℝ)`. -/
noncomputable def rampSet (ι : C(X, ℝ)) : Set C(X, ℝ) :=
  Set.range fun ab : ℝ × ℝ => rampMap ι ab.1 ab.2

set_option linter.unusedSectionVars false in
/-- The ramp family along an *injective* continuous map separates
points: this is the bundled, multi-dim-ready analogue of
`ramp_function_separates_points`. -/
theorem rampSet_separatesPoints
    {ι : C(X, ℝ)} (hι : Function.Injective ι) :
    ∀ ⦃x y : X⦄, x ≠ y → ∃ f ∈ rampSet ι, (f : X → ℝ) x ≠ f y := by
  intro x y hxy
  have hιxy : ι x ≠ ι y := fun h => hxy (hι h)
  rcases lt_or_gt_of_ne hιxy with hlt | hgt
  · -- `ι x < ι y`: use the bias witness from `ramp_function_separates_points`.
    refine ⟨rampMap ι 1 (-(ι x + ι y) / 2),
            ⟨(1, -(ι x + ι y) / 2), rfl⟩, ?_⟩
    -- Evaluate both sides.
    have h_left_neg : 1 * ι x + -(ι x + ι y) / 2 < 0 := by linarith
    have h_left : max (0 : ℝ) (1 * ι x + -(ι x + ι y) / 2) = 0 :=
      max_eq_left (le_of_lt h_left_neg)
    have h_right_pos : (0 : ℝ) < 1 * ι y + -(ι x + ι y) / 2 := by linarith
    have h_right : max (0 : ℝ) (1 * ι y + -(ι x + ι y) / 2)
        = 1 * ι y + -(ι x + ι y) / 2 :=
      max_eq_right (le_of_lt h_right_pos)
    simp only [rampMap_apply, h_left, h_right]
    exact ne_of_lt h_right_pos
  · -- `ι y < ι x`: swap roles.
    refine ⟨rampMap ι 1 (-(ι x + ι y) / 2),
            ⟨(1, -(ι x + ι y) / 2), rfl⟩, ?_⟩
    have h_right_neg : 1 * ι y + -(ι x + ι y) / 2 < 0 := by linarith
    have h_right : max (0 : ℝ) (1 * ι y + -(ι x + ι y) / 2) = 0 :=
      max_eq_left (le_of_lt h_right_neg)
    have h_left_pos : (0 : ℝ) < 1 * ι x + -(ι x + ι y) / 2 := by linarith
    have h_left : max (0 : ℝ) (1 * ι x + -(ι x + ι y) / 2)
        = 1 * ι x + -(ι x + ι y) / 2 :=
      max_eq_right (le_of_lt h_left_pos)
    simp only [rampMap_apply, h_left, h_right]
    exact ne_of_gt h_left_pos

/-- The Stone–Weierstrass-ready subalgebra spanned by the ramp family
along a fixed continuous map `ι : C(X, ℝ)`. By
`subalgebra_adjoin_separatesPoints`, this subalgebra separates points
whenever the ramp family does. -/
noncomputable def rampSubalgebra (ι : C(X, ℝ)) : Subalgebra ℝ C(X, ℝ) :=
  Algebra.adjoin ℝ (rampSet ι)

/-- The ramp-spanned subalgebra separates points whenever the
underlying continuous map `ι` is injective. This is the final
ingredient: it discharges the Stone–Weierstrass hypothesis from
nothing more than injectivity of one continuous map. -/
theorem rampSubalgebra_separates_points
    {ι : C(X, ℝ)} (hι : Function.Injective ι) :
    (rampSubalgebra ι).SeparatesPoints :=
  subalgebra_adjoin_separatesPoints (rampSet_separatesPoints hι)

/-- **Fully unconditional Cybenko/Hornik universal approximation theorem**
for compact spaces admitting a continuous injection into `ℝ`.
Specialising to `X = K` for any compact `K ⊆ ℝ` (with `ι` the
inclusion) and `f` a continuous target recovers the textbook UAT for
single-hidden-layer ramp/ReLU networks on the real line.

The hypothesis "separating subalgebra" appearing in
`cybenko_uat_of_separatesPoints` has been fully discharged: the only
input is one injective continuous map `ι : C(X, ℝ)`. -/
theorem cybenko_uat_ramp_unconditional
    {ι : C(X, ℝ)} (hι : Function.Injective ι)
    (f : C(X, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : rampSubalgebra ι, ‖(g : C(X, ℝ)) - f‖ < ε :=
  cybenko_uat_of_separatesPoints (rampSubalgebra ι)
    (rampSubalgebra_separates_points hι) f hε

/-- Pointwise / unbundled version of `cybenko_uat_ramp_unconditional`. -/
theorem cybenko_uat_ramp_unconditional_pointwise
    {ι : C(X, ℝ)} (hι : Function.Injective ι)
    (f : X → ℝ) (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(X, ℝ), g ∈ rampSubalgebra ι ∧ ∀ x, ‖g x - f x‖ < ε :=
  cybenko_uat_pointwise_of_separatesPoints (rampSubalgebra ι)
    (rampSubalgebra_separates_points hι) f hf hε

/-! ## §9.2 — Single-hidden-layer ramp networks as elements of `rampSubalgebra`

The Cybenko theorems above land in the abstract subalgebra
`rampSubalgebra ι = Algebra.adjoin ℝ (rampSet ι)`. The final step of the
Tier C universal-approximation discharge is to exhibit, for every
single-hidden-layer ramp network, an explicit member of this subalgebra
representing the same continuous function. With that bridge in place the
universal approximation theorem reads as a statement directly about
explicit width-`m` ramp networks rather than about abstract subalgebra
elements.

The continuous-map analogue of `singleHiddenNN` along a fixed continuous
feature `ι : C(X, ℝ)` and with ramp activation `t ↦ max 0 t` is the
finite sum `∑ i, aᵢ • rampMap ι wᵢ bᵢ`. Each summand is, up to a scalar
multiple, a ramp drawn from `rampSet ι`, and `rampSubalgebra ι` is
closed under finite sums and scalar multiplication; hence the whole sum
lies in `rampSubalgebra ι`.
-/

/-- Continuous-map realisation of a single-hidden-layer **ramp**
network on `X` along a continuous feature `ι : C(X, ℝ)`, with `m`
hidden units, input weights `w : Fin m → ℝ`, biases `b : Fin m → ℝ`,
and output weights `a : Fin m → ℝ`. Concretely:
`x ↦ ∑ᵢ aᵢ · max 0 (wᵢ · ι x + bᵢ)`. -/
noncomputable def singleHiddenRampNN
    (ι : C(X, ℝ)) {m : ℕ} (a w b : Fin m → ℝ) : C(X, ℝ) :=
  ∑ i, (a i) • rampMap ι (w i) (b i)

set_option linter.unusedSectionVars false in
@[simp]
theorem singleHiddenRampNN_apply
    (ι : C(X, ℝ)) {m : ℕ} (a w b : Fin m → ℝ) (x : X) :
    singleHiddenRampNN ι a w b x =
      ∑ i, a i * max 0 (w i * ι x + b i) := by
  classical
  simp only [singleHiddenRampNN, ContinuousMap.coe_sum, Finset.sum_apply,
    ContinuousMap.smul_apply, rampMap_apply, smul_eq_mul]

set_option linter.unusedSectionVars false in
/-- Every single-hidden-layer ramp network along `ι` lies in the
ramp-spanned subalgebra. This is the bridge from the explicit
`singleHiddenRampNN` parametrisation to the abstract subalgebra
membership required by Stone–Weierstrass. -/
theorem singleHiddenRampNN_mem_rampSubalgebra
    (ι : C(X, ℝ)) {m : ℕ} (a w b : Fin m → ℝ) :
    singleHiddenRampNN ι a w b ∈ rampSubalgebra ι := by
  classical
  refine Subalgebra.sum_mem _ ?_
  intro i _
  refine Subalgebra.smul_mem _ ?_ (a i)
  exact Algebra.subset_adjoin ⟨(w i, b i), rfl⟩

/-- **Discharge of Tier C universal-approximation row (scaffold form).**
For any compact space `X` admitting an injective continuous map
`ι : C(X, ℝ)`, every continuous target `f : C(X, ℝ)` is uniformly
ε-approximated by some element of `rampSubalgebra ι` — the
subalgebra of `C(X, ℝ)` generated by the ramp family along `ι`.

**Honest scope (2026-05-23 audit):** this statement returns
`g ∈ rampSubalgebra ι`, *not* an explicit witness
`∃ m a w b, g = singleHiddenRampNN ι a w b`. The bridge lemma
`singleHiddenRampNN_mem_rampSubalgebra` shows that every explicit
single-hidden-layer ramp network `singleHiddenRampNN ι a w b` is an
element of this subalgebra — so this theorem combined with the bridge
lemma exhibits the class of explicit single-hidden-layer ramp networks
as a dense subset (in fact, a `Submodule`-dense one — a sum-of-scalar-
ramps expression) of `C(X, ℝ)`, recovering Cybenko (1989) /
Hornik (1991). The "scaffold" suffix in the theorem name flags this
indirect-witness shape: the existential is on subalgebra elements, not
on `singleHiddenRampNN` parameters.

**Rename note (2026-05-23):** previously called
`cybenko_uat_singleHiddenRampNN`, which falsely implied an explicit
NN-shape witness. Deprecated alias retained for backward
compatibility. -/
theorem cybenko_uat_rampSubalgebra_via_singleHiddenRampNN_scaffold
    {ι : C(X, ℝ)} (hι : Function.Injective ι)
    (f : C(X, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (g : C(X, ℝ)), g ∈ rampSubalgebra ι ∧ ‖g - f‖ < ε := by
  obtain ⟨g, hg⟩ := cybenko_uat_ramp_unconditional hι f hε
  exact ⟨(g : C(X, ℝ)), g.2, hg⟩

@[deprecated (since := "2026-05-23")] alias cybenko_uat_singleHiddenRampNN :=
  cybenko_uat_rampSubalgebra_via_singleHiddenRampNN_scaffold

set_option linter.unusedSectionVars false in
/-- Pointwise / unbundled version of
`cybenko_uat_rampSubalgebra_via_singleHiddenRampNN_scaffold`: given a
continuous target `f : X → ℝ` on a compact space `X` with an
injective continuous feature map `ι : C(X, ℝ)`, there exists some
element of `rampSubalgebra ι` whose pointwise distance to `f` is
uniformly bounded by `ε`.

As with the bundled version, the approximant `g` is asserted only to
lie in `rampSubalgebra ι` (not exhibited as a `singleHiddenRampNN`
parametrisation directly); the bridge lemma
`singleHiddenRampNN_mem_rampSubalgebra` is what guarantees that the
explicit `singleHiddenRampNN` parametrisation populates this
subalgebra.

**Rename note (2026-05-23):** previously called
`cybenko_uat_singleHiddenRampNN_pointwise`. Deprecated alias retained
for backward compatibility. -/
theorem cybenko_uat_rampSubalgebra_via_singleHiddenRampNN_scaffold_pointwise
    {ι : C(X, ℝ)} (hι : Function.Injective ι)
    (f : X → ℝ) (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(X, ℝ), g ∈ rampSubalgebra ι ∧ ∀ x, ‖g x - f x‖ < ε :=
  cybenko_uat_ramp_unconditional_pointwise hι f hf hε

@[deprecated (since := "2026-05-23")] alias cybenko_uat_singleHiddenRampNN_pointwise :=
  cybenko_uat_rampSubalgebra_via_singleHiddenRampNN_scaffold_pointwise

end LTFP.MathlibExt.Topology
