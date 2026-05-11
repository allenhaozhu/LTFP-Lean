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

end LTFP.MathlibExt.Topology
