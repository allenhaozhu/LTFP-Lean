/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.FullNetworkGradient
import LTFP.Ch07_Kernels.Representer
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# NTK linearized-model finite-dimensional RKHS membership (T6c-lin)

**Bach (2024) §12.4 — the linearized network at initialization lives in
the finite-dimensional RKHS spanned by the empirical NTK kernel sections
`K_NTK(·, x_i)`.**

The *linearized model* at an initialization `θ₀ : Param d m` is the
affine surrogate

  `f^{lin}_θ(x) := f_{θ₀}(x) + ⟨∇_θ f_{θ₀}(x), θ - θ₀⟩_Param`,

where the parameter inner product on
`Param d m = (Fin m → ℝ) × (Fin m → EuclideanSpace ℝ (Fin d))` is the
sum of the standard Euclidean products on the two blocks. Under
gradient flow on the squared-error loss of this surrogate the
parameter increment `Δθ := θ - θ₀` stays in the finite-dimensional
subspace of parameter space spanned by the training-input gradients
`{∇_θ f_{θ₀}(x_i)}_{i=1}^n`. This module records the deterministic
consequence: the difference `f^{lin}_θ - f_{θ₀}`, evaluated at *any*
test input `x`, is a finite linear combination of the empirical NTK
kernel sections

  `K_NTK(·, x_i) : x ↦ paramNTKKernel x (xs i)`,

i.e. lives in the finite-dimensional RKHS
`span{K_NTK(·, x_i)}_{i=1}^n`.

## Deterministic structure

The proof is deterministic and does *not* depend on the training
dynamics (gradient flow, gradient step, discrete or continuous). It
reduces to the single algebraic input

  `θ - θ₀ ∈ Submodule.span ℝ (range (fun i => ∇_θ f_{θ₀}(x_i)))`.

Once this span-membership is given, the RKHS expansion coefficients
`α i` are read off directly from the linear-combination decomposition
of `θ - θ₀`. The span-membership holds along any gradient-flow or
gradient-descent trajectory of the linearized squared loss because the
gradient of that loss is itself a linear combination of the training
gradients (see the discrete Euler-step lemma below).

## Parameter inner product

`Param d m` is a product of two inner-product spaces, so its natural
inner product

  `⟨(a, w), (a', w')⟩_Param := Σ_j a_j · a'_j + Σ_j ⟨w_j, w'_j⟩`

is used throughout. Rather than reaching for the abstract Mathlib
`Prod` inner-product instance (which is only defined via the `WithLp 2`
wrapper) we spell out the sum explicitly via `paramInner` below. This
matches the concrete calculation in
`gradFullNet_inner_eq_fullTrainingKernel`.

## Main definitions

* `LTFP.paramInner` — the natural inner product on `Param d m` as an
  explicit sum of the two block Euclidean products.
* `LTFP.paramNTKKernel σ σ' b θ₀` — the empirical NTK kernel
  `K_NTK(x, x') := paramInner (∇_θ f_{θ₀}(x)) (∇_θ f_{θ₀}(x'))`.
* `LTFP.linearizedNetOutput σ σ' b θ₀ θ` — the linearized network
  predictor `f^{lin}_θ(x) := f_{θ₀}(x) + paramInner (∇_θ f_{θ₀}(x)) (θ - θ₀)`.

## Main results

* `LTFP.ntk_linearized_model_in_finite_rkhs` — main theorem: whenever
  the parameter increment `θ - θ₀` lies in the finite-dim span, the
  linearized network output difference is a finite sum of empirical
  NTK kernel sections:

    `f^{lin}_θ(x) - f_{θ₀}(x) = ∑ i, α i · K_NTK(x, x_i)`.

* `LTFP.ntk_linearized_span_step_invariant` — discrete gradient-step
  invariance: the sequence of parameter increments produced by
  explicit Euler on the linearized squared loss stays in
  `span{∇_θ f_{θ₀}(x_i)}` at every step.

* `LTFP.ntk_linearized_kernel_expansion_of_euler_trajectory` —
  composition of the two: any discrete-Euler trajectory with steps in
  the training-gradient span produces linearized outputs that expand
  as finite kernel sums.

## Sanity check (R2 counterexample gate)

At `n = 1`, `y = 1`, `r(T) = 0`, the theorem specializes to
`f^{lin}_θ(x) - f_{θ₀}(x) = α · K_NTK(x, x_1)` — a single-term kernel
expansion. This makes NO claim about ridge regression,
generalisation, or off-training-set behaviour: it is a pure
representer/finite-span statement about the linearized surrogate's
expressive support.

## References

* Bach (2024) *Learning Theory from First Principles*, §12.4 (NTK
  regime and linearized model).
* `LTFP.MathlibExt.Probability.FullNetworkGradient` — `gradFullNet`
  and the Gram identity `gradFullNet_inner_eq_fullTrainingKernel`.
* `LTFP.Ch07_Kernels.Representer` — `kernelExpansion` and the
  finite-span RKHS predictor form.
-/

namespace LTFP

open BigOperators Real ProbabilityTheory

/-! ### Parameter inner product on `Param d m`

`Param d m := (Fin m → ℝ) × (Fin m → EuclideanSpace ℝ (Fin d))`. Its
natural inner product is the sum of the standard Euclidean products
on the two blocks. We spell it out as a concrete sum-of-blocks
formula because Mathlib does not equip `Prod` with a direct
`InnerProductSpace` instance (only via `WithLp 2`). -/

/-- The parameter inner product on `Param d m` written as an explicit
sum of block Euclidean inner products. -/
noncomputable def paramInner
    {d m : ℕ} (u v : Param d m) : ℝ :=
  (∑ j, u.1 j * v.1 j) + (∑ j, inner ℝ (u.2 j) (v.2 j))

/-! ### Basic algebra of `paramInner`

We only need the two operations used in the RKHS calculation:
linearity in the second slot when the second slot is a finite linear
combination, and the additivity used to distribute over subtraction. -/

/-- `paramInner` is additive in its second argument. -/
theorem paramInner_add_right
    {d m : ℕ} (u v w : Param d m) :
    paramInner u (v + w) = paramInner u v + paramInner u w := by
  classical
  simp only [paramInner, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  have h1 :
      ∑ j, u.1 j * (v.1 j + w.1 j)
        = (∑ j, u.1 j * v.1 j) + (∑ j, u.1 j * w.1 j) := by
    simp only [mul_add, Finset.sum_add_distrib]
  have h2 :
      ∑ j, inner ℝ (u.2 j) (v.2 j + w.2 j)
        = (∑ j, inner ℝ (u.2 j) (v.2 j))
            + (∑ j, inner ℝ (u.2 j) (w.2 j)) := by
    simp only [inner_add_right, Finset.sum_add_distrib]
  rw [h1, h2]
  ring

/-- `paramInner` is homogeneous in the scalar factor of its second
argument. -/
theorem paramInner_smul_right
    {d m : ℕ} (c : ℝ) (u v : Param d m) :
    paramInner u (c • v) = c * paramInner u v := by
  classical
  simp only [paramInner, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply,
             smul_eq_mul]
  have h1 :
      ∑ j, u.1 j * (c * v.1 j) = c * ∑ j, u.1 j * v.1 j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    ring
  have h2 :
      ∑ j, inner ℝ (u.2 j) (c • v.2 j)
        = c * ∑ j, inner ℝ (u.2 j) (v.2 j) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [real_inner_smul_right]
  rw [h1, h2]
  ring

/-- `paramInner u 0 = 0`. -/
theorem paramInner_zero_right
    {d m : ℕ} (u : Param d m) : paramInner u 0 = 0 := by
  simp [paramInner]

/-- `paramInner` distributes over a `Finset.sum` in the second slot. -/
theorem paramInner_finset_sum_right
    {d m : ℕ} {ι : Type*} [DecidableEq ι] (u : Param d m)
    (s : Finset ι) (v : ι → Param d m) :
    paramInner u (∑ i ∈ s, v i)
      = ∑ i ∈ s, paramInner u (v i) := by
  refine Finset.induction_on s ?_ ?_
  · -- empty
    simp [paramInner_zero_right]
  · -- insert
    intro a t hat ih
    rw [Finset.sum_insert hat, Finset.sum_insert hat,
        paramInner_add_right, ih]

/-- `paramInner` distributes over a finite `∑ i, c i • v i`. -/
theorem paramInner_finset_sum_smul
    {d m n : ℕ} (u : Param d m)
    (c : Fin n → ℝ) (v : Fin n → Param d m) :
    paramInner u (∑ i, c i • v i)
      = ∑ i, c i * paramInner u (v i) := by
  classical
  rw [paramInner_finset_sum_right u Finset.univ (fun i => c i • v i)]
  refine Finset.sum_congr rfl ?_
  intro i _
  exact paramInner_smul_right (c i) u (v i)

/-! ### Empirical NTK kernel and linearized network output -/

variable {d : ℕ}

/-- **Empirical NTK kernel at initialization.**

The empirical NTK kernel is the parameter inner product of the
network's parameter gradients at the initialization `θ₀`:

  `K_NTK(x, x') := paramInner (∇_θ f_{θ₀}(x)) (∇_θ f_{θ₀}(x'))`.

Here `∇_θ f_{θ₀}` is the explicit parameter gradient `gradFullNet`
introduced in `FullNetworkGradient.lean`. Evaluating at `x'` a
training input `x_i` recovers a *kernel section*
`K_NTK(·, x_i)` used in the finite-dim RKHS expansion.

By `gradFullNet_inner_eq_fullTrainingKernel`, when evaluated at two
training inputs `xs r` and `xs s` this equals the corresponding entry
`fullTrainingKernel σ σ' b θ₀ xs r s` of the dynamic training kernel
at `θ₀`. -/
noncomputable def paramNTKKernel
    {m : ℕ}
    (σ σ' : ℝ → ℝ) (b : Fin m → ℝ) (θ₀ : Param d m)
    (x x' : EuclideanSpace ℝ (Fin d)) : ℝ :=
  paramInner (gradFullNet σ σ' b θ₀ x) (gradFullNet σ σ' b θ₀ x')

/-- **Linearized network output at `θ`.**

The linearized surrogate at initialization `θ₀`, evaluated at
parameter `θ` and test input `x`:

  `f^{lin}_θ(x) := f_{θ₀}(x)
                    + paramInner (∇_θ f_{θ₀}(x)) (θ - θ₀)`.

The parameter increment `θ - θ₀ ∈ Param d m` is computed componentwise
(the underlying `Prod` structure); the inner product is the
sum-of-blocks formula `paramInner`. -/
noncomputable def linearizedNetOutput
    {m : ℕ}
    (σ σ' : ℝ → ℝ) (b : Fin m → ℝ) (θ₀ θ : Param d m)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  fullNet σ b θ₀ x + paramInner (gradFullNet σ σ' b θ₀ x) (θ - θ₀)

/-- The linearized output at `θ = θ₀` reduces to the base network
value. -/
theorem linearizedNetOutput_at_init
    {m : ℕ}
    (σ σ' : ℝ → ℝ) (b : Fin m → ℝ) (θ₀ : Param d m)
    (x : EuclideanSpace ℝ (Fin d)) :
    linearizedNetOutput σ σ' b θ₀ θ₀ x = fullNet σ b θ₀ x := by
  classical
  simp [linearizedNetOutput, sub_self, paramInner_zero_right]

/-! ### Finite-dimensional RKHS membership (main theorem)

The theorem takes as its substantive hypothesis the finite-span
membership `θ - θ₀ ∈ span{∇_θ f_{θ₀}(x_i)}`. This hypothesis is
established for both discrete gradient descent and continuous gradient
flow on the linearized squared-error loss because the loss's gradient
is *itself* a linear combination of the training gradients (see
`ntk_linearized_span_step_invariant` for the discrete case). -/

/-- **NTK linearized-model finite-dimensional RKHS membership.**

For every parameter `θ` whose increment `θ - θ₀` lies in the finite-
dimensional subspace of `Param d m` spanned by the training-input
parameter gradients `{∇_θ f_{θ₀}(x_i)}_{i=1}^n`, the linearized
network output difference is a finite kernel expansion in the
empirical NTK:

  `f^{lin}_θ(x) - f_{θ₀}(x) = ∑ i, α i · K_NTK(x, x_i)`.

Bach (2024) §12.4 uses this to conclude that the linearized model
lives in the finite-dimensional RKHS spanned by the training-input
kernel sections — the deterministic side of the NTK regime story.

The proof is purely algebraic: substitute the span decomposition
`θ - θ₀ = ∑ i, α i • ∇_θ f_{θ₀}(x_i)` into
`f^{lin}_θ(x) - f_{θ₀}(x) = paramInner (∇_θ f_{θ₀}(x)) (θ - θ₀)` and
distribute the parameter inner product using bilinearity. -/
theorem ntk_linearized_model_in_finite_rkhs
    {n m : ℕ}
    (σ σ' : ℝ → ℝ) (b : Fin m → ℝ) (θ₀ θ : Param d m)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (h_span : θ - θ₀ ∈
      Submodule.span ℝ
        (Set.range (fun i => gradFullNet σ σ' b θ₀ (xs i)))) :
    ∃ α : Fin n → ℝ,
      ∀ (x : EuclideanSpace ℝ (Fin d)),
        linearizedNetOutput σ σ' b θ₀ θ x - fullNet σ b θ₀ x
          = ∑ i, α i * paramNTKKernel σ σ' b θ₀ x (xs i) := by
  classical
  -- Extract the linear-combination decomposition of the increment.
  obtain ⟨α, hα⟩ :=
    (Submodule.mem_span_range_iff_exists_fun ℝ).mp h_span
  refine ⟨α, ?_⟩
  intro x
  -- Unfold definitions.
  simp only [linearizedNetOutput, paramNTKKernel]
  -- After subtracting `f_{θ₀}(x)` the expression is a single paramInner.
  have h_diff :
      fullNet σ b θ₀ x
          + paramInner (gradFullNet σ σ' b θ₀ x) (θ - θ₀)
        - fullNet σ b θ₀ x
        = paramInner (gradFullNet σ σ' b θ₀ x) (θ - θ₀) := by ring
  rw [h_diff]
  -- Substitute the span decomposition of `θ - θ₀`.
  rw [← hα]
  -- Distribute `paramInner` across the finite sum.
  exact paramInner_finset_sum_smul (gradFullNet σ σ' b θ₀ x) α
    (fun i => gradFullNet σ σ' b θ₀ (xs i))

/-! ### Discrete gradient-step invariance of the span

For a clean, verifiable formalization of the training-dynamics side
we record the discrete-time (explicit Euler) version: any parameter
trajectory `θ : ℕ → Param d m` whose per-step increment
`θ (k+1) - θ k` is a linear combination of the training gradients
yields parameter increments `θ k - θ₀` that lie in
`span{∇_θ f_{θ₀}(x_i)}` for all `k`. This is the invariance property
consumed by the main theorem `ntk_linearized_model_in_finite_rkhs`.

The per-step hypothesis holds automatically for explicit Euler on the
linearized squared loss because that loss's gradient at any parameter
is `∑ i, (linearized-residual_i) · ∇_θ f_{θ₀}(x_i)`.

The continuous-time (gradient-flow) analogue is that any curve `Δ`
with `Δ 0 = 0` and `deriv Δ t ∈ span (range φ)` stays in the span;
the same "closed subspace + integral" argument yields it, and the
discrete version here serves as the tractable Lean-verified anchor. -/

theorem span_invariant_of_step_in_span
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {n : ℕ}
    (φ : Fin n → E)
    (Δ : ℕ → E)
    (h_init : Δ 0 = 0)
    (h_step : ∀ k, Δ (k + 1) - Δ k ∈
      Submodule.span ℝ (Set.range φ)) :
    ∀ k, Δ k ∈ Submodule.span ℝ (Set.range φ) := by
  intro k
  induction k with
  | zero =>
      rw [h_init]
      exact Submodule.zero_mem _
  | succ k ih =>
      have h_decomp : Δ (k + 1) = (Δ (k + 1) - Δ k) + Δ k := by
        abel
      rw [h_decomp]
      exact Submodule.add_mem _ (h_step k) ih

/-- **Discrete gradient-step span invariance for the linearized loss.**

If a parameter trajectory `θ : ℕ → Param d m` satisfies `θ 0 = θ₀`
and at every step the increment `θ (k+1) - θ k` lies in
`span{∇_θ f_{θ₀}(x_i)}`, then the parameter increment `θ k - θ₀`
lies in that span for all `k`.

This is the finite-span hypothesis of
`ntk_linearized_model_in_finite_rkhs`. The per-step hypothesis
`h_step` is automatically satisfied by an explicit Euler step on the
linearized squared loss, whose gradient at any parameter is
`∑ i, (linearized-residual_i) · ∇_θ f_{θ₀}(x_i)`. -/
theorem ntk_linearized_span_step_invariant
    {n m : ℕ}
    (σ σ' : ℝ → ℝ) (b : Fin m → ℝ) (θ₀ : Param d m)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (θ : ℕ → Param d m)
    (h_init : θ 0 = θ₀)
    (h_step : ∀ k, θ (k + 1) - θ k ∈
      Submodule.span ℝ
        (Set.range (fun i => gradFullNet σ σ' b θ₀ (xs i)))) :
    ∀ k, θ k - θ₀ ∈
      Submodule.span ℝ
        (Set.range (fun i => gradFullNet σ σ' b θ₀ (xs i))) := by
  -- Apply the abstract lemma to the increment sequence `k ↦ θ k - θ₀`.
  refine span_invariant_of_step_in_span
    (fun i => gradFullNet σ σ' b θ₀ (xs i))
    (fun j => θ j - θ₀) ?_ ?_
  · simp [h_init]
  · intro k
    have h_rewrite :
        (θ (k + 1) - θ₀) - (θ k - θ₀) = θ (k + 1) - θ k := by abel
    rw [h_rewrite]
    exact h_step k

/-! ### Composition: discrete Euler → finite-span → kernel expansion

Assembling the pieces: any discrete-step trajectory whose per-step
increment lies in the training-gradient span produces a parameter
whose increment lies in the span (by
`ntk_linearized_span_step_invariant`), and the linearized network
output difference is therefore a finite kernel expansion (by
`ntk_linearized_model_in_finite_rkhs`). -/

theorem ntk_linearized_kernel_expansion_of_euler_trajectory
    {n m : ℕ}
    (σ σ' : ℝ → ℝ) (b : Fin m → ℝ) (θ₀ : Param d m)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (θ : ℕ → Param d m)
    (h_init : θ 0 = θ₀)
    (h_step : ∀ k, θ (k + 1) - θ k ∈
      Submodule.span ℝ
        (Set.range (fun i => gradFullNet σ σ' b θ₀ (xs i))))
    (k : ℕ) :
    ∃ α : Fin n → ℝ,
      ∀ (x : EuclideanSpace ℝ (Fin d)),
        linearizedNetOutput σ σ' b θ₀ (θ k) x - fullNet σ b θ₀ x
          = ∑ i, α i * paramNTKKernel σ σ' b θ₀ x (xs i) :=
  ntk_linearized_model_in_finite_rkhs σ σ' b θ₀ (θ k) xs
    (ntk_linearized_span_step_invariant σ σ' b θ₀ xs θ h_init h_step k)

end LTFP

#print axioms LTFP.ntk_linearized_model_in_finite_rkhs
