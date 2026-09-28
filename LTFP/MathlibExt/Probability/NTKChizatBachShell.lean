/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Probability.NTKLinearizedRKHS
import LTFP.MathlibExt.Probability.NTKTrainingSetBound

/-!
# NTK Chizat-Bach lazy-regime parametric shell (T6c-nonlin)

**Chizat & Bach (2019), Bach (2024) §12.4 — lazy-regime linearization
bound as a parametric carrier composed with T6c-lin's kernel expansion.**

The linearized surrogate `f^{lin}_θ(x)` at initialization `θ₀`
approximates the nonlinear network `f_θ(x)` in the lazy regime. The
sharpest existing analytic statement (Chizat & Bach 2019) is

  `sup_x |f_θ(x) - f^{lin}_θ(x)| ≤ C / √p`

for a width parameter `p`. Deriving this analytic bound from first
principles inside Lean is a multi-week Mathlib project (it needs a
quantitative Taylor-remainder-of-the-network estimate plus a
random-feature concentration on the Hessian). This module takes a
different tack: it accepts the Chizat-Bach bound as a *parametric
hypothesis* on a constant `C ≥ 0` and composes it with the T6c-lin
kernel expansion of `f^{lin}_θ - f_{θ₀}` to conclude a
"nonlinear network approximates a kernel-regression predictor" statement.

Concretely, given

* the finite-span hypothesis
  `θ - θ₀ ∈ span{∇_θ f_{θ₀}(x_i)}` (produced along any gradient-flow /
  gradient-descent trajectory on the linearized squared loss, and
  packaged by T6c-lin), and

* the parametric Chizat-Bach bound
  `∀ x, |f_θ(x) - f^{lin}_θ(x)| ≤ C`,

the shell theorem produces coefficients `α : Fin n → ℝ` such that

  `∀ x, |f_θ(x) - (f_{θ₀}(x) + ∑ i, α i · K_NTK(x, x_i))| ≤ C`.

Interpretation: modulo the parametric error `C` (which the honest
Chizat-Bach picture instantiates as `O(1/√p)` at width `p`), the
nonlinear network output is a *kernel-regression predictor* in the
finite-dimensional RKHS spanned by the empirical NTK kernel sections
at the training inputs — exactly the picture of Bach (2024) §12.4.

## Framing

The analytical bound `C = O(1/√p)` — the substantive lazy-regime
statement — is deferred to future work. This module is the **carrier**
that says: *if* such a bound holds, *then* the kernel expansion picture
also holds, with the same width-scaling in the residual. It composes
cleanly with T6c-lin (`ntk_linearized_model_in_finite_rkhs`) and, on
the training set, with the T6b-restricted pointwise residual decay
(`ntk_training_residual_pointwise_bound`).

## Main definitions

* `LTFP.ChizatBachBound σ σ' b θ₀ θ C` — the parametric hypothesis
  `∀ x, |f_θ(x) - f^{lin}_θ(x)| ≤ C`.

## Main results

* `LTFP.ntk_network_approx_kernel_expansion` — the shell theorem:
  under the finite-span hypothesis and the Chizat-Bach parametric
  bound, the nonlinear network approximates the empirical-NTK
  kernel-expansion predictor uniformly in the test input `x`, with
  error at most `C`.

* `LTFP.ntk_network_approx_kernel_expansion_at_init_exact` — R2
  counterexample-gate sanity check: at `C = 0` the shell degenerates
  to an exact kernel-expansion identity for the nonlinear network.

* `LTFP.ntk_network_pointwise_error_on_training_set` — corollary
  linking the shell with T6b-restricted's pointwise residual decay.
  On the training set specifically, the total pointwise error of the
  nonlinear-network prediction relative to the training labels
  decomposes into a Chizat-Bach `C`-term plus the exponentially-decaying
  T6b-restricted training-set residual.

## References

* Chizat, L. & Bach, F. (2019) *On lazy training in differentiable
  programming*. NeurIPS.
* Bach, F. (2024) *Learning Theory from First Principles*, §12.4
  (linearized model in the NTK regime).
* `LTFP.MathlibExt.Probability.NTKLinearizedRKHS` — the T6c-lin
  kernel-expansion of `f^{lin}_θ - f_{θ₀}`.
* `LTFP.MathlibExt.Probability.NTKTrainingSetBound` — T6b-restricted
  pointwise residual decay on the training set.
-/

namespace LTFP

open BigOperators Real ProbabilityTheory

/-! ### The Chizat-Bach parametric hypothesis -/

variable {d : ℕ}

/-- **Chizat-Bach lazy-regime parametric bound (hypothesis carrier).**

Packages the analytical Chizat-Bach (2019) lazy-regime linearization
bound as a hypothesis parametric in a scalar `C ≥ 0`. The intended
instantiation is `C = C₀ / √p` for a width parameter `p` and a
width-independent constant `C₀ > 0`, matching Bach (2024) §12.4.

The analytical bound itself — deriving the `1/√p` scaling from a
Taylor-remainder-of-the-network estimate plus random-feature Hessian
concentration — is a substantive multi-step argument left for future
Lean work. This structure is the parametric interface that downstream
composition consumes. -/
structure ChizatBachBound
    {m : ℕ}
    (σ σ' : ℝ → ℝ) (b : Fin m → ℝ) (θ₀ θ : Param d m) (C : ℝ) : Prop where
  /-- The uniform-in-`x` linearization error is bounded by `C`. -/
  bound : ∀ x : EuclideanSpace ℝ (Fin d),
    |fullNet σ b θ x - linearizedNetOutput σ σ' b θ₀ θ x| ≤ C

/-! ### The parametric shell theorem

Chaining T6c-lin's kernel expansion with the Chizat-Bach hypothesis
yields the "nonlinear network approximates a kernel-regression
predictor" statement of Bach (2024) §12.4. -/

/-- **NTK nonlinear-network kernel-expansion approximation.**

Under the finite-span hypothesis of T6c-lin and the Chizat-Bach
parametric bound `ChizatBachBound σ σ' b θ₀ θ C`, the nonlinear network
`f_θ(x)` differs from the empirical-NTK kernel-expansion predictor

  `f_{θ₀}(x) + ∑ i, α i · K_NTK(x, x_i)`

by at most `C`, uniformly in the test input `x`. The coefficients
`α : Fin n → ℝ` are exactly the ones produced by T6c-lin.

This is the parametric carrier of Bach (2024) §12.4: on top of the
deterministic RKHS identity for the linearized surrogate, the
Chizat-Bach lazy-regime bound propagates into the nonlinear regime
with the same-order residual. -/
theorem ntk_network_approx_kernel_expansion
    {n m : ℕ}
    (σ σ' : ℝ → ℝ) (b : Fin m → ℝ) (θ₀ θ : Param d m)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (h_span : θ - θ₀ ∈
      Submodule.span ℝ
        (Set.range (fun i => gradFullNet σ σ' b θ₀ (xs i))))
    {C : ℝ} (hC : ChizatBachBound σ σ' b θ₀ θ C) :
    ∃ α : Fin n → ℝ,
      ∀ x : EuclideanSpace ℝ (Fin d),
        |fullNet σ b θ x -
            (fullNet σ b θ₀ x +
              ∑ i, α i * paramNTKKernel σ σ' b θ₀ x (xs i))| ≤ C := by
  classical
  -- Step 1: extract the T6c-lin kernel expansion coefficients.
  obtain ⟨α, hα⟩ :=
    ntk_linearized_model_in_finite_rkhs σ σ' b θ₀ θ xs h_span
  refine ⟨α, ?_⟩
  intro x
  -- Step 2: rewrite the kernel expansion into the substitution form
  -- `linearizedNetOutput θ x = f_{θ₀}(x) + ∑ i, α i · K_NTK(x, x_i)`.
  have h_lin_eq :
      linearizedNetOutput σ σ' b θ₀ θ x
        = fullNet σ b θ₀ x +
            ∑ i, α i * paramNTKKernel σ σ' b θ₀ x (xs i) := by
    have h := hα x
    linarith
  -- Step 3: apply the Chizat-Bach hypothesis at `x` and substitute.
  have h_bound := hC.bound x
  -- `|f_θ(x) - linearizedNetOutput θ x| ≤ C` combined with h_lin_eq.
  rw [h_lin_eq] at h_bound
  exact h_bound

/-- **R2 counterexample-gate sanity check.**

At `C = 0` the Chizat-Bach hypothesis collapses to the exact identity
`f_θ(x) = f^{lin}_θ(x)` uniformly in `x`. The shell theorem then
degenerates to an exact kernel-expansion identity for the nonlinear
network: there exist coefficients `α : Fin n → ℝ` such that

  `f_θ(x) = f_{θ₀}(x) + ∑ i, α i · K_NTK(x, x_i)`

for every test input `x`. Specializing further to `n = 1` yields a
single-term kernel expansion `f_θ(x) = f_{θ₀}(x) + α · K_NTK(x, x_1)`.

The purpose of this corollary is defensive: it verifies that the
shell theorem specializes correctly in the null case `C = 0`, i.e.
that the shell does not accidentally weaken the deterministic identity
of T6c-lin. -/
theorem ntk_network_approx_kernel_expansion_at_init_exact
    {n m : ℕ}
    (σ σ' : ℝ → ℝ) (b : Fin m → ℝ) (θ₀ θ : Param d m)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (h_span : θ - θ₀ ∈
      Submodule.span ℝ
        (Set.range (fun i => gradFullNet σ σ' b θ₀ (xs i))))
    (hC0 : ChizatBachBound σ σ' b θ₀ θ 0) :
    ∃ α : Fin n → ℝ,
      ∀ x : EuclideanSpace ℝ (Fin d),
        fullNet σ b θ x
          = fullNet σ b θ₀ x +
              ∑ i, α i * paramNTKKernel σ σ' b θ₀ x (xs i) := by
  classical
  obtain ⟨α, hα⟩ :=
    ntk_network_approx_kernel_expansion σ σ' b θ₀ θ xs h_span hC0
  refine ⟨α, ?_⟩
  intro x
  have h := hα x
  -- `|LHS - RHS| ≤ 0` implies `LHS = RHS`.
  have h_abs_zero :
      |fullNet σ b θ x -
          (fullNet σ b θ₀ x +
            ∑ i, α i * paramNTKKernel σ σ' b θ₀ x (xs i))| = 0 :=
    le_antisymm h (abs_nonneg _)
  have h_diff_zero :
      fullNet σ b θ x -
          (fullNet σ b θ₀ x +
            ∑ i, α i * paramNTKKernel σ σ' b θ₀ x (xs i)) = 0 :=
    abs_eq_zero.mp h_abs_zero
  linarith

/-! ### Corollary: composition with T6b-restricted on the training set

On the training data specifically, the shell theorem composes with the
T6b-restricted pointwise residual decay
(`ntk_training_residual_pointwise_bound`) to give a coordinate-wise
decomposition of the total error. This is the parametric statement
that Bach (2024) §12.4 uses to conclude "the nonlinear network with a
lazy-regime bound achieves near-zero training error at the same
exponential rate as the linearized surrogate, up to the Chizat-Bach
residual".

The corollary is stated in a form that consumes both the shell result
and the T6b-restricted training-set bound, without re-deriving them. -/

/-- **Pointwise training-set error decomposition.**

Suppose the Chizat-Bach parametric bound `ChizatBachBound σ σ' b θ₀ θ C`
holds and suppose additionally that on the training set the linearized
model's prediction matches the training label up to a residual `ε ≥ 0`
in absolute value at index `i`, i.e.

  `|linearizedNetOutput σ σ' b θ₀ θ (xs i) - y i| ≤ ε`.

Then the nonlinear network's pointwise training error at `xs i` is
bounded by `C + ε`.

This is the coordinate-wise consumption interface: the T6b-restricted
pointwise decay `ntk_training_residual_pointwise_bound` supplies an
exponentially-decaying `ε` for the linearized residual, and the
Chizat-Bach shell contributes the `C = O(1/√p)` transfer to the
nonlinear network.

Note that `y` here is the training target and is unconstrained by the
lemma — the caller picks it. In the intended composition, `y` is the
label vector and `ε` is a specific exponential-decay bound from
T6b-restricted. -/
theorem ntk_network_pointwise_training_error_decomposition
    {n m : ℕ}
    (σ σ' : ℝ → ℝ) (b : Fin m → ℝ) (θ₀ θ : Param d m)
    (xs : Fin n → EuclideanSpace ℝ (Fin d))
    (y : Fin n → ℝ)
    {C ε : ℝ}
    (hC : ChizatBachBound σ σ' b θ₀ θ C)
    (i : Fin n)
    (h_lin_residual :
      |linearizedNetOutput σ σ' b θ₀ θ (xs i) - y i| ≤ ε) :
    |fullNet σ b θ (xs i) - y i| ≤ C + ε := by
  -- Triangle inequality: |f_θ(x_i) - y i|
  --   ≤ |f_θ(x_i) - f^{lin}_θ(x_i)| + |f^{lin}_θ(x_i) - y i|
  --   ≤ C + ε.
  have h_bound := hC.bound (xs i)
  have h_split :
      fullNet σ b θ (xs i) - y i
        = (fullNet σ b θ (xs i) - linearizedNetOutput σ σ' b θ₀ θ (xs i))
            + (linearizedNetOutput σ σ' b θ₀ θ (xs i) - y i) := by
    ring
  calc
    |fullNet σ b θ (xs i) - y i|
        = |(fullNet σ b θ (xs i) - linearizedNetOutput σ σ' b θ₀ θ (xs i))
            + (linearizedNetOutput σ σ' b θ₀ θ (xs i) - y i)| := by
          rw [h_split]
    _ ≤ |fullNet σ b θ (xs i) - linearizedNetOutput σ σ' b θ₀ θ (xs i)|
          + |linearizedNetOutput σ σ' b θ₀ θ (xs i) - y i| :=
          abs_add_le _ _
    _ ≤ C + ε := add_le_add h_bound h_lin_residual

end LTFP

#print axioms LTFP.ntk_network_approx_kernel_expansion
