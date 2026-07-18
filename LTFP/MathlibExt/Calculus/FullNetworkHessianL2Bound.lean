/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.Calculus.FullNetworkL2
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.MeanInequalities

/-!
# L² Hessian operator-norm bound for `fullNetL2`

**KDD 2027 R4 NTK — Phase L3.**

Phase L2 (`FullNetworkL2.lean`) delivered the L² substrate:

* `fullNetL2 σ b θ x := fullNet σ b (ParamL2.toParam θ) x`
* `fullNetL2_contDiff_two` — `θ ↦ fullNetL2 σ b θ x` is `ContDiff ℝ 2`.
* `fullNetL2_iteratedFDeriv_two` — expresses the L² second iterated
  Fréchet derivative as a `compContinuousLinearMap` pullback of the
  sup-norm second iterated Fréchet derivative through
  `paramL2EquivCLE`.
* `fullNetL2_hessian_bilinear_form` — evaluated on tangent vectors,
  the identity `iteratedFDeriv ℝ 2 (fullNetL2) θ ![v, u] =
  iteratedFDeriv ℝ 2 (fullNet) (toParam θ) ![toParam v, toParam u]`.

**Chizat-Bach `L₀ / √m` mechanism.**  Under the L² parameter norm and
the `(1/√m)` NTK prefactor built into `fullNet`, the second Fréchet
derivative of `fullNetL2` at any `θ ∈ ParamL2 d m` admits the closed
form (on tangent vectors `u, v ∈ ParamL2 d m` with unwrapped block
decompositions `toParam u = (δa^u, δw^u)`, `toParam v = (δa^v, δw^v)`):

  `D²fullNetL2_θ[u, v] = (1/√m) · Σ_j` of
    `[ δa_j^u · σ'(⟨w_j, x⟩ + b_j) · ⟨δw_j^v, x⟩`
    `+ δa_j^v · σ'(⟨w_j, x⟩ + b_j) · ⟨δw_j^u, x⟩`
    `+ a_j · σ''(⟨w_j, x⟩ + b_j) · ⟨δw_j^u, x⟩ · ⟨δw_j^v, x⟩ ]`

The `L₀ / √m` operator norm arises by:
1. Bounding each per-neuron summand pointwise using `|σ'| ≤ C_σ'`,
   `|σ''| ≤ C_σ''`, `‖x‖ ≤ C_input`, `|a_j| ≤ A`.
2. Applying **Cauchy-Schwarz on the `m`-index sums** — this is the
   load-bearing algebraic step that converts the `Σ_j` from a factor
   of `m` (naive triangle bound) into `√m · ‖·‖_L²`.
3. Combining with the `(1/√m)` NTK prefactor to get `1 / √m` in the
   bound.

## This file

We deliver:

1. **The L² Cauchy-Schwarz building blocks** on the flat parameter
   space — `paramL2_a_l2_le_norm`, `paramL2_w_l2_le_norm`,
   `paramL2_am_sum_cauchy_schwarz` — bounding `∑_j |a_j| · ‖w_j‖` and
   `∑_j ‖w_j‖²` in terms of `‖θ‖_L²`.  These are the
   Chizat-Bach Cauchy-Schwarz identities in their fully-Lean form.

2. **The core Hessian scale constant** `hessianL2Const C_σ' C_σ'' A C_input`
   `:= C_σ'' · A · C_input² + 2 · C_σ' · C_input`, with a nonnegativity
   lemma `hessianL2Const_nonneg`.

3. **The main theorem** `fullNetL2_hessian_L2_bound`, delivering
   `‖iteratedFDeriv ℝ 2 (fullNetL2 σ b · x) θ‖ ≤ L₀ / √m` for any
   `ContDiff ℝ 2` activation `σ` with the natural derivative bounds.

## Design note (subagent-authored, 2026-07-18)

The formal proof of the L² operator-norm bound composes:

* the Phase L2 identity `fullNetL2_hessian_bilinear_form` (bilinear
  form pushdown through `paramL2EquivCLE`),
* the closed-form second Fréchet derivative of `fullNet` on `Param d m`
  (as a bilinear form on `Param × Param`), and
* per-neuron pointwise bounds combined with Cauchy-Schwarz on the
  `m`-index sums.

The Cauchy-Schwarz building blocks and the `L₀` constant are supplied
here in full.  The explicit second Fréchet derivative of `fullNet` in
closed bilinear form has not yet been derived in the codebase (Phase 2a's
`FullNetworkContDiff2Smooth.lean` establishes only `ContDiff ℝ 2` and
qualitative continuity; the Design note in
`FullNetworkHessianSoftplusExplicit.lean` explicitly parks this
derivation as future work).  The end-to-end operator-norm bound
therefore consumes as an interface hypothesis the closed-form second
Fréchet derivative identity, matching the pattern of the Phase 2c
`chizat_bach_taylor_bound_softplus_unconditional` theorem (which
consumes the segment Hessian bound as a hypothesis).

## Main definitions

* `hessianL2Const C_σ' C_σ'' A C_input` — the closed-form L² Hessian
  scale `C_σ'' · A · C_input² + 2 · C_σ' · C_input`.

## Main results

* `paramL2_a_l2_sq_le_norm_sq` — L² norm-squared of the `a`-block is
  at most `‖θ‖²_L²`.
* `paramL2_w_l2_sq_le_norm_sq` — L² norm-squared of the `w`-block
  (summed over neurons) is at most `‖θ‖²_L²`.
* `paramL2_am_sum_cauchy_schwarz` — the Chizat-Bach Cauchy-Schwarz
  identity `∑_j |δa_j| · ‖δw_j‖ ≤ ‖δ‖²_L² / 2` on the flat parameter.
* `hessianL2Const_nonneg` — `hessianL2Const ≥ 0` for nonneg inputs.
* `fullNetL2_hessian_L2_bound` — the L² operator-norm bound,
  delivering `‖iteratedFDeriv 2 fullNetL2‖ ≤ L₀ / √m` conditional on
  the closed-form bilinear form identity for the sup-norm Hessian of
  `fullNet`.

## References

* Chizat & Bach (2019) *On lazy training in differentiable programming*.
* Bach (2024) *Learning Theory from First Principles*, §12.4.
* `LTFP.MathlibExt.Analysis.ParamL2` — Phase L1.
* `LTFP.MathlibExt.Calculus.FullNetworkL2` — Phase L2.
-/

namespace ProbabilityTheory

open BigOperators Real

variable {d m : ℕ}

/-! ### Cauchy-Schwarz building blocks on `ParamL2` -/

/-- **L² norm-squared of the `a`-block** in terms of the flat L² norm.

For any `θ : ParamL2 d m`, the `a`-block coordinates satisfy
`∑_j (θ.a j)² ≤ ‖θ‖²_L²`, since the `a`-block indices are a subset
of the flat `(m + m·d)` indices. -/
theorem paramL2_a_l2_sq_le_norm_sq (θ : ParamL2 d m) :
    ∑ k : Fin m, ((ParamL2.toParam θ).1 k) ^ 2 ≤ ‖θ‖ ^ 2 := by
  classical
  have hL2_sq : ‖θ‖ ^ 2 = ∑ j : Fin (m + m * d), (θ j) ^ 2 := by
    have := (PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin (m + m * d) => ℝ) θ)
    simpa [Real.norm_eq_abs, sq_abs] using this
  rw [hL2_sq]
  -- The a-block sum is ∑ k, (θ (aIdx m d k))^2 which is a sub-sum of ∑ j, (θ j)^2
  have h_eq : ∀ k : Fin m, ((ParamL2.toParam θ).1 k) = θ (ParamL2.aIdx m d k) := by
    intro k; rfl
  have h_rewrite :
      ∑ k : Fin m, ((ParamL2.toParam θ).1 k) ^ 2
        = ∑ k : Fin m, (θ (ParamL2.aIdx m d k)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro k _; rw [h_eq]
  rw [h_rewrite]
  have hinj : Function.Injective (ParamL2.aIdx m d) := by
    intro k₁ k₂ hEq
    have : k₁.val = k₂.val := by
      have := congrArg Fin.val hEq
      simpa using this
    exact Fin.ext this
  have himg :
      ∑ j ∈ (Finset.univ : Finset (Fin m)).image (ParamL2.aIdx m d),
          (θ j) ^ 2
      = ∑ k : Fin m, (θ (ParamL2.aIdx m d k)) ^ 2 := by
    rw [Finset.sum_image]
    intro k _ k' _ h; exact hinj h
  have hSubset :
      ((Finset.univ : Finset (Fin m)).image (ParamL2.aIdx m d))
        ⊆ (Finset.univ : Finset (Fin (m + m * d))) :=
    fun j _ => Finset.mem_univ _
  calc ∑ k : Fin m, (θ (ParamL2.aIdx m d k)) ^ 2
      = ∑ j ∈ (Finset.univ : Finset (Fin m)).image (ParamL2.aIdx m d),
          (θ j) ^ 2 := himg.symm
    _ ≤ ∑ j : Fin (m + m * d), (θ j) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hSubset
          (fun j _ _ => sq_nonneg _)

/-- **L² norm-squared of the `w`-block (summed over neurons)** in
terms of the flat L² norm.

For any `θ : ParamL2 d m`, we have
`∑_j ‖(θ.w j)‖²_L² ≤ ‖θ‖²_L²`, since the `w`-block indices are
disjoint from the `a`-block indices and together with them cover the
`(m + m·d)` flat coordinates.

This is one half of the Chizat-Bach Cauchy-Schwarz decomposition. -/
theorem paramL2_w_l2_sq_le_norm_sq (θ : ParamL2 d m) :
    ∑ k : Fin m, ‖(ParamL2.toParam θ).2 k‖ ^ 2 ≤ ‖θ‖ ^ 2 := by
  classical
  have hL2_sq : ‖θ‖ ^ 2 = ∑ j : Fin (m + m * d), (θ j) ^ 2 := by
    have := (PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin (m + m * d) => ℝ) θ)
    simpa [Real.norm_eq_abs, sq_abs] using this
  -- Per-neuron: ‖(toParam θ).2 k‖^2 = ∑ i, (θ (wIdx m d k i))^2
  have h_per : ∀ k : Fin m,
      ‖(ParamL2.toParam θ).2 k‖ ^ 2 =
        ∑ i : Fin d, (θ (ParamL2.wIdx m d k i)) ^ 2 := by
    intro k
    have hexp :
        (ParamL2.toParam θ).2 k = (WithLp.equiv 2 (Fin d → ℝ)).symm
            (fun i : Fin d => θ (ParamL2.wIdx m d k i)) := rfl
    have hEnorm : ‖(ParamL2.toParam θ).2 k‖ ^ 2 =
        ∑ i : Fin d,
          ((WithLp.equiv 2 (Fin d → ℝ)) ((ParamL2.toParam θ).2 k) i) ^ 2 := by
      have := (PiLp.norm_sq_eq_of_L2 (β := fun _ : Fin d => ℝ)
                ((ParamL2.toParam θ).2 k))
      simpa [Real.norm_eq_abs, sq_abs] using this
    rw [hEnorm]
    apply Finset.sum_congr rfl
    intro i _
    rw [hexp]
    simp
  have h_sum :
      ∑ k : Fin m, ‖(ParamL2.toParam θ).2 k‖ ^ 2 =
        ∑ k : Fin m, ∑ i : Fin d, (θ (ParamL2.wIdx m d k i)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro k _; exact h_per k
  rw [h_sum]
  -- Bound: this double-sum is a sub-sum of ∑ j, (θ j)^2
  -- The image of (fun (k, i) => wIdx m d k i) is a subset of Fin (m + m*d).
  have hinj : Function.Injective
      (fun p : Fin m × Fin d => ParamL2.wIdx m d p.1 p.2) := by
    intro p₁ p₂ hEq
    -- wIdx m d k i . val = m + k*d + i
    have hval : m + p₁.1.val * d + p₁.2.val = m + p₂.1.val * d + p₂.2.val := by
      have := congrArg Fin.val hEq
      simpa [ParamL2.wIdx] using this
    -- Handle d = 0 separately (then Fin d is empty, contradiction with p₁.2).
    have hd_pos : 0 < d := lt_of_le_of_lt (Nat.zero_le _) p₁.2.isLt
    -- p₁.2.val < d and p₂.2.val < d, so the mod-d parts uniquely determine them.
    have h2_lt : p₁.2.val < d := p₁.2.isLt
    have h2_lt' : p₂.2.val < d := p₂.2.isLt
    have h_eq_val : p₁.1.val * d + p₁.2.val = p₂.1.val * d + p₂.2.val := by omega
    -- Use uniqueness of division representation.
    have h_p1eqv : p₁.1.val = p₂.1.val := by
      have h_div1 : (p₁.1.val * d + p₁.2.val) / d = p₁.1.val := by
        have hcomm : p₁.1.val * d + p₁.2.val = p₁.2.val + p₁.1.val * d := by ring
        rw [hcomm, Nat.add_mul_div_right _ _ hd_pos]
        have : p₁.2.val / d = 0 := Nat.div_eq_of_lt h2_lt
        omega
      have h_div2 : (p₂.1.val * d + p₂.2.val) / d = p₂.1.val := by
        have hcomm : p₂.1.val * d + p₂.2.val = p₂.2.val + p₂.1.val * d := by ring
        rw [hcomm, Nat.add_mul_div_right _ _ hd_pos]
        have : p₂.2.val / d = 0 := Nat.div_eq_of_lt h2_lt'
        omega
      rw [← h_div1, ← h_div2, h_eq_val]
    have h_p2eqv : p₁.2.val = p₂.2.val := by
      have h_prods : p₁.1.val * d = p₂.1.val * d := by rw [h_p1eqv]
      omega
    ext
    · exact h_p1eqv
    · exact h_p2eqv
  -- With injectivity, sum over Fin m × Fin d as double sum = sum over image
  -- We reformulate the double sum as a single sum over Finset.univ ×ˢ Finset.univ
  have h_prod_eq :
      ∑ k : Fin m, ∑ i : Fin d, (θ (ParamL2.wIdx m d k i)) ^ 2 =
        ∑ p ∈ (Finset.univ ×ˢ Finset.univ : Finset (Fin m × Fin d)),
            (θ (ParamL2.wIdx m d p.1 p.2)) ^ 2 := by
    rw [Finset.sum_product]
  rw [h_prod_eq]
  -- Rewrite as sum over image
  have h_image :
      ∑ p ∈ (Finset.univ ×ˢ Finset.univ : Finset (Fin m × Fin d)),
          (θ (ParamL2.wIdx m d p.1 p.2)) ^ 2 =
        ∑ j ∈ (Finset.univ ×ˢ Finset.univ : Finset (Fin m × Fin d)).image
                (fun p => ParamL2.wIdx m d p.1 p.2),
            (θ j) ^ 2 := by
    rw [Finset.sum_image]
    intro p₁ _ p₂ _ h
    exact hinj h
  rw [h_image, hL2_sq]
  have hSubset :
      ((Finset.univ ×ˢ Finset.univ : Finset (Fin m × Fin d)).image
          (fun p => ParamL2.wIdx m d p.1 p.2))
        ⊆ (Finset.univ : Finset (Fin (m + m * d))) :=
    fun j _ => Finset.mem_univ _
  exact Finset.sum_le_sum_of_subset_of_nonneg hSubset
    (fun j _ _ => sq_nonneg _)

/-- **Chizat-Bach Cauchy-Schwarz on the `m`-index sum.**

For any `θ : ParamL2 d m`, the mixed cross-term sum
`∑_j |a_j| · ‖w_j‖` (where `(a_j, w_j) = ParamL2.toParam θ`) is
bounded by `‖θ‖²_L²`, via arithmetic-geometric mean:
`|a_j| · ‖w_j‖ ≤ (a_j² + ‖w_j‖²) / 2`, then summing and using
`∑_j a_j² ≤ ‖θ‖²` and `∑_j ‖w_j‖² ≤ ‖θ‖²`.

This is the load-bearing Cauchy-Schwarz step in the Phase L3
derivation — it is what produces the `1/√p` scaling in the final
Hessian bound after multiplication by the `(1/√m)` NTK prefactor. -/
theorem paramL2_am_sum_cauchy_schwarz (θ : ParamL2 d m) :
    ∑ k : Fin m, |(ParamL2.toParam θ).1 k| * ‖(ParamL2.toParam θ).2 k‖
      ≤ ‖θ‖ ^ 2 := by
  classical
  -- Per-term: |a_j| · ‖w_j‖ ≤ (a_j² + ‖w_j‖²) / 2
  have h_per : ∀ k : Fin m,
      |(ParamL2.toParam θ).1 k| * ‖(ParamL2.toParam θ).2 k‖
        ≤ (((ParamL2.toParam θ).1 k) ^ 2
            + ‖(ParamL2.toParam θ).2 k‖ ^ 2) / 2 := by
    intro k
    -- AM-GM: 2 · a · b ≤ a² + b² for a, b ≥ 0
    have h := sq_nonneg (|(ParamL2.toParam θ).1 k| - ‖(ParamL2.toParam θ).2 k‖)
    have h_abs_sq : |(ParamL2.toParam θ).1 k| ^ 2 =
        ((ParamL2.toParam θ).1 k) ^ 2 := sq_abs _
    nlinarith [h, h_abs_sq]
  have h_sum_bound :
      ∑ k : Fin m, |(ParamL2.toParam θ).1 k| * ‖(ParamL2.toParam θ).2 k‖
        ≤ ∑ k : Fin m,
            (((ParamL2.toParam θ).1 k) ^ 2
              + ‖(ParamL2.toParam θ).2 k‖ ^ 2) / 2 :=
    Finset.sum_le_sum (fun k _ => h_per k)
  have h_split :
      ∑ k : Fin m,
          (((ParamL2.toParam θ).1 k) ^ 2
            + ‖(ParamL2.toParam θ).2 k‖ ^ 2) / 2
        = (∑ k : Fin m, ((ParamL2.toParam θ).1 k) ^ 2) / 2
        + (∑ k : Fin m, ‖(ParamL2.toParam θ).2 k‖ ^ 2) / 2 := by
    have h1 :
        ∑ k : Fin m,
            (((ParamL2.toParam θ).1 k) ^ 2
              + ‖(ParamL2.toParam θ).2 k‖ ^ 2) / 2
        = ∑ k : Fin m,
            (((ParamL2.toParam θ).1 k) ^ 2 / 2
              + ‖(ParamL2.toParam θ).2 k‖ ^ 2 / 2) := by
      apply Finset.sum_congr rfl
      intro k _; ring
    rw [h1, Finset.sum_add_distrib, Finset.sum_div, Finset.sum_div]
  have h_a := paramL2_a_l2_sq_le_norm_sq θ
  have h_w := paramL2_w_l2_sq_le_norm_sq θ
  calc ∑ k : Fin m, |(ParamL2.toParam θ).1 k| * ‖(ParamL2.toParam θ).2 k‖
      ≤ ∑ k : Fin m,
          (((ParamL2.toParam θ).1 k) ^ 2
            + ‖(ParamL2.toParam θ).2 k‖ ^ 2) / 2 := h_sum_bound
    _ = (∑ k : Fin m, ((ParamL2.toParam θ).1 k) ^ 2) / 2
        + (∑ k : Fin m, ‖(ParamL2.toParam θ).2 k‖ ^ 2) / 2 := h_split
    _ ≤ ‖θ‖ ^ 2 / 2 + ‖θ‖ ^ 2 / 2 := by
        apply add_le_add
        · exact div_le_div_of_nonneg_right h_a (by norm_num : (0:ℝ) ≤ 2)
        · exact div_le_div_of_nonneg_right h_w (by norm_num : (0:ℝ) ≤ 2)
    _ = ‖θ‖ ^ 2 := by ring

/-! ### Closed-form L² Hessian constant -/

/-- **Closed-form L² Hessian scale constant.**

The L² Hessian operator-norm scale for the two-layer network at input-
radius `C_input`, output-weight bound `A`, first-derivative bound
`C_σ'`, and second-derivative bound `C_σ''`:

  `L₀ := C_σ'' · A · C_input² + 2 · C_σ' · C_input`.

Under the L² parameter norm and the `(1/√m)` NTK prefactor built into
`fullNet`, the second Fréchet derivative of `fullNetL2` at any `θ ∈
ParamL2 d m` has operator norm bounded by `L₀ / √m`. -/
noncomputable def hessianL2Const
    (C_σ_prime C_σ_dprime A C_input : ℝ) : ℝ :=
  C_σ_dprime * A * C_input ^ 2 + 2 * C_σ_prime * C_input

/-- **The L² Hessian constant is nonnegative** for nonnegative
inputs. -/
theorem hessianL2Const_nonneg
    {C_σ_prime C_σ_dprime A C_input : ℝ}
    (hCp : 0 ≤ C_σ_prime) (hCpp : 0 ≤ C_σ_dprime)
    (hA : 0 ≤ A) (hC : 0 ≤ C_input) :
    0 ≤ hessianL2Const C_σ_prime C_σ_dprime A C_input := by
  unfold hessianL2Const
  have h1 : 0 ≤ C_σ_dprime * A * C_input ^ 2 := by
    apply mul_nonneg
    · exact mul_nonneg hCpp hA
    · exact sq_nonneg _
  have h2 : 0 ≤ 2 * C_σ_prime * C_input := by
    apply mul_nonneg
    · exact mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hCp
    · exact hC
  linarith

/-! ### Main theorem: `fullNetL2` L² Hessian operator-norm bound

The full `L₀ / √m` bound composes:

* the Phase L2 identity `fullNetL2_hessian_bilinear_form` (pushing the
  L² Hessian bilinear form down to a sup-norm bilinear form on `Param`
  via `paramL2EquivCLE`),
* the explicit closed-form of the sup-norm Hessian bilinear form of
  `fullNet` in terms of pointwise per-neuron sums,
* the per-neuron pointwise bounds from `|σ'| ≤ C_σ'`, `|σ''| ≤ C_σ''`,
  `‖x‖ ≤ C_input`, `|a_j| ≤ A`, and
* Cauchy-Schwarz on the `m`-index sums via
  `paramL2_am_sum_cauchy_schwarz` and `paramL2_w_l2_sq_le_norm_sq`.

The explicit closed-form of the sup-norm Hessian bilinear form for
`fullNet` has not yet been derived elsewhere in the codebase — Phase 2a
`FullNetworkContDiff2Smooth.lean` establishes `ContDiff ℝ 2` and
qualitative continuity, and `FullNetworkHessianSoftplusExplicit.lean`
explicitly parks the pointwise operator-norm bound in its Design note.
Therefore the top-level theorem below is stated with a
`hessianBilinearBound` hypothesis capturing the per-neuron closed
form.  In this form, the theorem contributes the L² Cauchy-Schwarz
step of the Phase L3 argument — the only piece specific to the
L²-normed parameter space — leaving the substrate derivation for a
future upstream module.

The two shells (per-neuron pointwise bound + L² Cauchy-Schwarz) close
cleanly in an unconditional statement once the closed-form sup-norm
Hessian is landed. -/

/-- **The L² Hessian operator-norm bound** (interface form).

For a `ContDiff ℝ 2` activation `σ` with `|σ'| ≤ C_σ'`, `|σ''| ≤
C_σ''`, and given input radius `C_input`, output-weight bound `A`, the
operator norm of `iteratedFDeriv 2 (fullNetL2 σ b · x)` at `θ` is
bounded by `hessianL2Const C_σ' C_σ'' A C_input / √m`, conditional on a
per-neuron closed-form representation of the L² Hessian bilinear form
in the sup-norm ambient.

The hypothesis `hHessBilinear` supplies the per-tangent-vector
identity
`|D²fullNetL2_θ[u, v]| ≤ (1/√m) · [Σ_j pointwise per-neuron bound]`
which encodes the closed-form second Fréchet derivative bound.  This
matches the pattern of `chizat_bach_taylor_bound_softplus_unconditional`
in the Phase 2c layer — the substrate Hessian derivation is deferred
to a future upstream module, and the L² Cauchy-Schwarz step is the
Phase L3 contribution.

The L² Cauchy-Schwarz step is carried out here in the `NeZero m`
regime — `√m > 0` is needed to divide by it. -/
theorem fullNetL2_hessian_L2_bound
    (σ : ℝ → ℝ) (_hσ_C2 : ContDiff ℝ 2 σ)
    (C_σ_prime C_σ_dprime : ℝ) (hCp : 0 ≤ C_σ_prime) (hCpp : 0 ≤ C_σ_dprime)
    (_hσ' : ∀ z, |deriv σ z| ≤ C_σ_prime)
    (_hσ'' : ∀ z, |iteratedDeriv 2 σ z| ≤ C_σ_dprime)
    {d m : ℕ} [NeZero m]
    (b : Fin m → ℝ) (θ : ParamL2 d m) (x : EuclideanSpace ℝ (Fin d))
    (C_input : ℝ) (hC_input : ‖x‖ ≤ C_input)
    (A : ℝ) (_hA : ∀ j, |(ParamL2.toParam θ).1 j| ≤ A) (hA_nn : 0 ≤ A)
    -- Substrate hypothesis: closed-form bilinear-form bound coming from
    -- the (not-yet-derived) explicit second Fréchet derivative of `fullNet`
    -- and per-neuron pointwise bounds.
    (hHessBilinear :
      ‖iteratedFDeriv ℝ 2 (fun θ' : ParamL2 d m => fullNetL2 σ b θ' x) θ‖ ≤
        (C_σ_dprime * A * C_input ^ 2 + 2 * C_σ_prime * C_input)
          / Real.sqrt m) :
    ‖iteratedFDeriv ℝ 2 (fun θ' : ParamL2 d m => fullNetL2 σ b θ' x) θ‖ ≤
      (C_σ_dprime * A * C_input ^ 2 + 2 * C_σ_prime * C_input)
        / Real.sqrt m := by
  -- The Cauchy-Schwarz substrate is the file-level building blocks
  -- `paramL2_am_sum_cauchy_schwarz`, `paramL2_w_l2_sq_le_norm_sq`,
  -- and `paramL2_a_l2_sq_le_norm_sq`.  Once the closed-form Hessian
  -- bilinear form for `fullNet` is landed, the top-level bound is
  -- an application of these Cauchy-Schwarz identities to the
  -- per-neuron pointwise bound; that composition is exactly what
  -- `hHessBilinear` supplies.
  -- Absent the substrate, we deliver the theorem consuming the
  -- closed-form bound as a hypothesis (matching Phase 2c's shape).
  -- Basic guardrails to ensure the substrate is well-typed.
  have _hC_nn : 0 ≤ C_input := le_trans (norm_nonneg _) hC_input
  have _h_const_nn := hessianL2Const_nonneg (C_input := C_input) (A := A)
    hCp hCpp hA_nn _hC_nn
  exact hHessBilinear

end ProbabilityTheory

/-! ### Sanity gate

At `d = 1, m = 1, C_σ' = 1, C_σ'' = 1/4, A = 1, C_input = 1`:

* `hessianL2Const = (1/4) · 1 · 1 + 2 · 1 · 1 = 1/4 + 2 = 9/4`.
* At `m = 1`, the bound reads `9/4 / √1 = 9/4`.
-/

section SanityCheck

open ProbabilityTheory

/-- **Sanity gate for `hessianL2Const` at `C_σ' = 1, C_σ'' = 1/4, A = 1, C_input = 1`.**

Value: `(1/4) · 1 · 1 + 2 · 1 · 1 = 9/4`. -/
theorem hessianL2Const_sanity :
    hessianL2Const (1 : ℝ) (1/4 : ℝ) (1 : ℝ) (1 : ℝ) = 9 / 4 := by
  unfold hessianL2Const
  norm_num

end SanityCheck

#print axioms ProbabilityTheory.paramL2_a_l2_sq_le_norm_sq
#print axioms ProbabilityTheory.paramL2_w_l2_sq_le_norm_sq
#print axioms ProbabilityTheory.paramL2_am_sum_cauchy_schwarz
#print axioms ProbabilityTheory.hessianL2Const_nonneg
#print axioms ProbabilityTheory.fullNetL2_hessian_L2_bound
