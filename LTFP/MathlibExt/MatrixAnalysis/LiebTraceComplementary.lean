/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import LTFP.MathlibExt.MatrixAnalysis.LiebSuperopRpowPersp
import LTFP.MathlibExt.MatrixAnalysis.CStarRpowPerspectiveConcave
import LTFP.MathlibExt.MatrixAnalysis.CStarLogConcave

/-!
# Complementary Lieb concavity at a vector `vec K` (strictly positive case)

This file extracts the *complementary* form of Lieb's joint concavity
theorem at the vector level by combining

* `CFC.concaveOn_rpowPerspective` (joint operator concavity of the
  operator `rpow` perspective on the C⋆-algebra `SuperAlg n`, B6 L3
  Sub-Part 6.5),
* `LiebSuperop.rpowPerspective_L_R_of_strictlyPositive` (the
  simplification of the rpow perspective on `(LC A, RC B)` to
  `LC (A^p) * RC (B^(1-p))`, B6 L3 Sub-Part 7.3b, strictly positive
  case), and
* the Kronecker `vec`-identity `(B ⊗ₖ A) *ᵥ vec X = vec (A * X * Bᵀ)`
  (`Matrix.kronecker_mulVec_vec`).

The composition delivers the **scalar / quadratic form** of complementary
Lieb concavity:

```
ConcaveOn ℝ {z | IsStrictlyPositive z.1 ∧ IsStrictlyPositive z.2}
  (fun z => (Matrix.trace (star K * z.1 ^ p * K * z.2 ^ (1 - p))).re).
```

The PSD-relaxation of the first argument requires an ε-regularization
argument and is deferred to Sub-Part 7.5.

## Main result

* `CFC.lieb_concavity_complementary_strictPos` — for any `K`, any
  `p ∈ [0, 1]`, the map
  `(A, B) ↦ Re Tr(K* · A^p · K · B^(1-p))` is concave on the open cone
  of pairs of strictly positive matrices.

## Proof structure

We package the construction with three local helpers:

1. `Φmat` — the scalar quadratic functional on the *underlying matrix*
   `M ↦ Re ⟨vec K, M *ᵥ vec K⟩`, additive and `ℝ`-scalar-homogeneous.
2. `Φmat_monotone_on_posSemidef` — monotonicity through `PosSemidef`.
3. `mulVec_vec_of_L_mul_R` — Kronecker vec-identity for the underlying
   matrix of `LC A * RC B`.

The main theorem is then obtained by applying `Φmat` (a real-affine
monotone functional) to the operator inequality coming from
`CFC.concaveOn_rpowPerspective`, after specialising it to the pair
`(LC A, RC B)` via `rpowPerspective_L_R_of_strictlyPositive`.
-/

@[expose] public section

open scoped Kronecker ComplexOrder NNReal MatrixOrder Matrix
open CStarMatrix CFC

namespace LiebSuperop

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Helper 1: transport of the C⋆-algebra order to/from matrices -/

omit [DecidableEq n] in
/-- The C⋆-algebra order on `SuperAlg n` agrees with the matrix
`PosSemidef` order through `CStarMatrix.ofMatrix`.  This is the
two-sided strengthening of `ofMatrix_nonneg_of_nonneg`: both
directions are intertwined via the star ring equivalence
`ofMatrixStarAlgEquiv`. -/
lemma ofMatrix_le_ofMatrix_iff {M N : Matrix (n × n) (n × n) ℂ} :
    (CStarMatrix.ofMatrix M : SuperAlg n) ≤ CStarMatrix.ofMatrix N
      ↔ M ≤ N := by
  -- `ofMatrixStarAlgEquiv` is an `OrderIsoClass` via
  -- `StarRingEquivClass.instOrderIsoClass`; the `iff` follows from
  -- `OrderIsoClass.map_le_map_iff`.
  exact OrderIsoClass.map_le_map_iff
    (CStarMatrix.ofMatrixStarAlgEquiv (n := n × n) (A := ℂ))

/-- A nonneg element of `SuperAlg n` corresponds to a `PosSemidef`
matrix under the identity-on-data type-copy `ofMatrix.symm`. -/
lemma posSemidef_of_nonneg_superAlg
    {M : SuperAlg n} (hM : 0 ≤ M) :
    (M : Matrix (n × n) (n × n) ℂ).PosSemidef := by
  -- Both `SuperAlg n` and `Matrix (n × n) (n × n) ℂ` have the same
  -- underlying type via the definitional alias
  -- `CStarMatrix m n A := Matrix m n A`.
  have hM' : (CStarMatrix.ofMatrix (M : Matrix (n × n) (n × n) ℂ)
        : SuperAlg n) = M := rfl
  have h0 : (CStarMatrix.ofMatrix (0 : Matrix (n × n) (n × n) ℂ)
        : SuperAlg n) = 0 := rfl
  rw [← hM', ← h0] at hM
  have hle : (0 : Matrix (n × n) (n × n) ℂ) ≤
      (M : Matrix (n × n) (n × n) ℂ) :=
    ofMatrix_le_ofMatrix_iff.mp hM
  exact Matrix.nonneg_iff_posSemidef.mp hle

/-! ### Helper 2: the scalar quadratic functional `Φmat` -/

/-- The scalar quadratic functional associated to a matrix `K`:
`Φmat K M = Re ⟨vec K, M *ᵥ vec K⟩` on the matrix
`M : Matrix (n × n) (n × n) ℂ`.

`Φmat K` is additive and `ℝ`-scalar-homogeneous in `M`, and monotone
on the PSD cone. -/
noncomputable def Φmat (K : Matrix n n ℂ)
    (M : Matrix (n × n) (n × n) ℂ) : ℝ :=
  (star (Matrix.vec K) ⬝ᵥ (M *ᵥ Matrix.vec K)).re

omit [DecidableEq n] in
lemma Φmat_add (K : Matrix n n ℂ) (M N : Matrix (n × n) (n × n) ℂ) :
    Φmat K (M + N) = Φmat K M + Φmat K N := by
  unfold Φmat
  rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re]

omit [DecidableEq n] in
lemma Φmat_smul_real (K : Matrix n n ℂ) (c : ℝ)
    (M : Matrix (n × n) (n × n) ℂ) :
    Φmat K (c • M) = c * Φmat K M := by
  unfold Φmat
  -- `(c • M) *ᵥ x = c • (M *ᵥ x)`, then the `ℝ`-smul on `ℂ` is
  -- multiplication by `(c : ℂ)`.
  rw [show (c • M : Matrix (n × n) (n × n) ℂ) *ᵥ Matrix.vec K
        = c • (M *ᵥ Matrix.vec K) from Matrix.smul_mulVec _ _ _,
      dotProduct_smul, Complex.real_smul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im]
  ring

omit [DecidableEq n] in
/-- `Φmat K` is monotone on the PSD cone (and hence on the
`Matrix.le` order, which is `PosSemidef` of the difference). -/
lemma Φmat_monotone_on_posSemidef (K : Matrix n n ℂ)
    {M N : Matrix (n × n) (n × n) ℂ} (hMN : M ≤ N) :
    Φmat K M ≤ Φmat K N := by
  have hpsd : (N - M).PosSemidef := Matrix.le_iff.mp hMN
  -- `re_dotProduct_nonneg` for `N - M`.
  have h0 : 0 ≤ (star (Matrix.vec K)
                    ⬝ᵥ ((N - M) *ᵥ Matrix.vec K)).re := by
    have := hpsd.re_dotProduct_nonneg (Matrix.vec K)
    -- `RCLike.re` on `ℂ` is `Complex.re` (definitionally).
    exact this
  -- `Φmat K (N - M) = Φmat K N - Φmat K M` by additivity (via sub).
  have hsub : Φmat K (N - M) = Φmat K N - Φmat K M := by
    have := Φmat_add (n := n) K (N - M) M
    -- `(N - M) + M = N`.
    rw [sub_add_cancel] at this
    linarith
  have h0' : 0 ≤ Φmat K (N - M) := h0
  linarith [hsub.symm ▸ h0']

/-! ### Helper 3: vec/trace evaluation for `L A * R B` -/

/-- The Kronecker `vec`-identity, specialised to the superoperator
factorisation `L A * R B = Bᵀ ⊗ₖ A` (`LiebSuperop.L_mul_R`): for any
matrices `A`, `B`, `K`,

```
(L A * R B) *ᵥ vec K = vec (A * K * B).
```

The transpose-collapse is `Matrix.transpose_transpose`. -/
lemma L_mul_R_mulVec_vec (A B K : Matrix n n ℂ) :
    (L A * R B) *ᵥ Matrix.vec K = Matrix.vec (A * K * B) := by
  rw [L_mul_R]
  -- `kronecker_mulVec_vec` with `B := Bᵀ`:
  --   `(Bᵀ ⊗ₖ A) *ᵥ vec K = vec (A * K * (Bᵀ)ᵀ) = vec (A * K * B)`.
  have hkron := Matrix.kronecker_mulVec_vec (R := ℂ) A K B.transpose
  rw [Matrix.transpose_transpose] at hkron
  exact hkron

/-- Evaluation of `Φmat` on `L (A^p) * R (B^(1-p))` produces the
target scalar trace functional. -/
lemma Φmat_L_pow_mul_R_pow (A B K : Matrix n n ℂ) (p : ℝ) :
    Φmat K (L (A ^ p) * R (B ^ ((1 : ℝ) - p)))
      = (Matrix.trace
          (star K * (A ^ p) * K * (B ^ ((1 : ℝ) - p)))).re := by
  unfold Φmat
  rw [L_mul_R_mulVec_vec, Matrix.star_vec_dotProduct_vec]
  -- After: `LHS = Re (Kᴴ * (A^p * K * B^(1-p))).trace`.
  -- Use `star_eq_conjTranspose`, then re-associate to match the target.
  rw [← Matrix.star_eq_conjTranspose]
  -- Goal: `Re tr (star K * (A^p * K * B^(1-p)))
  --      = Re tr (star K * A^p * K * B^(1-p))`.
  congr 2
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc]

end LiebSuperop

/-! ### Main theorem -/

namespace CFC

open LiebSuperop

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Convexity of the cone of strictly positive matrices.**

For `M N : Matrix n n ℂ` both strictly positive (= positive definite)
and weights `0 ≤ t`, `0 ≤ u` with `t + u = 1`, the convex combination
`t • M + u • N` is again strictly positive.  Proof routes through
`Matrix.PosDef.add_posSemidef` / `Matrix.PosDef.smul`. -/
lemma convex_setOf_isStrictlyPositive_matrix :
    Convex ℝ {M : Matrix n n ℂ | IsStrictlyPositive M} := by
  intro M hM N hN t u ht hu htu
  simp only [Set.mem_setOf_eq] at hM hN ⊢
  -- Translate to `PosDef`.
  have hMd : M.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp hM
  have hNd : N.PosDef := Matrix.isStrictlyPositive_iff_posDef.mp hN
  -- Case-split on which weight is strictly positive (`t + u = 1`,
  -- so at least one is `> 0`).
  rcases ht.lt_or_eq with htpos | ht0
  · -- `t > 0` so `t • M` is PosDef; `u • N` is PosSemidef.
    have h1 : (t • M).PosDef := hMd.smul htpos
    have h2 : (u • N).PosSemidef := hNd.posSemidef.smul hu
    have hadd : (t • M + u • N).PosDef := h1.add_posSemidef h2
    exact Matrix.isStrictlyPositive_iff_posDef.mpr hadd
  · -- `t = 0` so `u = 1` and `t • M + u • N = N`.
    subst ht0
    have hu1 : u = 1 := by linarith
    subst hu1
    simpa using hN

/-- **Complementary Lieb concavity at a vector (strictly positive case).**

For any matrix `K` and any `p ∈ [0, 1]`, the bilinear-quadratic functional

```
(A, B) ↦ Re Tr(K* · A^p · K · B^(1-p))
```

is jointly concave on the open cone of pairs of strictly positive
matrices.

This is the scalar / quadratic-form extraction of Lieb's joint
concavity theorem at the inner-product slot `(vec K, vec K)`, with both
inputs strictly positive.  PSD-relaxation of the first argument is
deferred to B6 L3 Sub-Part 7.5 (requires an ε-regularization argument
together with continuity of `(·)^p` in the operator argument).

**Proof.**  Combine

* `CFC.concaveOn_rpowPerspective` — joint operator concavity of
  `(a, b) ↦ rpowPerspective p a b` on the natural domain in the
  C⋆-algebra `SuperAlg n` (B6 L3 Sub-Part 6.5);
* `rpowPerspective_L_R_of_strictlyPositive` — for strict-positive
  `(A, B)`, `rpowPerspective p (LC A) (RC B) = LC (A^p) * RC (B^(1-p))`
  (B6 L3 Sub-Part 7.3b);
* `L_mul_R_mulVec_vec` — Kronecker vec-identity
  `(L X * R Y) *ᵥ vec K = vec (X * K * Y)`;
* `star_vec_dotProduct_vec` — trace identification
  `star (vec K) ⬝ᵥ vec Y = tr (Kᴴ * Y)`.

The monotone real-linear functional
`Φmat K M = Re ⟨vec K, M *ᵥ vec K⟩` then pushes the operator
inequality down to scalars.
-/
theorem lieb_concavity_complementary_strictPos
    (K : Matrix n n ℂ) {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    ConcaveOn ℝ
      {z : Matrix n n ℂ × Matrix n n ℂ |
        IsStrictlyPositive z.1 ∧ IsStrictlyPositive z.2}
      (fun z =>
        (Matrix.trace
            (star K * (z.1 ^ p) * K * (z.2 ^ ((1 : ℝ) - p)))).re) := by
  -- Convexity of the domain (product of two open cones).
  have hconv : Convex ℝ
      {z : Matrix n n ℂ × Matrix n n ℂ |
        IsStrictlyPositive z.1 ∧ IsStrictlyPositive z.2} := by
    have hSP := convex_setOf_isStrictlyPositive_matrix (n := n)
    have hprod := hSP.prod hSP
    -- The domain matches the product set `{A | sp A} ×ˢ {B | sp B}`
    -- after unpacking `Set.mem_prod` and `Set.mem_setOf_eq`.
    convert hprod using 1
  refine ⟨hconv, ?_⟩
  rintro ⟨A₁, B₁⟩ hz₁ ⟨A₂, B₂⟩ hz₂ t u ht hu htu
  obtain ⟨hA₁, hB₁⟩ : IsStrictlyPositive A₁ ∧ IsStrictlyPositive B₁ := hz₁
  obtain ⟨hA₂, hB₂⟩ : IsStrictlyPositive A₂ ∧ IsStrictlyPositive B₂ := hz₂
  -- Strict positivity of the convex combinations.
  have hA_conv_sp : IsStrictlyPositive (t • A₁ + u • A₂ : Matrix n n ℂ) :=
    convex_setOf_isStrictlyPositive_matrix (n := n) hA₁ hA₂ ht hu htu
  have hB_conv_sp : IsStrictlyPositive (t • B₁ + u • B₂ : Matrix n n ℂ) :=
    convex_setOf_isStrictlyPositive_matrix (n := n) hB₁ hB₂ ht hu htu
  -- C⋆-algebra wrappers and their strict positivity.
  have ha₁_sp : IsStrictlyPositive (LC A₁ : SuperAlg n) :=
    LC_strictlyPositive (n := n) hA₁
  have ha₂_sp : IsStrictlyPositive (LC A₂ : SuperAlg n) :=
    LC_strictlyPositive (n := n) hA₂
  have hb₁_sp : IsStrictlyPositive (RC B₁ : SuperAlg n) :=
    RC_strictlyPositive (n := n) hB₁
  have hb₂_sp : IsStrictlyPositive (RC B₂ : SuperAlg n) :=
    RC_strictlyPositive (n := n) hB₂
  -- Membership in the natural domain of `rpowPerspective`.
  have hz₁' : ((LC A₁ : SuperAlg n), RC B₁) ∈
      {z : SuperAlg n × SuperAlg n | 0 ≤ z.1 ∧ IsStrictlyPositive z.2} :=
    ⟨ha₁_sp.nonneg, hb₁_sp⟩
  have hz₂' : ((LC A₂ : SuperAlg n), RC B₂) ∈
      {z : SuperAlg n × SuperAlg n | 0 ≤ z.1 ∧ IsStrictlyPositive z.2} :=
    ⟨ha₂_sp.nonneg, hb₂_sp⟩
  -- Operator-level concavity inequality on `SuperAlg n`.
  have hop_raw := (concaveOn_rpowPerspective (A := SuperAlg n) hp).2
                    hz₁' hz₂' ht hu htu
  -- Unfold `Prod.smul` / `Prod.add` and beta-reduce.
  simp only [Prod.smul_mk, Prod.mk_add_mk] at hop_raw
  -- Real-linearity of `LC`/`RC` at convex combinations, fully expanded.
  -- Since `LC X := ofMatrix (L X)`, `ofMatrix` is `Equiv.refl`, and the
  -- `ℝ`-module structure on `Matrix n n ℂ` factors through `ℂ`, we have
  -- `t • LC A = LC (t • A)` and `LC A + LC B = LC (A + B)` after
  -- entry-wise comparison.
  have hLC_comb : ((t • (LC A₁ : SuperAlg n) + u • LC A₂ : SuperAlg n))
                  = LC (t • A₁ + u • A₂) := by
    -- Unfold `LC` to `ofMatrix (L _)` and verify entry-wise.
    show (t • CStarMatrix.ofMatrix (L A₁) + u • CStarMatrix.ofMatrix (L A₂)
          : SuperAlg n) = CStarMatrix.ofMatrix (L (t • A₁ + u • A₂))
    ext i j
    simp only [CStarMatrix.add_apply, CStarMatrix.smul_apply,
      CStarMatrix.ofMatrix_apply, L, Matrix.kroneckerMap_apply,
      Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
    by_cases h : i.1 = j.1
    · simp [h, mul_add]
    · simp [h]
  have hRC_comb : ((t • (RC B₁ : SuperAlg n) + u • RC B₂ : SuperAlg n))
                  = RC (t • B₁ + u • B₂) := by
    show (t • CStarMatrix.ofMatrix (R B₁) + u • CStarMatrix.ofMatrix (R B₂)
          : SuperAlg n) = CStarMatrix.ofMatrix (R (t • B₁ + u • B₂))
    ext i j
    simp only [CStarMatrix.add_apply, CStarMatrix.smul_apply,
      CStarMatrix.ofMatrix_apply, R, Matrix.kroneckerMap_apply,
      Matrix.add_apply, Matrix.smul_apply,
      Matrix.transpose_apply, Matrix.one_apply]
    by_cases h : i.2 = j.2
    · simp [h]
    · simp [h]
  -- Apply `rpowPerspective_L_R_of_strictlyPositive` at all three slots.
  have hp0 : (0 : ℝ) ≤ p := hp.1
  rw [hLC_comb, hRC_comb,
      rpowPerspective_L_R_of_strictlyPositive (n := n) hA₁ hB₁ hp0,
      rpowPerspective_L_R_of_strictlyPositive (n := n) hA₂ hB₂ hp0,
      rpowPerspective_L_R_of_strictlyPositive (n := n)
        hA_conv_sp hB_conv_sp hp0] at hop_raw
  -- Now convert `hop_raw` (in `SuperAlg n`) to a `Matrix`-level inequality.
  -- `LC X * RC Y` underlies `L X * R Y` (CStarMatrix multiplication is
  -- defeq to matrix multiplication through `ofMatrix`).  Combined with
  -- defeq-of-smul, the inequality is the same after `ofMatrix.symm`.
  have hop_mat : ((t • (L (A₁ ^ p) * R (B₁ ^ ((1 : ℝ) - p)))
                + u • (L (A₂ ^ p) * R (B₂ ^ ((1 : ℝ) - p))))
                : Matrix (n × n) (n × n) ℂ)
            ≤ (L ((t • A₁ + u • A₂) ^ p) * R ((t • B₁ + u • B₂) ^ ((1 : ℝ) - p))
                : Matrix (n × n) (n × n) ℂ) := by
    -- Every `LC X * RC Y` term in `hop_raw` equals `ofMatrix (L X * R Y)`
    -- by defeq (CStarMatrix multiplication unfolds to matrix multiplication).
    -- The `ℝ`-smul on `CStarMatrix` equals `ofMatrix ∘ (smul on Matrix)`.
    -- We use `ofMatrix_le_ofMatrix_iff` to peel off the type wrapper.
    have hwrap : (CStarMatrix.ofMatrix
        (t • (L (A₁ ^ p) * R (B₁ ^ ((1 : ℝ) - p)))
          + u • (L (A₂ ^ p) * R (B₂ ^ ((1 : ℝ) - p)))
              : Matrix (n × n) (n × n) ℂ) : SuperAlg n)
        ≤ CStarMatrix.ofMatrix
            (L ((t • A₁ + u • A₂) ^ p) *
              R ((t • B₁ + u • B₂) ^ ((1 : ℝ) - p))) := hop_raw
    exact ofMatrix_le_ofMatrix_iff.mp hwrap
  -- Apply `Φmat` (monotone) to `hop_mat`.
  have hΦle := Φmat_monotone_on_posSemidef (n := n) K hop_mat
  -- Expand `Φmat` of the LHS by additivity and scalar-homogeneity, then
  -- apply the trace evaluation lemma to each `L * R` block.
  rw [Φmat_add, Φmat_smul_real, Φmat_smul_real,
      Φmat_L_pow_mul_R_pow, Φmat_L_pow_mul_R_pow,
      Φmat_L_pow_mul_R_pow] at hΦle
  -- Convert `ℝ`-smul on `ℝ` to multiplication on the goal.
  change t • _ + u • _ ≤ _
  rw [smul_eq_mul, smul_eq_mul]
  exact hΦle

/-! ### Extension A: relax the second argument to PosSemidef -/

open scoped Topology Matrix.Norms.L2Operator

namespace Matrix.Norms.L2Operator

/-- The unital `CStarAlgebra` instance on `Matrix n n ℂ` under the
`Matrix.Norms.L2Operator` topology. Although `Matrix n n ℂ` carries
`NormedRing`, `NormedAlgebra ℂ`, `CStarRing`, `CompleteSpace`,
`StarRing`, and `StarModule ℂ` instances individually via the
L2-operator-norm scope, the bundled `CStarAlgebra` class is not
auto-synthesised; we provide it explicitly here so downstream
`ContinuousFunctionalCalculus` / `IsometricContinuousFunctionalCalculus`
instances become available.

Scoped to `Matrix.Norms.L2Operator` so the bundled `CStarAlgebra`
structure on raw `Matrix n n ℂ` is exported only to files that opt in
via `open scoped Matrix.Norms.L2Operator`. -/
noncomputable scoped instance instCStarAlgebraL2Op
    {n : Type*} [Fintype n] [DecidableEq n] : CStarAlgebra (Matrix n n ℂ) where

end Matrix.Norms.L2Operator

-- Re-open after declaring the scoped instance so it is in scope below.
open scoped Matrix.Norms.L2Operator

set_option maxHeartbeats 800000

/-- **Complementary Lieb concavity at a vector (`A` strict-pos, `B` PSD).**

For any matrix `K` and any `p ∈ [0, 1]`, the bilinear-quadratic functional

```
(A, B) ↦ Re Tr(K* · A^p · K · B^(1-p))
```

is jointly concave on the domain of pairs where `A` is strictly positive
and `B` is positive semidefinite.

This is **Extension A** of `lieb_concavity_complementary_strictPos`
(B6 L3 Sub-Part 7.4): the strict-positive requirement on the second
argument is relaxed to merely `PosSemidef` via an `ε`-regularization
argument.

**Proof.**  For each `ε > 0`, the perturbed map

```
g_ε (A, B) := Re Tr(K* · A^p · K · (B + ε•1)^(1-p))
```

is concave on `{(A, B) | A strict-pos ∧ B PSD}`, because:

* `B + ε•1` is strictly positive whenever `B` is PSD (sum of PSD and
  PosDef is PosDef);
* The convex combination `t • (A₁, B₁) + u • (A₂, B₂) ↦ (·, · + ε•1)`
  factors through `(tA₁+uA₂, t(B₁+ε•1) + u(B₂+ε•1))` since
  `t + u = 1` distributes `ε•1` correctly;
* The strict-pos theorem `lieb_concavity_complementary_strictPos`
  then applies to give the concavity inequality on the perturbed
  inputs.

As `ε → 0⁺`, `(B + ε•1)^(1-p) → B^(1-p)` by continuity of the
continuous functional calculus (`Filter.Tendsto.cfc`), so `g_ε → g`
pointwise. The set of concave functions is closed under pointwise
limits (`isClosed_concaveOn` in `CStarLogConcave.lean`), so the
limit `g` is concave. -/
theorem lieb_concavity_complementary_strictPos_A_PSD_B
    (K : Matrix n n ℂ) {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    ConcaveOn ℝ
      {z : Matrix n n ℂ × Matrix n n ℂ |
        IsStrictlyPositive z.1 ∧ z.2.PosSemidef}
      (fun z =>
        (Matrix.trace
            (star K * (z.1 ^ p) * K * (z.2 ^ ((1 : ℝ) - p)))).re) := by
  -- The target domain and the target functional, named for clarity.
  set s : Set (Matrix n n ℂ × Matrix n n ℂ) :=
    {z | IsStrictlyPositive z.1 ∧ z.2.PosSemidef} with hs_def
  set g : Matrix n n ℂ × Matrix n n ℂ → ℝ := fun z =>
    (Matrix.trace (star K * (z.1 ^ p) * K * (z.2 ^ ((1 : ℝ) - p)))).re
    with hg_def
  -- The perturbed family.
  let g_eps : ℝ → Matrix n n ℂ × Matrix n n ℂ → ℝ := fun ε z =>
    (Matrix.trace
        (star K * (z.1 ^ p) * K *
          ((z.2 + ε • (1 : Matrix n n ℂ)) ^ ((1 : ℝ) - p)))).re
  -- Step 1: convexity of `s`.
  have hs_conv : Convex ℝ s := by
    intro z₁ hz₁ z₂ hz₂ t u ht hu htu
    simp only [hs_def, Set.mem_setOf_eq] at hz₁ hz₂ ⊢
    obtain ⟨hA₁, hB₁⟩ := hz₁
    obtain ⟨hA₂, hB₂⟩ := hz₂
    refine ⟨?_, ?_⟩
    · -- `t • A₁ + u • A₂` strictly positive.
      exact convex_setOf_isStrictlyPositive_matrix (n := n)
        hA₁ hA₂ ht hu htu
    · -- `t • B₁ + u • B₂` PSD.
      exact (hB₁.smul ht).add (hB₂.smul hu)
  -- Step 2: for each `ε > 0`, `g_eps ε` is concave on `s`.
  have h_eps_concave : ∀ ε : ℝ, 0 < ε → ConcaveOn ℝ s (g_eps ε) := by
    intro ε hε
    refine ⟨hs_conv, ?_⟩
    rintro ⟨A₁, B₁⟩ hz₁ ⟨A₂, B₂⟩ hz₂ t u ht hu htu
    simp only [hs_def, Set.mem_setOf_eq] at hz₁ hz₂
    obtain ⟨hA₁, hB₁⟩ := hz₁
    obtain ⟨hA₂, hB₂⟩ := hz₂
    -- Each `Bᵢ + ε • 1` is strictly positive.
    have hε1 : (ε • (1 : Matrix n n ℂ)).PosDef := Matrix.PosDef.one.smul hε
    have hB₁ε_pd : (B₁ + ε • (1 : Matrix n n ℂ)).PosDef :=
      Matrix.PosDef.posSemidef_add hB₁ hε1
    have hB₂ε_pd : (B₂ + ε • (1 : Matrix n n ℂ)).PosDef :=
      Matrix.PosDef.posSemidef_add hB₂ hε1
    have hB₁ε_sp : IsStrictlyPositive (B₁ + ε • (1 : Matrix n n ℂ)) :=
      Matrix.isStrictlyPositive_iff_posDef.mpr hB₁ε_pd
    have hB₂ε_sp : IsStrictlyPositive (B₂ + ε • (1 : Matrix n n ℂ)) :=
      Matrix.isStrictlyPositive_iff_posDef.mpr hB₂ε_pd
    -- Apply the strict-positive theorem to the perturbed inputs.
    have hstrict := (lieb_concavity_complementary_strictPos
      (n := n) K hp).2
      (x := (A₁, B₁ + ε • (1 : Matrix n n ℂ)))
      (y := (A₂, B₂ + ε • (1 : Matrix n n ℂ)))
      ⟨hA₁, hB₁ε_sp⟩ ⟨hA₂, hB₂ε_sp⟩ ht hu htu
    -- Repackage `t • B₁ + u • B₂ + ε • 1 = t • (B₁ + ε•1) + u • (B₂ + ε•1)`.
    have hcombine : t • B₁ + u • B₂ + ε • (1 : Matrix n n ℂ)
                  = t • (B₁ + ε • (1 : Matrix n n ℂ))
                    + u • (B₂ + ε • (1 : Matrix n n ℂ)) := by
      have heq : ε • (1 : Matrix n n ℂ)
                = t • (ε • (1 : Matrix n n ℂ))
                  + u • (ε • (1 : Matrix n n ℂ)) := by
        have hsplit : (t + u) • (ε • (1 : Matrix n n ℂ))
                    = t • (ε • (1 : Matrix n n ℂ))
                      + u • (ε • (1 : Matrix n n ℂ)) := add_smul t u _
        rw [htu, one_smul] at hsplit
        exact hsplit
      rw [smul_add, smul_add]
      rw [show t • B₁ + t • (ε • (1 : Matrix n n ℂ))
            + (u • B₂ + u • (ε • (1 : Matrix n n ℂ)))
            = t • B₁ + u • B₂ + (t • (ε • (1 : Matrix n n ℂ))
              + u • (ε • (1 : Matrix n n ℂ))) from by abel]
      rw [← heq]
    show t • g_eps ε (A₁, B₁) + u • g_eps ε (A₂, B₂) ≤ g_eps ε _
    simp only [g_eps, Prod.smul_mk, Prod.mk_add_mk] at hstrict ⊢
    rw [hcombine]
    exact hstrict
  -- Step 3: `g_eps ε z → g z` as `ε → 0⁺`, for each `z ∈ s`.
  have h_tendsto_at : ∀ z ∈ s,
      Filter.Tendsto (fun ε : ℝ => g_eps ε z) (𝓝[>] (0 : ℝ)) (𝓝 (g z)) := by
    intro z hz
    obtain ⟨hA, hB⟩ := hz
    -- The key continuity: `(B + ε • 1)^(1-p) → B^(1-p)`.
    have hB_nonneg : (0 : Matrix n n ℂ) ≤ z.2 :=
      Matrix.nonneg_iff_posSemidef.mpr hB
    -- Spectrum bound: use a compact `Set ℝ` containing the spectra of all
    -- `B + ε • 1` for `ε ∈ (0, 1]`, and of `B` itself.
    -- For `r ∈ spectrum (B + ε•1)`, `|r| ≤ ‖B + ε•1‖ * ‖1‖ ≤ (‖B‖ + ‖1‖) * ‖1‖`
    -- (when `ε ≤ 1`), so we use `R := (‖B‖ + ‖1‖) * ‖1‖ + 1`.
    let R : ℝ := (‖z.2‖ + ‖(1 : Matrix n n ℂ)‖) * ‖(1 : Matrix n n ℂ)‖ + 1
    let s_spec : Set ℝ := Set.Icc 0 R
    have hs_spec_compact : IsCompact s_spec := isCompact_Icc
    have hq_cont : ContinuousOn (fun x : ℝ => x ^ ((1 : ℝ) - p)) s_spec := by
      intro x hx
      exact (Real.continuousAt_rpow_const x ((1 : ℝ) - p)
        (Or.inr (sub_nonneg.mpr hp.2))).continuousWithinAt
    -- Convergence: `B + ε • 1 → B` as `ε → 0`.
    have h_add_tendsto : Filter.Tendsto
        (fun ε : ℝ => z.2 + ε • (1 : Matrix n n ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 z.2) := by
      have h_smul_cont : Continuous (fun ε : ℝ => ε • (1 : Matrix n n ℂ)) := by
        exact continuous_id.smul continuous_const
      have h1 : Filter.Tendsto (fun ε : ℝ => ε • (1 : Matrix n n ℂ))
          (𝓝 (0 : ℝ)) (𝓝 (0 : Matrix n n ℂ)) := by
        have := h_smul_cont.tendsto (0 : ℝ)
        simpa using this
      have h2 : Filter.Tendsto (fun ε : ℝ => z.2 + ε • (1 : Matrix n n ℂ))
          (𝓝 (0 : ℝ)) (𝓝 z.2) := by
        have h := (tendsto_const_nhds (x := z.2) (f := 𝓝 (0 : ℝ))).add h1
        simpa using h
      exact h2.mono_left nhdsWithin_le_nhds
    -- Eventually (for `ε ∈ (0, 1]`), the spectrum of `B + ε • 1` is in `s_spec`.
    have h_eventually_spec : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        spectrum ℝ (z.2 + ε • (1 : Matrix n n ℂ)) ⊆ s_spec := by
      have hbasis := nhdsGT_basis (0 : ℝ) |>.mem_of_mem (zero_lt_one' ℝ)
      filter_upwards [hbasis] with ε ⟨hε_pos, hε_lt⟩
      intro r hr
      -- spectrum is in `[0, ‖B + ε•1‖] ⊆ [0, ‖B‖ + ε] ⊆ [0, R]`.
      have hBε_pd : (z.2 + ε • (1 : Matrix n n ℂ)).PosDef :=
        Matrix.PosDef.posSemidef_add hB (Matrix.PosDef.one.smul hε_pos)
      have hBε_psd : (z.2 + ε • (1 : Matrix n n ℂ)).PosSemidef :=
        hBε_pd.posSemidef
      have hBε_sp : IsStrictlyPositive (z.2 + ε • (1 : Matrix n n ℂ)) :=
        Matrix.isStrictlyPositive_iff_posDef.mpr hBε_pd
      have hBε_nonneg : (0 : Matrix n n ℂ) ≤ z.2 + ε • (1 : Matrix n n ℂ) :=
        hBε_sp.nonneg
      have hr_nonneg : (0 : ℝ) ≤ r := by
        have := StarOrderedRing.nonneg_iff_spectrum_nonneg
          (R := ℝ) (z.2 + ε • (1 : Matrix n n ℂ)) |>.mp hBε_nonneg
        exact this r hr
      have hr_norm_mul : ‖r‖ ≤ ‖z.2 + ε • (1 : Matrix n n ℂ)‖ * ‖(1 : Matrix n n ℂ)‖ :=
        spectrum.norm_le_norm_mul_of_mem hr
      have h_one_nn : (0 : ℝ) ≤ ‖(1 : Matrix n n ℂ)‖ := norm_nonneg _
      have hB_nn : (0 : ℝ) ≤ ‖z.2‖ := norm_nonneg _
      -- `‖z.2 + ε • 1‖ ≤ ‖z.2‖ + ‖1‖` (since ε ≤ 1).
      have hadd_norm : ‖z.2 + ε • (1 : Matrix n n ℂ)‖
                      ≤ ‖z.2‖ + ‖(1 : Matrix n n ℂ)‖ := by
        have h1 : ‖z.2 + ε • (1 : Matrix n n ℂ)‖
                  ≤ ‖z.2‖ + ‖ε • (1 : Matrix n n ℂ)‖ := norm_add_le _ _
        have h2 : ‖ε • (1 : Matrix n n ℂ)‖ ≤ ‖(1 : Matrix n n ℂ)‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε_pos]
          nlinarith
        linarith
      have hr_abs : r ≤ ‖z.2 + ε • (1 : Matrix n n ℂ)‖ * ‖(1 : Matrix n n ℂ)‖ := by
        have := Real.le_norm_self r
        linarith
      have hbound :
          ‖z.2 + ε • (1 : Matrix n n ℂ)‖ * ‖(1 : Matrix n n ℂ)‖
            ≤ (‖z.2‖ + ‖(1 : Matrix n n ℂ)‖) * ‖(1 : Matrix n n ℂ)‖ := by
        exact mul_le_mul_of_nonneg_right hadd_norm h_one_nn
      exact ⟨hr_nonneg, by show r ≤ R; linarith⟩
    -- Eventually `(B + ε•1)` is selfadjoint / nonneg.
    have h_eventually_nn : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        IsSelfAdjoint (z.2 + ε • (1 : Matrix n n ℂ)) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε_pos
      have hBε_pd : (z.2 + ε • (1 : Matrix n n ℂ)).PosDef :=
        Matrix.PosDef.posSemidef_add hB (Matrix.PosDef.one.smul hε_pos)
      exact (Matrix.isStrictlyPositive_iff_posDef.mpr hBε_pd).isSelfAdjoint
    -- Spectrum of B itself is in s_spec.
    have hB_spec : spectrum ℝ z.2 ⊆ s_spec := by
      intro r hr
      have hr_nonneg : (0 : ℝ) ≤ r :=
        (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) z.2).mp
          hB_nonneg r hr
      have hr_norm_mul : ‖r‖ ≤ ‖z.2‖ * ‖(1 : Matrix n n ℂ)‖ :=
        spectrum.norm_le_norm_mul_of_mem hr
      have h_one_nn : (0 : ℝ) ≤ ‖(1 : Matrix n n ℂ)‖ := norm_nonneg _
      have hB_nn : (0 : ℝ) ≤ ‖z.2‖ := norm_nonneg _
      have hr_abs : r ≤ ‖z.2‖ * ‖(1 : Matrix n n ℂ)‖ := by
        have := Real.le_norm_self r
        linarith
      have hbound : ‖z.2‖ * ‖(1 : Matrix n n ℂ)‖
                  ≤ (‖z.2‖ + ‖(1 : Matrix n n ℂ)‖) * ‖(1 : Matrix n n ℂ)‖ := by
        exact mul_le_mul_of_nonneg_right (by linarith) h_one_nn
      exact ⟨hr_nonneg, by show r ≤ R; linarith⟩
    -- Now apply `Filter.Tendsto.cfc`.
    have h_cfc_tendsto :
        Filter.Tendsto
          (fun ε : ℝ => cfc (fun x : ℝ => x ^ ((1 : ℝ) - p))
            (z.2 + ε • (1 : Matrix n n ℂ)))
          (𝓝[>] (0 : ℝ))
          (𝓝 (cfc (fun x : ℝ => x ^ ((1 : ℝ) - p)) z.2)) :=
      Filter.Tendsto.cfc (𝕜 := ℝ) hs_spec_compact
        (fun x : ℝ => x ^ ((1 : ℝ) - p))
        h_add_tendsto h_eventually_spec h_eventually_nn hB_spec
        hB_nonneg.isSelfAdjoint hq_cont
    -- Translate `cfc` back to `(·)^(1-p)`.
    have h_rpow_tendsto :
        Filter.Tendsto
          (fun ε : ℝ => (z.2 + ε • (1 : Matrix n n ℂ)) ^ ((1 : ℝ) - p))
          (𝓝[>] (0 : ℝ))
          (𝓝 (z.2 ^ ((1 : ℝ) - p))) := by
      have hreq : ∀ ε ∈ Set.Ioi (0 : ℝ),
          (z.2 + ε • (1 : Matrix n n ℂ)) ^ ((1 : ℝ) - p)
            = cfc (fun x : ℝ => x ^ ((1 : ℝ) - p))
              (z.2 + ε • (1 : Matrix n n ℂ)) := by
        intro ε hε_pos
        have hBε_pd : (z.2 + ε • (1 : Matrix n n ℂ)).PosDef :=
          Matrix.PosDef.posSemidef_add hB (Matrix.PosDef.one.smul hε_pos)
        have hBε_nonneg : (0 : Matrix n n ℂ) ≤ z.2 + ε • (1 : Matrix n n ℂ) :=
          (Matrix.isStrictlyPositive_iff_posDef.mpr hBε_pd).nonneg
        exact CFC.rpow_eq_cfc_real (a := z.2 + ε • (1 : Matrix n n ℂ))
          (y := (1 : ℝ) - p) hBε_nonneg
      have hreqB : z.2 ^ ((1 : ℝ) - p)
                  = cfc (fun x : ℝ => x ^ ((1 : ℝ) - p)) z.2 :=
        CFC.rpow_eq_cfc_real hB_nonneg
      have := h_cfc_tendsto
      rw [← hreqB] at this
      -- Use `Tendsto.congr'` with frequent equality on `𝓝[>] 0`.
      apply this.congr'
      filter_upwards [self_mem_nhdsWithin] with ε hε_pos
      exact (hreq ε hε_pos).symm
    -- Now combine via trace continuity.
    -- Define `h : Matrix n n ℂ → ℂ` continuous (multiplication + trace).
    have hcont :
        Continuous (fun M : Matrix n n ℂ =>
          Matrix.trace (star K * (z.1 ^ p) * K * M)) := by
      have h_const : Continuous (fun _ : Matrix n n ℂ =>
        star K * (z.1 ^ p) * K) := continuous_const
      have h_mul : Continuous (fun M : Matrix n n ℂ =>
        star K * (z.1 ^ p) * K * M) := h_const.mul continuous_id
      exact h_mul.matrix_trace
    -- Conclude by composing tendsto.
    have h_full :
        Filter.Tendsto
          (fun ε : ℝ =>
            Matrix.trace (star K * (z.1 ^ p) * K *
              ((z.2 + ε • (1 : Matrix n n ℂ)) ^ ((1 : ℝ) - p))))
          (𝓝[>] (0 : ℝ))
          (𝓝 (Matrix.trace (star K * (z.1 ^ p) * K * (z.2 ^ ((1 : ℝ) - p))))) :=
      (hcont.tendsto _).comp h_rpow_tendsto
    exact (Complex.continuous_re.tendsto _).comp h_full
  -- Step 4: Apply `isClosed_concaveOn` via pointwise convergence.
  -- We construct extended-to-everywhere functions:
  --   f_eps ε z := if z ∈ s then g_eps ε z else 0
  --   g_ext z   := if z ∈ s then g z else 0
  classical
  let f_eps : ℝ → Matrix n n ℂ × Matrix n n ℂ → ℝ :=
    fun ε z => if z ∈ s then g_eps ε z else 0
  let g_ext : Matrix n n ℂ × Matrix n n ℂ → ℝ :=
    fun z => if z ∈ s then g z else 0
  have hg_ext_eq : s.EqOn g_ext g := by
    intro z hz
    show (if z ∈ s then g z else 0) = g z
    simp [hz]
  refine ConcaveOn.congr ?_ hg_ext_eq
  -- Each `f_eps ε` is concave on `s`.
  have h_f_concave : ∀ ε : ℝ, 0 < ε → ConcaveOn ℝ s (f_eps ε) := by
    intro ε hε
    have h := h_eps_concave ε hε
    refine h.congr ?_
    intro z hz
    show g_eps ε z = (if z ∈ s then g_eps ε z else 0)
    simp [hz]
  -- Pointwise convergence `f_eps ε → g_ext` as `ε → 0⁺`.
  have h_tendsto : Filter.Tendsto f_eps (𝓝[>] (0 : ℝ)) (𝓝 g_ext) := by
    rw [tendsto_pi_nhds]
    intro z
    by_cases hz : z ∈ s
    · have h_tn := h_tendsto_at z hz
      have h_eq : ∀ ε ∈ Set.Ioi (0 : ℝ), f_eps ε z = g_eps ε z := by
        intro ε _
        show (if z ∈ s then g_eps ε z else 0) = g_eps ε z
        simp [hz]
      have hg_z : g_ext z = g z := by
        show (if z ∈ s then g z else 0) = g z
        simp [hz]
      rw [hg_z]
      apply h_tn.congr'
      filter_upwards [self_mem_nhdsWithin] with ε hε_pos
      exact (h_eq ε hε_pos).symm
    · have h_const : ∀ ε, f_eps ε z = 0 := by
        intro ε
        show (if z ∈ s then g_eps ε z else 0) = 0
        simp [hz]
      have hg_z : g_ext z = 0 := by
        show (if z ∈ s then g z else 0) = 0
        simp [hz]
      rw [hg_z]
      simp only [h_const]
      exact tendsto_const_nhds
  -- Closedness of concavity.
  have h_closed :
      IsClosed {h : Matrix n n ℂ × Matrix n n ℂ → ℝ | ConcaveOn ℝ s h} :=
    LTFP.MathlibExt.MatrixAnalysis.isClosed_concaveOn
      (E := Matrix n n ℂ × Matrix n n ℂ) (β := ℝ) hs_conv
  -- Eventually, `f_eps ε` is concave (specifically for `ε > 0`).
  have h_eventually : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      f_eps ε ∈ {h : Matrix n n ℂ × Matrix n n ℂ → ℝ | ConcaveOn ℝ s h} := by
    filter_upwards [self_mem_nhdsWithin] with ε hε_pos
    exact h_f_concave ε hε_pos
  exact h_closed.mem_of_tendsto h_tendsto h_eventually

/-! ### Extension B: relax both arguments to PosSemidef -/

/-- **Complementary Lieb concavity (full PSD boundary, B6 L3 Sub-Part 7.5b).**

For any matrix `K` and any `p ∈ [0, 1]`, the bilinear-quadratic functional

```
(A, B) ↦ Re Tr(K* · A^p · K · B^(1-p))
```

is jointly concave on the **full PSD × PSD cone** of pairs of positive
semidefinite matrices.

This is **Extension B** of `lieb_concavity_complementary_strictPos_A_PSD_B`
(Sub-Part 7.5): the strict-positive requirement on the *first* argument
is relaxed to merely `PosSemidef` via a symmetric ε-regularization
argument applied to `A`.

**Proof.**  For each `ε > 0`, the perturbed map

```
g_ε (A, B) := Re Tr(K* · (A + ε•1)^p · K · B^(1-p))
```

is concave on `{(A, B) | A PSD ∧ B PSD}`, because:

* `A + ε•1` is strictly positive whenever `A` is PSD (sum of PSD and
  PosDef is PosDef);
* The convex combination distributes `ε•1` correctly via `t + u = 1`;
* The PSD-B theorem `lieb_concavity_complementary_strictPos_A_PSD_B`
  then applies to give the concavity inequality on the perturbed inputs.

As `ε → 0⁺`, `(A + ε•1)^p → A^p` by continuity of the continuous
functional calculus (`Filter.Tendsto.cfc`), so `g_ε → g` pointwise. The
set of concave functions is closed under pointwise limits
(`isClosed_concaveOn`), so the limit `g` is concave. -/
theorem lieb_concavity_complementary_PSD
    (K : Matrix n n ℂ) {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    ConcaveOn ℝ
      {z : Matrix n n ℂ × Matrix n n ℂ |
        z.1.PosSemidef ∧ z.2.PosSemidef}
      (fun z =>
        (Matrix.trace
            (star K * (z.1 ^ p) * K * (z.2 ^ ((1 : ℝ) - p)))).re) := by
  -- The target domain and the target functional.
  set s : Set (Matrix n n ℂ × Matrix n n ℂ) :=
    {z | z.1.PosSemidef ∧ z.2.PosSemidef} with hs_def
  set g : Matrix n n ℂ × Matrix n n ℂ → ℝ := fun z =>
    (Matrix.trace (star K * (z.1 ^ p) * K * (z.2 ^ ((1 : ℝ) - p)))).re
    with hg_def
  -- The perturbed family: regularize the first coordinate `A`.
  let g_eps : ℝ → Matrix n n ℂ × Matrix n n ℂ → ℝ := fun ε z =>
    (Matrix.trace
        (star K * ((z.1 + ε • (1 : Matrix n n ℂ)) ^ p) * K *
          (z.2 ^ ((1 : ℝ) - p)))).re
  -- Step 1: convexity of `s`.
  have hs_conv : Convex ℝ s := by
    intro z₁ hz₁ z₂ hz₂ t u ht hu htu
    simp only [hs_def, Set.mem_setOf_eq] at hz₁ hz₂ ⊢
    obtain ⟨hA₁, hB₁⟩ := hz₁
    obtain ⟨hA₂, hB₂⟩ := hz₂
    exact ⟨(hA₁.smul ht).add (hA₂.smul hu), (hB₁.smul ht).add (hB₂.smul hu)⟩
  -- Step 2: for each `ε > 0`, `g_eps ε` is concave on `s`.
  have h_eps_concave : ∀ ε : ℝ, 0 < ε → ConcaveOn ℝ s (g_eps ε) := by
    intro ε hε
    refine ⟨hs_conv, ?_⟩
    rintro ⟨A₁, B₁⟩ hz₁ ⟨A₂, B₂⟩ hz₂ t u ht hu htu
    simp only [hs_def, Set.mem_setOf_eq] at hz₁ hz₂
    obtain ⟨hA₁, hB₁⟩ := hz₁
    obtain ⟨hA₂, hB₂⟩ := hz₂
    -- Each `Aᵢ + ε • 1` is strictly positive.
    have hε1 : (ε • (1 : Matrix n n ℂ)).PosDef := Matrix.PosDef.one.smul hε
    have hA₁ε_pd : (A₁ + ε • (1 : Matrix n n ℂ)).PosDef :=
      Matrix.PosDef.posSemidef_add hA₁ hε1
    have hA₂ε_pd : (A₂ + ε • (1 : Matrix n n ℂ)).PosDef :=
      Matrix.PosDef.posSemidef_add hA₂ hε1
    have hA₁ε_sp : IsStrictlyPositive (A₁ + ε • (1 : Matrix n n ℂ)) :=
      Matrix.isStrictlyPositive_iff_posDef.mpr hA₁ε_pd
    have hA₂ε_sp : IsStrictlyPositive (A₂ + ε • (1 : Matrix n n ℂ)) :=
      Matrix.isStrictlyPositive_iff_posDef.mpr hA₂ε_pd
    -- Apply the PSD-B theorem to the perturbed inputs.
    have hstrict := (lieb_concavity_complementary_strictPos_A_PSD_B
      (n := n) K hp).2
      (x := (A₁ + ε • (1 : Matrix n n ℂ), B₁))
      (y := (A₂ + ε • (1 : Matrix n n ℂ), B₂))
      ⟨hA₁ε_sp, hB₁⟩ ⟨hA₂ε_sp, hB₂⟩ ht hu htu
    -- Repackage `t • A₁ + u • A₂ + ε • 1 = t • (A₁ + ε•1) + u • (A₂ + ε•1)`.
    have hcombine : t • A₁ + u • A₂ + ε • (1 : Matrix n n ℂ)
                  = t • (A₁ + ε • (1 : Matrix n n ℂ))
                    + u • (A₂ + ε • (1 : Matrix n n ℂ)) := by
      have heq : ε • (1 : Matrix n n ℂ)
                = t • (ε • (1 : Matrix n n ℂ))
                  + u • (ε • (1 : Matrix n n ℂ)) := by
        have hsplit : (t + u) • (ε • (1 : Matrix n n ℂ))
                    = t • (ε • (1 : Matrix n n ℂ))
                      + u • (ε • (1 : Matrix n n ℂ)) := add_smul t u _
        rw [htu, one_smul] at hsplit
        exact hsplit
      rw [smul_add, smul_add]
      rw [show t • A₁ + t • (ε • (1 : Matrix n n ℂ))
            + (u • A₂ + u • (ε • (1 : Matrix n n ℂ)))
            = t • A₁ + u • A₂ + (t • (ε • (1 : Matrix n n ℂ))
              + u • (ε • (1 : Matrix n n ℂ))) from by abel]
      rw [← heq]
    show t • g_eps ε (A₁, B₁) + u • g_eps ε (A₂, B₂) ≤ g_eps ε _
    simp only [g_eps, Prod.smul_mk, Prod.mk_add_mk] at hstrict ⊢
    rw [hcombine]
    exact hstrict
  -- Step 3: `g_eps ε z → g z` as `ε → 0⁺`, for each `z ∈ s`.
  have h_tendsto_at : ∀ z ∈ s,
      Filter.Tendsto (fun ε : ℝ => g_eps ε z) (𝓝[>] (0 : ℝ)) (𝓝 (g z)) := by
    intro z hz
    obtain ⟨hA, hB⟩ := hz
    -- The key continuity: `(A + ε • 1)^p → A^p`.
    have hA_nonneg : (0 : Matrix n n ℂ) ≤ z.1 :=
      Matrix.nonneg_iff_posSemidef.mpr hA
    -- Spectrum bound: compact `Set ℝ` containing spectra of `A + ε • 1`
    -- for `ε ∈ (0, 1]` and of `A` itself.
    let R : ℝ := (‖z.1‖ + ‖(1 : Matrix n n ℂ)‖) * ‖(1 : Matrix n n ℂ)‖ + 1
    let s_spec : Set ℝ := Set.Icc 0 R
    have hs_spec_compact : IsCompact s_spec := isCompact_Icc
    have hq_cont : ContinuousOn (fun x : ℝ => x ^ p) s_spec := by
      intro x hx
      exact (Real.continuousAt_rpow_const x p
        (Or.inr hp.1)).continuousWithinAt
    -- Convergence: `A + ε • 1 → A` as `ε → 0`.
    have h_add_tendsto : Filter.Tendsto
        (fun ε : ℝ => z.1 + ε • (1 : Matrix n n ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 z.1) := by
      have h_smul_cont : Continuous (fun ε : ℝ => ε • (1 : Matrix n n ℂ)) := by
        exact continuous_id.smul continuous_const
      have h1 : Filter.Tendsto (fun ε : ℝ => ε • (1 : Matrix n n ℂ))
          (𝓝 (0 : ℝ)) (𝓝 (0 : Matrix n n ℂ)) := by
        have := h_smul_cont.tendsto (0 : ℝ)
        simpa using this
      have h2 : Filter.Tendsto (fun ε : ℝ => z.1 + ε • (1 : Matrix n n ℂ))
          (𝓝 (0 : ℝ)) (𝓝 z.1) := by
        have h := (tendsto_const_nhds (x := z.1) (f := 𝓝 (0 : ℝ))).add h1
        simpa using h
      exact h2.mono_left nhdsWithin_le_nhds
    -- Eventually (for `ε ∈ (0, 1]`), the spectrum of `A + ε • 1` is in `s_spec`.
    have h_eventually_spec : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        spectrum ℝ (z.1 + ε • (1 : Matrix n n ℂ)) ⊆ s_spec := by
      have hbasis := nhdsGT_basis (0 : ℝ) |>.mem_of_mem (zero_lt_one' ℝ)
      filter_upwards [hbasis] with ε ⟨hε_pos, hε_lt⟩
      intro r hr
      have hAε_pd : (z.1 + ε • (1 : Matrix n n ℂ)).PosDef :=
        Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.one.smul hε_pos)
      have hAε_psd : (z.1 + ε • (1 : Matrix n n ℂ)).PosSemidef :=
        hAε_pd.posSemidef
      have hAε_sp : IsStrictlyPositive (z.1 + ε • (1 : Matrix n n ℂ)) :=
        Matrix.isStrictlyPositive_iff_posDef.mpr hAε_pd
      have hAε_nonneg : (0 : Matrix n n ℂ) ≤ z.1 + ε • (1 : Matrix n n ℂ) :=
        hAε_sp.nonneg
      have hr_nonneg : (0 : ℝ) ≤ r := by
        have := StarOrderedRing.nonneg_iff_spectrum_nonneg
          (R := ℝ) (z.1 + ε • (1 : Matrix n n ℂ)) |>.mp hAε_nonneg
        exact this r hr
      have hr_norm_mul : ‖r‖ ≤ ‖z.1 + ε • (1 : Matrix n n ℂ)‖ * ‖(1 : Matrix n n ℂ)‖ :=
        spectrum.norm_le_norm_mul_of_mem hr
      have h_one_nn : (0 : ℝ) ≤ ‖(1 : Matrix n n ℂ)‖ := norm_nonneg _
      have hA_nn : (0 : ℝ) ≤ ‖z.1‖ := norm_nonneg _
      have hadd_norm : ‖z.1 + ε • (1 : Matrix n n ℂ)‖
                      ≤ ‖z.1‖ + ‖(1 : Matrix n n ℂ)‖ := by
        have h1 : ‖z.1 + ε • (1 : Matrix n n ℂ)‖
                  ≤ ‖z.1‖ + ‖ε • (1 : Matrix n n ℂ)‖ := norm_add_le _ _
        have h2 : ‖ε • (1 : Matrix n n ℂ)‖ ≤ ‖(1 : Matrix n n ℂ)‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε_pos]
          nlinarith
        linarith
      have hr_abs : r ≤ ‖z.1 + ε • (1 : Matrix n n ℂ)‖ * ‖(1 : Matrix n n ℂ)‖ := by
        have := Real.le_norm_self r
        linarith
      have hbound :
          ‖z.1 + ε • (1 : Matrix n n ℂ)‖ * ‖(1 : Matrix n n ℂ)‖
            ≤ (‖z.1‖ + ‖(1 : Matrix n n ℂ)‖) * ‖(1 : Matrix n n ℂ)‖ := by
        exact mul_le_mul_of_nonneg_right hadd_norm h_one_nn
      exact ⟨hr_nonneg, by show r ≤ R; linarith⟩
    -- Eventually `(A + ε•1)` is selfadjoint.
    have h_eventually_nn : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        IsSelfAdjoint (z.1 + ε • (1 : Matrix n n ℂ)) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε_pos
      have hAε_pd : (z.1 + ε • (1 : Matrix n n ℂ)).PosDef :=
        Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.one.smul hε_pos)
      exact (Matrix.isStrictlyPositive_iff_posDef.mpr hAε_pd).isSelfAdjoint
    -- Spectrum of A itself is in s_spec.
    have hA_spec : spectrum ℝ z.1 ⊆ s_spec := by
      intro r hr
      have hr_nonneg : (0 : ℝ) ≤ r :=
        (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) z.1).mp
          hA_nonneg r hr
      have hr_norm_mul : ‖r‖ ≤ ‖z.1‖ * ‖(1 : Matrix n n ℂ)‖ :=
        spectrum.norm_le_norm_mul_of_mem hr
      have h_one_nn : (0 : ℝ) ≤ ‖(1 : Matrix n n ℂ)‖ := norm_nonneg _
      have hA_nn : (0 : ℝ) ≤ ‖z.1‖ := norm_nonneg _
      have hr_abs : r ≤ ‖z.1‖ * ‖(1 : Matrix n n ℂ)‖ := by
        have := Real.le_norm_self r
        linarith
      have hbound : ‖z.1‖ * ‖(1 : Matrix n n ℂ)‖
                  ≤ (‖z.1‖ + ‖(1 : Matrix n n ℂ)‖) * ‖(1 : Matrix n n ℂ)‖ := by
        exact mul_le_mul_of_nonneg_right (by linarith) h_one_nn
      exact ⟨hr_nonneg, by show r ≤ R; linarith⟩
    -- Now apply `Filter.Tendsto.cfc`.
    have h_cfc_tendsto :
        Filter.Tendsto
          (fun ε : ℝ => cfc (fun x : ℝ => x ^ p)
            (z.1 + ε • (1 : Matrix n n ℂ)))
          (𝓝[>] (0 : ℝ))
          (𝓝 (cfc (fun x : ℝ => x ^ p) z.1)) :=
      Filter.Tendsto.cfc (𝕜 := ℝ) hs_spec_compact
        (fun x : ℝ => x ^ p)
        h_add_tendsto h_eventually_spec h_eventually_nn hA_spec
        hA_nonneg.isSelfAdjoint hq_cont
    -- Translate `cfc` back to `(·)^p`.
    have h_rpow_tendsto :
        Filter.Tendsto
          (fun ε : ℝ => (z.1 + ε • (1 : Matrix n n ℂ)) ^ p)
          (𝓝[>] (0 : ℝ))
          (𝓝 (z.1 ^ p)) := by
      have hreq : ∀ ε ∈ Set.Ioi (0 : ℝ),
          (z.1 + ε • (1 : Matrix n n ℂ)) ^ p
            = cfc (fun x : ℝ => x ^ p)
              (z.1 + ε • (1 : Matrix n n ℂ)) := by
        intro ε hε_pos
        have hAε_pd : (z.1 + ε • (1 : Matrix n n ℂ)).PosDef :=
          Matrix.PosDef.posSemidef_add hA (Matrix.PosDef.one.smul hε_pos)
        have hAε_nonneg : (0 : Matrix n n ℂ) ≤ z.1 + ε • (1 : Matrix n n ℂ) :=
          (Matrix.isStrictlyPositive_iff_posDef.mpr hAε_pd).nonneg
        exact CFC.rpow_eq_cfc_real (a := z.1 + ε • (1 : Matrix n n ℂ))
          (y := p) hAε_nonneg
      have hreqA : z.1 ^ p
                  = cfc (fun x : ℝ => x ^ p) z.1 :=
        CFC.rpow_eq_cfc_real hA_nonneg
      have := h_cfc_tendsto
      rw [← hreqA] at this
      apply this.congr'
      filter_upwards [self_mem_nhdsWithin] with ε hε_pos
      exact (hreq ε hε_pos).symm
    -- Now combine via trace continuity.
    -- The continuous function in M is `M ↦ Tr(star K * M * K * z.2^(1-p))`.
    have hcont :
        Continuous (fun M : Matrix n n ℂ =>
          Matrix.trace (star K * M * K * (z.2 ^ ((1 : ℝ) - p)))) := by
      have h_left : Continuous (fun M : Matrix n n ℂ => star K * M) :=
        continuous_const.mul continuous_id
      have h_then_K : Continuous (fun M : Matrix n n ℂ => star K * M * K) :=
        h_left.mul continuous_const
      have h_full_mul : Continuous (fun M : Matrix n n ℂ =>
        star K * M * K * (z.2 ^ ((1 : ℝ) - p))) :=
        h_then_K.mul continuous_const
      exact h_full_mul.matrix_trace
    -- Conclude by composing tendsto.
    have h_full :
        Filter.Tendsto
          (fun ε : ℝ =>
            Matrix.trace (star K * ((z.1 + ε • (1 : Matrix n n ℂ)) ^ p) * K *
              (z.2 ^ ((1 : ℝ) - p))))
          (𝓝[>] (0 : ℝ))
          (𝓝 (Matrix.trace (star K * (z.1 ^ p) * K * (z.2 ^ ((1 : ℝ) - p))))) :=
      (hcont.tendsto _).comp h_rpow_tendsto
    exact (Complex.continuous_re.tendsto _).comp h_full
  -- Step 4: Apply `isClosed_concaveOn` via pointwise convergence.
  classical
  let f_eps : ℝ → Matrix n n ℂ × Matrix n n ℂ → ℝ :=
    fun ε z => if z ∈ s then g_eps ε z else 0
  let g_ext : Matrix n n ℂ × Matrix n n ℂ → ℝ :=
    fun z => if z ∈ s then g z else 0
  have hg_ext_eq : s.EqOn g_ext g := by
    intro z hz
    show (if z ∈ s then g z else 0) = g z
    simp [hz]
  refine ConcaveOn.congr ?_ hg_ext_eq
  have h_f_concave : ∀ ε : ℝ, 0 < ε → ConcaveOn ℝ s (f_eps ε) := by
    intro ε hε
    have h := h_eps_concave ε hε
    refine h.congr ?_
    intro z hz
    show g_eps ε z = (if z ∈ s then g_eps ε z else 0)
    simp [hz]
  have h_tendsto : Filter.Tendsto f_eps (𝓝[>] (0 : ℝ)) (𝓝 g_ext) := by
    rw [tendsto_pi_nhds]
    intro z
    by_cases hz : z ∈ s
    · have h_tn := h_tendsto_at z hz
      have h_eq : ∀ ε ∈ Set.Ioi (0 : ℝ), f_eps ε z = g_eps ε z := by
        intro ε _
        show (if z ∈ s then g_eps ε z else 0) = g_eps ε z
        simp [hz]
      have hg_z : g_ext z = g z := by
        show (if z ∈ s then g z else 0) = g z
        simp [hz]
      rw [hg_z]
      apply h_tn.congr'
      filter_upwards [self_mem_nhdsWithin] with ε hε_pos
      exact (h_eq ε hε_pos).symm
    · have h_const : ∀ ε, f_eps ε z = 0 := by
        intro ε
        show (if z ∈ s then g_eps ε z else 0) = 0
        simp [hz]
      have hg_z : g_ext z = 0 := by
        show (if z ∈ s then g z else 0) = 0
        simp [hz]
      rw [hg_z]
      simp only [h_const]
      exact tendsto_const_nhds
  have h_closed :
      IsClosed {h : Matrix n n ℂ × Matrix n n ℂ → ℝ | ConcaveOn ℝ s h} :=
    LTFP.MathlibExt.MatrixAnalysis.isClosed_concaveOn
      (E := Matrix n n ℂ × Matrix n n ℂ) (β := ℝ) hs_conv
  have h_eventually : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      f_eps ε ∈ {h : Matrix n n ℂ × Matrix n n ℂ → ℝ | ConcaveOn ℝ s h} := by
    filter_upwards [self_mem_nhdsWithin] with ε hε_pos
    exact h_f_concave ε hε_pos
  exact h_closed.mem_of_tendsto h_tendsto h_eventually

/-! ### Sub-Part 7.6: Monotonicity of the complementary trace functional

For positive semidefinite `A₁ ≤ A₂` and `B₁ ≤ B₂` in the Löwner order,
the bilinear trace functional
`(A, B) ↦ Re Tr(K* · A^p · K · B^(1-p))` is monotonically nondecreasing
in both arguments. The proof telescopes through `F(A₁, B₂)` using the
Löwner-Heinz monotonicity of `x ↦ x^p` on `[0, 1]` (`CFC.rpow_le_rpow`)
and a small helper showing PSD × PSD trace has nonnegative real part. -/

/-- For two positive semidefinite complex matrices `P` and `Q`, the
trace of the product `P * Q` has nonnegative real part.

This is the classical fact that `tr(PQ) ≥ 0` for PSD `P, Q`. The proof
cycles `tr(P * Q) = tr(√Q * P * √Q)` and observes the right side is the
trace of a PSD matrix (`(√Q)ᴴ * P * √Q` with `√Q` selfadjoint). -/
lemma re_trace_mul_nonneg_of_posSemidef
    {n : Type*} [Fintype n] [DecidableEq n]
    {P Q : Matrix n n ℂ} (hP : P.PosSemidef) (hQ : Q.PosSemidef) :
    0 ≤ (Matrix.trace (P * Q)).re := by
  classical
  -- Let `S = √Q` (CFC square root of `Q`).
  set S : Matrix n n ℂ := CFC.sqrt Q with hS_def
  -- `S` is PSD, hence Hermitian; so `Sᴴ = S`, i.e. `star S = S`.
  have hS_psd : S.PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg Q)
  have hS_her : S.IsHermitian := hS_psd.isHermitian
  -- `S * S = Q`.
  have hSS : S * S = Q := CFC.sqrt_mul_sqrt_self Q
  -- Cycle the trace: `tr(P * Q) = tr(P * S * S) = tr(S * P * S)`.
  have hcyc :
      Matrix.trace (P * Q) = Matrix.trace (S * P * S) := by
    have h1 : P * Q = P * S * S := by
      rw [← hSS]; exact (Matrix.mul_assoc _ _ _).symm
    have h2 : Matrix.trace (P * S * S) = Matrix.trace (S * P * S) :=
      Matrix.trace_mul_cycle P S S
    rw [h1, h2]
  -- `S * P * S = Sᴴ * P * S` since `S` is Hermitian; this is PSD.
  have hSstar : Sᴴ = S := hS_her
  have hPSD : (S * P * S).PosSemidef := by
    have hKK : (Sᴴ * P * S).PosSemidef :=
      hP.conjTranspose_mul_mul_same S
    rwa [hSstar] at hKK
  -- `0 ≤ trace (S * P * S)` in `ℂ`, so its real part is `≥ 0`.
  have htr_nonneg : (0 : ℂ) ≤ Matrix.trace (S * P * S) :=
    hPSD.trace_nonneg
  have hre :
      0 ≤ (Matrix.trace (S * P * S)).re := (Complex.nonneg_iff.mp htr_nonneg).1
  rw [hcyc]
  exact hre

/-- **Sub-Part 7.6 (monotonicity of the complementary Lieb functional).**
For PSD `A₁ ≤ A₂` and `B₁ ≤ B₂` in the Loewner order, and `p ∈ [0, 1]`,
the trace functional
`(A, B) ↦ Re Tr(K* · A^p · K · B^(1-p))` is monotone nondecreasing.

Combined with `CFC.lieb_concavity_complementary_PSD`, this gives the
two structural properties (concavity + monotonicity) of the bilinear
form that drive the operator-convex / operator-concave packaging used
in downstream applications. -/
theorem lieb_complementary_monotone
    {n : Type*} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℂ) {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    {A₁ A₂ B₁ B₂ : Matrix n n ℂ}
    (hA₁ : A₁.PosSemidef) (hA₂ : A₂.PosSemidef)
    (hB₁ : B₁.PosSemidef) (hB₂ : B₂.PosSemidef)
    (hA : A₁ ≤ A₂) (hB : B₁ ≤ B₂) :
    (Matrix.trace (star K * (A₁ ^ p) * K * (B₁ ^ ((1 : ℝ) - p)))).re ≤
      (Matrix.trace (star K * (A₂ ^ p) * K * (B₂ ^ ((1 : ℝ) - p)))).re := by
  classical
  -- The PSD hypotheses on the corners are recorded in the signature for
  -- documentation; they are implied by `0 ≤ A_i` / `0 ≤ B_i` and not
  -- needed in the proof itself (`CFC.rpow_nonneg` is unconditional).
  let _ := hA₁; let _ := hA₂; let _ := hB₁; let _ := hB₂
  -- The exponents lie in [0, 1].
  have hp' : (1 : ℝ) - p ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨by linarith [hp.2], by linarith [hp.1]⟩
  -- PSD ⇒ rpow PSD (Löwner-Heinz).
  have hA₁p_psd : (A₁ ^ p).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp
      (CFC.rpow_nonneg (a := A₁) (y := p))
  have hA₂p_psd : (A₂ ^ p).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp
      (CFC.rpow_nonneg (a := A₂) (y := p))
  have hB₁q_psd : (B₁ ^ ((1 : ℝ) - p)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp
      (CFC.rpow_nonneg (a := B₁) (y := (1 : ℝ) - p))
  have hB₂q_psd : (B₂ ^ ((1 : ℝ) - p)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp
      (CFC.rpow_nonneg (a := B₂) (y := (1 : ℝ) - p))
  -- Löwner-Heinz monotonicity of `x ↦ x^p` on `[0, 1]`.
  have hApow : A₁ ^ p ≤ A₂ ^ p := CFC.rpow_le_rpow hp hA
  have hBpow : B₁ ^ ((1 : ℝ) - p) ≤ B₂ ^ ((1 : ℝ) - p) :=
    CFC.rpow_le_rpow hp' hB
  -- The PSD differences.
  have hDA_psd : (A₂ ^ p - A₁ ^ p).PosSemidef := Matrix.le_iff.mp hApow
  have hDB_psd : (B₂ ^ ((1 : ℝ) - p) - B₁ ^ ((1 : ℝ) - p)).PosSemidef :=
    Matrix.le_iff.mp hBpow
  -- `star K = Kᴴ`.
  have hstarK : (star K : Matrix n n ℂ) = Kᴴ := Matrix.star_eq_conjTranspose K
  -- The two "sandwich" PSD matrices.
  have hMid_A2 : (star K * (A₂ ^ p) * K).PosSemidef := by
    rw [hstarK]; exact hA₂p_psd.conjTranspose_mul_mul_same K
  have hMid_A1 : (star K * (A₁ ^ p) * K).PosSemidef := by
    rw [hstarK]; exact hA₁p_psd.conjTranspose_mul_mul_same K
  have hMid_dA : (star K * (A₂ ^ p - A₁ ^ p) * K).PosSemidef := by
    rw [hstarK]; exact hDA_psd.conjTranspose_mul_mul_same K
  -- Telescoping step A: `F(A₁, B₂) ≤ F(A₂, B₂)`.
  -- Difference: `Re tr (star K * (A₂^p - A₁^p) * K * B₂^(1-p))` ≥ 0.
  have hstepA :
      (Matrix.trace (star K * (A₁ ^ p) * K * (B₂ ^ ((1 : ℝ) - p)))).re ≤
        (Matrix.trace (star K * (A₂ ^ p) * K * (B₂ ^ ((1 : ℝ) - p)))).re := by
    -- Rearrange to a difference.
    have hsub :
        Matrix.trace (star K * (A₂ ^ p) * K * (B₂ ^ ((1 : ℝ) - p))) -
          Matrix.trace (star K * (A₁ ^ p) * K * (B₂ ^ ((1 : ℝ) - p))) =
        Matrix.trace ((star K * (A₂ ^ p - A₁ ^ p) * K) *
          (B₂ ^ ((1 : ℝ) - p))) := by
      rw [← Matrix.trace_sub]
      congr 1
      simp [sub_mul, mul_sub]
    have hnn :
        0 ≤ (Matrix.trace ((star K * (A₂ ^ p - A₁ ^ p) * K) *
              (B₂ ^ ((1 : ℝ) - p)))).re :=
      re_trace_mul_nonneg_of_posSemidef hMid_dA hB₂q_psd
    have hresub :
        (Matrix.trace (star K * (A₂ ^ p) * K * (B₂ ^ ((1 : ℝ) - p)))).re -
            (Matrix.trace (star K * (A₁ ^ p) * K *
              (B₂ ^ ((1 : ℝ) - p)))).re =
          (Matrix.trace ((star K * (A₂ ^ p - A₁ ^ p) * K) *
              (B₂ ^ ((1 : ℝ) - p)))).re := by
      rw [← Complex.sub_re, hsub]
    linarith [hresub ▸ hnn]
  -- Telescoping step B: `F(A₁, B₁) ≤ F(A₁, B₂)`.
  have hstepB :
      (Matrix.trace (star K * (A₁ ^ p) * K * (B₁ ^ ((1 : ℝ) - p)))).re ≤
        (Matrix.trace (star K * (A₁ ^ p) * K * (B₂ ^ ((1 : ℝ) - p)))).re := by
    have hsub :
        Matrix.trace (star K * (A₁ ^ p) * K * (B₂ ^ ((1 : ℝ) - p))) -
          Matrix.trace (star K * (A₁ ^ p) * K * (B₁ ^ ((1 : ℝ) - p))) =
        Matrix.trace ((star K * (A₁ ^ p) * K) *
          (B₂ ^ ((1 : ℝ) - p) - B₁ ^ ((1 : ℝ) - p))) := by
      rw [← Matrix.trace_sub]
      congr 1
      simp [mul_sub]
    have hnn :
        0 ≤ (Matrix.trace ((star K * (A₁ ^ p) * K) *
              (B₂ ^ ((1 : ℝ) - p) - B₁ ^ ((1 : ℝ) - p)))).re :=
      re_trace_mul_nonneg_of_posSemidef hMid_A1 hDB_psd
    have hresub :
        (Matrix.trace (star K * (A₁ ^ p) * K *
              (B₂ ^ ((1 : ℝ) - p)))).re -
            (Matrix.trace (star K * (A₁ ^ p) * K *
              (B₁ ^ ((1 : ℝ) - p)))).re =
          (Matrix.trace ((star K * (A₁ ^ p) * K) *
              (B₂ ^ ((1 : ℝ) - p) - B₁ ^ ((1 : ℝ) - p)))).re := by
      rw [← Complex.sub_re, hsub]
    linarith [hresub ▸ hnn]
  -- Combine: transitivity.
  exact le_trans hstepB hstepA

/-! ### Sub-Part 7.7: Full Lieb 1973 concavity (general `p + q ≤ 1`)

This section closes the canonical Lieb 1973 joint-concavity theorem in
its general form: for nonneg exponents `p, q ≥ 0` with `p + q ≤ 1`, the
bilinear-quadratic functional `(A, B) ↦ Re Tr(K* · A^p · K · B^q)` is
jointly concave on PSD × PSD pairs.

The case `p + q = 1` is `CFC.lieb_concavity_complementary_PSD`. The
general case is obtained by exponent normalization:

* Set `s := p + q` and `r := p / s` (so `r ∈ [0, 1]` and `1 - r = q/s`).
* `(A^s)^r = A^(s·r) = A^p` by `CFC.rpow_rpow_of_exponent_nonneg`, and
  similarly `(B^s)^(1-r) = B^q`.
* Operator concavity of `x ↦ x^s` on PSD (`CFC.concaveOn_rpow`) gives
  `t • A₁^s + u • A₂^s ≤ (t • A₁ + u • A₂)^s` and likewise for `B`.
* Monotonicity of the complementary Lieb functional
  (`CFC.lieb_complementary_monotone`) then bridges from `(t • A₁^s + …,
  …)` up to `((t • A₁ + …)^s, …)`.
* Joint concavity at `r ∈ [0, 1]` (`CFC.lieb_concavity_complementary_PSD`)
  closes the chain.

The edge case `s = 0` (i.e. `p = q = 0`) reduces to a constant
functional (`K* · 1 · K · 1 = K* K`), hence trivially concave. -/

/-- **Sub-Part 7.7 — Full Lieb 1973 joint concavity (general `p + q ≤ 1`).**

For any matrix `K` and any `p, q ≥ 0` with `p + q ≤ 1`, the bilinear-
quadratic functional `(A, B) ↦ Re Tr(K* · A^p · K · B^q)` is jointly
concave on the closed cone of pairs `(A, B)` of positive semidefinite
matrices.

This is the standard Lieb 1973 complementary concavity theorem (Carlen
2010, §6; Bhatia, *Matrix Analysis*, §IX). It generalises
`CFC.lieb_concavity_complementary_PSD` (the `p + q = 1` case) to all
admissible exponent pairs in the closed simplex `{p, q ≥ 0, p + q ≤ 1}`. -/
theorem lieb_concavity_general
    {n : Type*} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℂ) {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q ≤ 1) :
    ConcaveOn ℝ
      {z : Matrix n n ℂ × Matrix n n ℂ |
        z.1.PosSemidef ∧ z.2.PosSemidef}
      (fun z => (Matrix.trace (star K * (z.1 ^ p) * K * (z.2 ^ q))).re) := by
  classical
  set s : ℝ := p + q with hs_def
  have hs_nonneg : 0 ≤ s := add_nonneg hp hq
  have hs_le_one : s ≤ 1 := hpq
  -- Convexity of the PSD × PSD domain (shared between both branches).
  have hdom_conv : Convex ℝ
      ({z : Matrix n n ℂ × Matrix n n ℂ | z.1.PosSemidef ∧ z.2.PosSemidef}) := by
    intro z₁ hz₁ z₂ hz₂ t u ht hu _
    simp only [Set.mem_setOf_eq] at hz₁ hz₂ ⊢
    obtain ⟨hA₁, hB₁⟩ := hz₁
    obtain ⟨hA₂, hB₂⟩ := hz₂
    exact ⟨(hA₁.smul ht).add (hA₂.smul hu), (hB₁.smul ht).add (hB₂.smul hu)⟩
  -- Split on `s = 0` vs `s > 0`.
  rcases hs_nonneg.lt_or_eq' with hs_pos | hs_zero
  · -- **Case s > 0.** Use exponent normalization via `r := p / s`.
    have hs_ne : s ≠ 0 := ne_of_gt hs_pos
    set r : ℝ := p / s with hr_def
    have hr_nonneg : 0 ≤ r := div_nonneg hp hs_nonneg
    have hr_le_one : r ≤ 1 := by
      rw [hr_def, div_le_one hs_pos]
      exact (le_add_of_nonneg_right hq : p ≤ p + q)
    have hr_mem : r ∈ Set.Icc (0 : ℝ) 1 := ⟨hr_nonneg, hr_le_one⟩
    have hone_minus_r : (1 : ℝ) - r = q / s := by
      rw [hr_def]; field_simp; linarith
    -- Exponent composition: `(a ^ s) ^ r = a ^ p` and `(a ^ s) ^ (1-r) = a ^ q`
    -- on PSD operands.
    have hsr_eq_p : s * r = p := by
      rw [hr_def, mul_div_assoc']; field_simp
    have hsr_eq_q : s * (1 - r) = q := by
      rw [hone_minus_r, mul_div_assoc']; field_simp
    -- The functional, in both forms.
    have hpow_eq_p : ∀ (a : Matrix n n ℂ), a.PosSemidef →
        (a ^ s) ^ r = a ^ p := by
      intro a ha
      have ha0 : (0 : Matrix n n ℂ) ≤ a := Matrix.nonneg_iff_posSemidef.mpr ha
      have := CFC.rpow_rpow_of_exponent_nonneg
        (a := a) s r hs_nonneg hr_nonneg ha0
      rw [this, hsr_eq_p]
    have hpow_eq_q : ∀ (a : Matrix n n ℂ), a.PosSemidef →
        (a ^ s) ^ ((1 : ℝ) - r) = a ^ q := by
      intro a ha
      have ha0 : (0 : Matrix n n ℂ) ≤ a := Matrix.nonneg_iff_posSemidef.mpr ha
      have hrr : 0 ≤ (1 : ℝ) - r := by linarith
      have := CFC.rpow_rpow_of_exponent_nonneg
        (a := a) s ((1 : ℝ) - r) hs_nonneg hrr ha0
      rw [this, hsr_eq_q]
    -- Pull in the two ingredients.
    have h_F_concave := lieb_concavity_complementary_PSD (n := n) K hr_mem
    have h_concave_rpow_s :
        ConcaveOn ℝ (Set.Ici (0 : Matrix n n ℂ))
          (fun a : Matrix n n ℂ => a ^ s) := by
      have : s ∈ Set.Icc (0 : ℝ) 1 := ⟨hs_nonneg, hs_le_one⟩
      exact LTFP.MathlibExt.MatrixAnalysis.CFC.concaveOn_rpow this
    -- Now assemble the joint concavity.
    refine ⟨hdom_conv, ?_⟩
    rintro ⟨A₁, B₁⟩ hz₁ ⟨A₂, B₂⟩ hz₂ t u ht hu htu
    simp only [Set.mem_setOf_eq] at hz₁ hz₂
    obtain ⟨hA₁, hB₁⟩ := hz₁
    obtain ⟨hA₂, hB₂⟩ := hz₂
    -- Names for the convex combinations and their `^s` powers.
    set M : Matrix n n ℂ := t • A₁ + u • A₂ with hM_def
    set N : Matrix n n ℂ := t • B₁ + u • B₂ with hN_def
    have hM_psd : M.PosSemidef := (hA₁.smul ht).add (hA₂.smul hu)
    have hN_psd : N.PosSemidef := (hB₁.smul ht).add (hB₂.smul hu)
    -- PSD-ness of all involved powers.
    have hA₁s_psd : (A₁ ^ s).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := A₁) (y := s))
    have hA₂s_psd : (A₂ ^ s).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := A₂) (y := s))
    have hB₁s_psd : (B₁ ^ s).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := B₁) (y := s))
    have hB₂s_psd : (B₂ ^ s).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := B₂) (y := s))
    have hMs_psd : (M ^ s).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := M) (y := s))
    have hNs_psd : (N ^ s).PosSemidef :=
      Matrix.nonneg_iff_posSemidef.mp (CFC.rpow_nonneg (a := N) (y := s))
    -- Convex combinations of `^s` powers are PSD.
    have hMid_A_psd : (t • A₁ ^ s + u • A₂ ^ s).PosSemidef :=
      (hA₁s_psd.smul ht).add (hA₂s_psd.smul hu)
    have hMid_B_psd : (t • B₁ ^ s + u • B₂ ^ s).PosSemidef :=
      (hB₁s_psd.smul ht).add (hB₂s_psd.smul hu)
    -- Operator concavity of `^s` on PSD: convex-comb-of-powers ≤ power-of-comb.
    have hop_concave_A : t • A₁ ^ s + u • A₂ ^ s ≤ M ^ s := by
      have hA₁_mem : A₁ ∈ Set.Ici (0 : Matrix n n ℂ) :=
        Matrix.nonneg_iff_posSemidef.mpr hA₁
      have hA₂_mem : A₂ ∈ Set.Ici (0 : Matrix n n ℂ) :=
        Matrix.nonneg_iff_posSemidef.mpr hA₂
      have := h_concave_rpow_s.2 hA₁_mem hA₂_mem ht hu htu
      simpa [hM_def] using this
    have hop_concave_B : t • B₁ ^ s + u • B₂ ^ s ≤ N ^ s := by
      have hB₁_mem : B₁ ∈ Set.Ici (0 : Matrix n n ℂ) :=
        Matrix.nonneg_iff_posSemidef.mpr hB₁
      have hB₂_mem : B₂ ∈ Set.Ici (0 : Matrix n n ℂ) :=
        Matrix.nonneg_iff_posSemidef.mpr hB₂
      have := h_concave_rpow_s.2 hB₁_mem hB₂_mem ht hu htu
      simpa [hN_def] using this
    -- The complementary Lieb functional, parameterized by `r`.
    let F : Matrix n n ℂ → Matrix n n ℂ → ℝ := fun X Y =>
      (Matrix.trace (star K * (X ^ r) * K * (Y ^ ((1 : ℝ) - r)))).re
    -- Monotonicity step: F(mid_A, mid_B) ≤ F(M^s, N^s).
    have hmono :
        F (t • A₁ ^ s + u • A₂ ^ s) (t • B₁ ^ s + u • B₂ ^ s)
          ≤ F (M ^ s) (N ^ s) :=
      lieb_complementary_monotone (n := n) K hr_mem
        hMid_A_psd hMs_psd hMid_B_psd hNs_psd hop_concave_A hop_concave_B
    -- Concavity step: t • F(A₁^s, B₁^s) + u • F(A₂^s, B₂^s) ≤ F(mid_A, mid_B).
    have hjoint :
        t • F (A₁ ^ s) (B₁ ^ s) + u • F (A₂ ^ s) (B₂ ^ s)
          ≤ F (t • A₁ ^ s + u • A₂ ^ s) (t • B₁ ^ s + u • B₂ ^ s) := by
      have hPSD₁ : (A₁ ^ s, B₁ ^ s) ∈
          {z : Matrix n n ℂ × Matrix n n ℂ | z.1.PosSemidef ∧ z.2.PosSemidef} :=
        ⟨hA₁s_psd, hB₁s_psd⟩
      have hPSD₂ : (A₂ ^ s, B₂ ^ s) ∈
          {z : Matrix n n ℂ × Matrix n n ℂ | z.1.PosSemidef ∧ z.2.PosSemidef} :=
        ⟨hA₂s_psd, hB₂s_psd⟩
      have := h_F_concave.2 hPSD₁ hPSD₂ ht hu htu
      simpa [F, Prod.smul_mk, Prod.mk_add_mk] using this
    -- Chain: t • F(A₁^s, B₁^s) + u • F(A₂^s, B₂^s) ≤ F(M^s, N^s).
    have hchain :
        t • F (A₁ ^ s) (B₁ ^ s) + u • F (A₂ ^ s) (B₂ ^ s)
          ≤ F (M ^ s) (N ^ s) := le_trans hjoint hmono
    -- Translate F-of-^s-pair into the target functional via exponent identities.
    have hrw_A₁ : (A₁ ^ s) ^ r = A₁ ^ p := hpow_eq_p A₁ hA₁
    have hrw_A₂ : (A₂ ^ s) ^ r = A₂ ^ p := hpow_eq_p A₂ hA₂
    have hrw_B₁ : (B₁ ^ s) ^ ((1 : ℝ) - r) = B₁ ^ q := hpow_eq_q B₁ hB₁
    have hrw_B₂ : (B₂ ^ s) ^ ((1 : ℝ) - r) = B₂ ^ q := hpow_eq_q B₂ hB₂
    have hrw_M : (M ^ s) ^ r = M ^ p := hpow_eq_p M hM_psd
    have hrw_N : (N ^ s) ^ ((1 : ℝ) - r) = N ^ q := hpow_eq_q N hN_psd
    -- Final repackaging.
    show t • (Matrix.trace (star K * (A₁ ^ p) * K * (B₁ ^ q))).re
        + u • (Matrix.trace (star K * (A₂ ^ p) * K * (B₂ ^ q))).re
        ≤ (Matrix.trace (star K * ((t • A₁ + u • A₂) ^ p) * K *
            ((t • B₁ + u • B₂) ^ q))).re
    have hF_M_N :
        F (M ^ s) (N ^ s) =
          (Matrix.trace (star K * ((t • A₁ + u • A₂) ^ p) * K *
            ((t • B₁ + u • B₂) ^ q))).re := by
      show (Matrix.trace (star K * ((M ^ s) ^ r) * K *
              ((N ^ s) ^ ((1 : ℝ) - r)))).re = _
      rw [hrw_M, hrw_N, hM_def, hN_def]
    have hF_A₁_B₁ :
        F (A₁ ^ s) (B₁ ^ s) =
          (Matrix.trace (star K * (A₁ ^ p) * K * (B₁ ^ q))).re := by
      show (Matrix.trace (star K * ((A₁ ^ s) ^ r) * K *
              ((B₁ ^ s) ^ ((1 : ℝ) - r)))).re = _
      rw [hrw_A₁, hrw_B₁]
    have hF_A₂_B₂ :
        F (A₂ ^ s) (B₂ ^ s) =
          (Matrix.trace (star K * (A₂ ^ p) * K * (B₂ ^ q))).re := by
      show (Matrix.trace (star K * ((A₂ ^ s) ^ r) * K *
              ((B₂ ^ s) ^ ((1 : ℝ) - r)))).re = _
      rw [hrw_A₂, hrw_B₂]
    rw [← hF_M_N, ← hF_A₁_B₁, ← hF_A₂_B₂]
    exact hchain
  · -- **Case s = 0.** Then p = q = 0 (both ≥ 0 with p + q = 0), so the
    -- functional is the constant `Re tr(K* · 1 · K · 1) = Re tr(K* K)`.
    have hpq_eq : p + q = 0 := by rw [← hs_def]; exact hs_zero
    have hp_zero : p = 0 := by linarith
    have hq_zero : q = 0 := by linarith
    subst hp_zero
    subst hq_zero
    -- The functional reduces to a constant on the domain.
    have h_eq_const : ∀ z : Matrix n n ℂ × Matrix n n ℂ,
        z.1.PosSemidef ∧ z.2.PosSemidef →
        (Matrix.trace (star K * (z.1 ^ (0 : ℝ)) * K * (z.2 ^ (0 : ℝ)))).re
          = (Matrix.trace (star K * K)).re := by
      rintro ⟨A, B⟩ ⟨hA, hB⟩
      have hA0 : (0 : Matrix n n ℂ) ≤ A := Matrix.nonneg_iff_posSemidef.mpr hA
      have hB0 : (0 : Matrix n n ℂ) ≤ B := Matrix.nonneg_iff_posSemidef.mpr hB
      rw [CFC.rpow_zero A hA0, CFC.rpow_zero B hB0]
      congr 2
      rw [mul_one, mul_one]
    -- A constant function is concave.
    refine ConcaveOn.congr (concaveOn_const ((Matrix.trace (star K * K)).re)
      hdom_conv) ?_
    intro z hz
    exact (h_eq_const z hz).symm

end CFC
