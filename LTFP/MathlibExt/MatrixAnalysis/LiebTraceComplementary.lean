/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.LinearAlgebra.Matrix.Vec
import Mathlib.Analysis.Matrix.PosDef
import LTFP.MathlibExt.MatrixAnalysis.LiebSuperopRpowPersp
import LTFP.MathlibExt.MatrixAnalysis.CStarRpowPerspectiveConcave

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

end CFC
