/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Operator-monotone real functions on Hermitian matrices

This file introduces the predicate `OperatorMonotone f` for real-valued
`f : ℝ → ℝ`, meaning that `f` is monotone with respect to the Löwner order on
finite Hermitian matrices over `RCLike 𝕜`, with the matrix value of `f`
computed via the continuous functional calculus (CFC).

This is the entry point to the operator-monotone / operator-concave tower
that underlies Lieb's 1973 joint concavity theorem and the downstream
matrix Bernstein concentration inequality.

The current file is intentionally a *scope probe*: it provides the
predicate and a few stability lemmas (identity, constant, sum, nonnegative
scalar multiple). It explicitly does NOT cover:

* Löwner's integral representation of operator-monotone functions on
  `[0, ∞)`;
* The operator-concavity equivalent and Jensen-style inequalities;
* Specific operator-monotone functions such as `t ↦ t^p` for `p ∈ (0, 1]`
  or `t ↦ log t`.

These belong to later modules in the Lieb tower.
-/

open scoped MatrixOrder

namespace LTFP.MathlibExt.MatrixAnalysis

universe uomk uomn

/-- A real-valued function `f : ℝ → ℝ` is operator monotone on finite Hermitian
matrices if `A ≤ B` in Löwner order implies `f(A) ≤ f(B)` under the continuous
functional calculus. -/
def OperatorMonotone (f : ℝ → ℝ) : Prop :=
  ∀ {𝕜 : Type uomk} [RCLike 𝕜] {n : Type uomn} [Fintype n] [DecidableEq n]
    (A B : Matrix n n 𝕜) (_hA : A.IsHermitian) (_hB : B.IsHermitian),
    A ≤ B →
      cfc (R := ℝ) (p := IsSelfAdjoint) f A ≤
        cfc (R := ℝ) (p := IsSelfAdjoint) f B

private lemma continuousOn_spectrum_matrix {𝕜 : Type uomk} {n : Type uomn}
    [RCLike 𝕜] [Fintype n] [DecidableEq n] (A : Matrix n n 𝕜) (f : ℝ → ℝ) :
    ContinuousOn f (spectrum ℝ A) := by
  rw [continuousOn_iff_continuous_restrict]
  fun_prop

/-- The identity is operator monotone. -/
theorem operatorMonotone_id : OperatorMonotone.{uomk, uomn} id := by
  intro 𝕜 _ n _ _ A B hA hB hAB
  simpa [cfc_id (R := ℝ) (p := IsSelfAdjoint) A (show IsSelfAdjoint A from hA),
    cfc_id (R := ℝ) (p := IsSelfAdjoint) B (show IsSelfAdjoint B from hB)] using hAB

/-- Constants are operator monotone. -/
theorem operatorMonotone_const (c : ℝ) : OperatorMonotone.{uomk, uomn} (fun _ => c) := by
  intro 𝕜 _ n _ _ A B hA hB _hAB
  rw [cfc_const (R := ℝ) (p := IsSelfAdjoint) c A (show IsSelfAdjoint A from hA),
    cfc_const (R := ℝ) (p := IsSelfAdjoint) c B (show IsSelfAdjoint B from hB)]

variable {f g : ℝ → ℝ}

/-- Sum of two operator-monotone functions is operator monotone. -/
theorem OperatorMonotone.add (hf : OperatorMonotone.{uomk, uomn} f)
    (hg : OperatorMonotone.{uomk, uomn} g) : OperatorMonotone.{uomk, uomn} (f + g) := by
  intro 𝕜 _ n _ _ A B hA hB hAB
  rw [Pi.add_def]
  rw [cfc_add (p := IsSelfAdjoint) A f g
      (continuousOn_spectrum_matrix A f) (continuousOn_spectrum_matrix A g),
    cfc_add (p := IsSelfAdjoint) B f g
      (continuousOn_spectrum_matrix B f) (continuousOn_spectrum_matrix B g)]
  exact add_le_add (hf A B hA hB hAB) (hg A B hA hB hAB)

/-- Nonnegative scalar multiples of operator-monotone functions are operator monotone. -/
theorem OperatorMonotone.const_smul {c : ℝ} (hc : 0 ≤ c)
    (hf : OperatorMonotone.{uomk, uomn} f) : OperatorMonotone.{uomk, uomn} (c • f) := by
  intro 𝕜 _ n _ _ A B hA hB hAB
  rw [Pi.smul_def]
  rw [cfc_smul (p := IsSelfAdjoint) c f A (continuousOn_spectrum_matrix A f),
    cfc_smul (p := IsSelfAdjoint) c f B (continuousOn_spectrum_matrix B f)]
  exact smul_le_smul_of_nonneg_left (hf A B hA hB hAB) hc

/-- A real-valued function `f : ℝ → ℝ` is operator antitone on finite Hermitian
matrices if `A ≤ B` in Löwner order implies `f(B) ≤ f(A)` under the continuous
functional calculus. -/
def OperatorAntitone (f : ℝ → ℝ) : Prop :=
  ∀ {𝕜 : Type uomk} [RCLike 𝕜] {n : Type uomn} [Fintype n] [DecidableEq n]
    (A B : Matrix n n 𝕜) (_hA : A.IsHermitian) (_hB : B.IsHermitian),
    A ≤ B →
      cfc (R := ℝ) (p := IsSelfAdjoint) f B ≤
        cfc (R := ℝ) (p := IsSelfAdjoint) f A

/-- Negating a function flips operator antitonicity into operator monotonicity. -/
theorem operatorAntitone_iff_neg_operatorMonotone (f : ℝ → ℝ) :
    OperatorAntitone.{uomk, uomn} f ↔ OperatorMonotone.{uomk, uomn} (-f) := by
  constructor
  · intro hf 𝕜 _ n _ _ A B hA hB hAB
    change cfc (R := ℝ) (p := IsSelfAdjoint) (fun x => -f x) A ≤
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x => -f x) B
    rw [cfc_neg (p := IsSelfAdjoint) f A, cfc_neg (p := IsSelfAdjoint) f B]
    exact neg_le_neg (hf A B hA hB hAB)
  · intro hf 𝕜 _ n _ _ A B hA hB hAB
    have h := hf A B hA hB hAB
    change cfc (R := ℝ) (p := IsSelfAdjoint) (fun x => -f x) A ≤
      cfc (R := ℝ) (p := IsSelfAdjoint) (fun x => -f x) B at h
    rw [cfc_neg (p := IsSelfAdjoint) f A, cfc_neg (p := IsSelfAdjoint) f B] at h
    exact neg_le_neg_iff.mp h

/-- Negating a function flips operator monotonicity into operator antitonicity. -/
theorem operatorMonotone_neg_iff_operatorAntitone (f : ℝ → ℝ) :
    OperatorMonotone.{uomk, uomn} (-f) ↔ OperatorAntitone.{uomk, uomn} f :=
  (operatorAntitone_iff_neg_operatorMonotone.{uomk, uomn} f).symm

/-- Constants are operator antitone. -/
theorem operatorAntitone_const (c : ℝ) : OperatorAntitone.{uomk, uomn} (fun _ => c) := by
  intro 𝕜 _ n _ _ A B hA hB _hAB
  rw [cfc_const (R := ℝ) (p := IsSelfAdjoint) c B (show IsSelfAdjoint B from hB),
    cfc_const (R := ℝ) (p := IsSelfAdjoint) c A (show IsSelfAdjoint A from hA)]

/-- Sum of two operator-antitone functions is operator antitone. -/
theorem OperatorAntitone.add {f g : ℝ → ℝ} (hf : OperatorAntitone.{uomk, uomn} f)
    (hg : OperatorAntitone.{uomk, uomn} g) : OperatorAntitone.{uomk, uomn} (f + g) := by
  intro 𝕜 _ n _ _ A B hA hB hAB
  rw [Pi.add_def]
  rw [cfc_add (p := IsSelfAdjoint) B f g
      (continuousOn_spectrum_matrix B f) (continuousOn_spectrum_matrix B g),
    cfc_add (p := IsSelfAdjoint) A f g
      (continuousOn_spectrum_matrix A f) (continuousOn_spectrum_matrix A g)]
  exact add_le_add (hf A B hA hB hAB) (hg A B hA hB hAB)

/-- Nonnegative scalar multiples of operator-antitone functions are operator antitone. -/
theorem OperatorAntitone.const_smul {f : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hf : OperatorAntitone.{uomk, uomn} f) : OperatorAntitone.{uomk, uomn} (c • f) := by
  intro 𝕜 _ n _ _ A B hA hB hAB
  rw [Pi.smul_def]
  rw [cfc_smul (p := IsSelfAdjoint) c f B (continuousOn_spectrum_matrix B f),
    cfc_smul (p := IsSelfAdjoint) c f A (continuousOn_spectrum_matrix A f)]
  exact smul_le_smul_of_nonneg_left (hf A B hA hB hAB) hc

/-- Negating an operator-monotone function gives an operator-antitone function. -/
theorem OperatorMonotone.neg_antitone {f : ℝ → ℝ}
    (hf : OperatorMonotone.{uomk, uomn} f) :
    OperatorAntitone.{uomk, uomn} (fun t => -f t) := by
  refine (operatorAntitone_iff_neg_operatorMonotone.{uomk, uomn} (fun t => -f t)).2 ?_
  intro 𝕜 _ n _ _ A B hA hB hAB
  have hfun : -(fun t => -f t) = f := by
    funext t
    simp
  rw [hfun]
  exact hf A B hA hB hAB

/-- Affine functions `t ↦ a·t + b` with `a ≥ 0` are operator monotone. -/
theorem operatorMonotone_affine_of_nonneg {a b : ℝ} (ha : 0 ≤ a) :
    OperatorMonotone.{uomk, uomn} (fun t => a * t + b) := by
  have hlin : OperatorMonotone.{uomk, uomn} (a • (id : ℝ → ℝ)) :=
    OperatorMonotone.const_smul ha operatorMonotone_id
  have hconst : OperatorMonotone.{uomk, uomn} (fun _ : ℝ => b) :=
    operatorMonotone_const b
  have hsum : OperatorMonotone.{uomk, uomn} (a • (id : ℝ → ℝ) + fun _ : ℝ => b) :=
    hlin.add hconst
  intro 𝕜 _ n _ _ A B hA hB hAB
  simpa [Pi.add_def, Pi.smul_def, smul_eq_mul] using hsum A B hA hB hAB

/-- Affine functions `t ↦ a·t + b` with `a ≤ 0` are operator antitone. -/
theorem operatorAntitone_affine_of_nonpos {a b : ℝ} (ha : a ≤ 0) :
    OperatorAntitone.{uomk, uomn} (fun t => a * t + b) := by
  refine (operatorAntitone_iff_neg_operatorMonotone.{uomk, uomn} (fun t => a * t + b)).2 ?_
  have h : OperatorMonotone.{uomk, uomn} (fun t => (-a) * t + (-b)) :=
    operatorMonotone_affine_of_nonneg (a := -a) (b := -b) (neg_nonneg.mpr ha)
  intro 𝕜 _ n _ _ A B hA hB hAB
  simpa [Pi.neg_def, neg_add, neg_mul, add_comm, add_left_comm, add_assoc] using
    h A B hA hB hAB

/-- Composition of two operator-monotone functions is operator monotone. -/
theorem OperatorMonotone.comp {f g : ℝ → ℝ}
    (hf : OperatorMonotone.{uomk, uomn} f) (hg : OperatorMonotone.{uomk, uomn} g) :
    OperatorMonotone.{uomk, uomn} (f ∘ g) := by
  intro 𝕜 _ n _ _ A B hA hB hAB
  rw [cfc_comp (R := ℝ) (p := IsSelfAdjoint) f g A (show IsSelfAdjoint A from hA)
      (by rw [continuousOn_iff_continuous_restrict]; fun_prop)
      (by rw [continuousOn_iff_continuous_restrict]; fun_prop),
    cfc_comp (R := ℝ) (p := IsSelfAdjoint) f g B (show IsSelfAdjoint B from hB)
      (by rw [continuousOn_iff_continuous_restrict]; fun_prop)
      (by rw [continuousOn_iff_continuous_restrict]; fun_prop)]
  exact hf (cfc g A) (cfc g B) (cfc_predicate g A) (cfc_predicate g B)
    (hg A B hA hB hAB)

/-- Composition of two operator-antitone functions is operator monotone. -/
theorem OperatorAntitone.comp {f g : ℝ → ℝ}
    (hf : OperatorAntitone.{uomk, uomn} f) (hg : OperatorAntitone.{uomk, uomn} g) :
    OperatorMonotone.{uomk, uomn} (f ∘ g) := by
  intro 𝕜 _ n _ _ A B hA hB hAB
  rw [cfc_comp (R := ℝ) (p := IsSelfAdjoint) f g A (show IsSelfAdjoint A from hA)
      (by rw [continuousOn_iff_continuous_restrict]; fun_prop)
      (by rw [continuousOn_iff_continuous_restrict]; fun_prop),
    cfc_comp (R := ℝ) (p := IsSelfAdjoint) f g B (show IsSelfAdjoint B from hB)
      (by rw [continuousOn_iff_continuous_restrict]; fun_prop)
      (by rw [continuousOn_iff_continuous_restrict]; fun_prop)]
  exact hf (cfc g B) (cfc g A) (cfc_predicate g B) (cfc_predicate g A)
    (hg A B hA hB hAB)

/-- Composition of an operator-monotone function after an operator-antitone function is operator antitone. -/
theorem OperatorMonotone.comp_antitone {f g : ℝ → ℝ}
    (hf : OperatorMonotone.{uomk, uomn} f) (hg : OperatorAntitone.{uomk, uomn} g) :
    OperatorAntitone.{uomk, uomn} (f ∘ g) := by
  intro 𝕜 _ n _ _ A B hA hB hAB
  rw [cfc_comp (R := ℝ) (p := IsSelfAdjoint) f g B (show IsSelfAdjoint B from hB)
      (by rw [continuousOn_iff_continuous_restrict]; fun_prop)
      (by rw [continuousOn_iff_continuous_restrict]; fun_prop),
    cfc_comp (R := ℝ) (p := IsSelfAdjoint) f g A (show IsSelfAdjoint A from hA)
      (by rw [continuousOn_iff_continuous_restrict]; fun_prop)
      (by rw [continuousOn_iff_continuous_restrict]; fun_prop)]
  exact hf (cfc g B) (cfc g A) (cfc_predicate g B) (cfc_predicate g A)
    (hg A B hA hB hAB)

/-- Composition of an operator-antitone function after an operator-monotone function is operator antitone. -/
theorem OperatorAntitone.comp_monotone {f g : ℝ → ℝ}
    (hf : OperatorAntitone.{uomk, uomn} f) (hg : OperatorMonotone.{uomk, uomn} g) :
    OperatorAntitone.{uomk, uomn} (f ∘ g) := by
  intro 𝕜 _ n _ _ A B hA hB hAB
  rw [cfc_comp (R := ℝ) (p := IsSelfAdjoint) f g B (show IsSelfAdjoint B from hB)
      (by rw [continuousOn_iff_continuous_restrict]; fun_prop)
      (by rw [continuousOn_iff_continuous_restrict]; fun_prop),
    cfc_comp (R := ℝ) (p := IsSelfAdjoint) f g A (show IsSelfAdjoint A from hA)
      (by rw [continuousOn_iff_continuous_restrict]; fun_prop)
      (by rw [continuousOn_iff_continuous_restrict]; fun_prop)]
  exact hf (cfc g A) (cfc g B) (cfc_predicate g A) (cfc_predicate g B)
    (hg A B hA hB hAB)

private lemma algebraMap_matrix_le_of_real_le {x y : ℝ} (hxy : x ≤ y) :
    (algebraMap ℝ (Matrix Unit Unit ℝ) x) ≤ algebraMap ℝ (Matrix Unit Unit ℝ) y := by
  rw [Matrix.le_iff]
  have hnonneg : 0 ≤ y - x := sub_nonneg.mpr hxy
  simpa [sub_eq_add_neg, Matrix.algebraMap_eq_diagonal, Pi.algebraMap_def] using
    (Matrix.PosSemidef.diagonal (n := Unit) (d := fun _ : Unit => y - x)
      (fun _ => hnonneg))

private lemma real_le_of_algebraMap_matrix_le {x y : ℝ}
    (hxy : (algebraMap ℝ (Matrix Unit Unit ℝ) x) ≤ algebraMap ℝ (Matrix Unit Unit ℝ) y) :
    x ≤ y := by
  rw [Matrix.le_iff] at hxy
  have hdiag : 0 ≤ y - x := by
    simpa [sub_eq_add_neg, Matrix.algebraMap_eq_diagonal, Pi.algebraMap_def] using
      (Matrix.posSemidef_diagonal_iff (n := Unit) (d := fun _ : Unit => y - x)).1 hxy ()
  exact sub_nonneg.mp hdiag

/-- Operator-monotone functions are monotone on scalars. -/
theorem OperatorMonotone.monotone {f : ℝ → ℝ}
    (hf : OperatorMonotone.{0, 0} f) : Monotone f := by
  intro x y hxy
  have hraw := hf
    (algebraMap ℝ (Matrix Unit Unit ℝ) x)
    (algebraMap ℝ (Matrix Unit Unit ℝ) y)
    (cfc_predicate_algebraMap (R := ℝ) (A := Matrix Unit Unit ℝ) (p := IsSelfAdjoint) x)
    (cfc_predicate_algebraMap (R := ℝ) (A := Matrix Unit Unit ℝ) (p := IsSelfAdjoint) y)
    (algebraMap_matrix_le_of_real_le hxy)
  have hmat : (algebraMap ℝ (Matrix Unit Unit ℝ) (f x)) ≤
      algebraMap ℝ (Matrix Unit Unit ℝ) (f y) := by
    simpa only [cfc_algebraMap] using hraw
  exact real_le_of_algebraMap_matrix_le hmat

/-- Operator-antitone functions are antitone on scalars. -/
theorem OperatorAntitone.antitone {f : ℝ → ℝ}
    (hf : OperatorAntitone.{0, 0} f) : Antitone f := by
  intro x y hxy
  have hraw := hf
    (algebraMap ℝ (Matrix Unit Unit ℝ) x)
    (algebraMap ℝ (Matrix Unit Unit ℝ) y)
    (cfc_predicate_algebraMap (R := ℝ) (A := Matrix Unit Unit ℝ) (p := IsSelfAdjoint) x)
    (cfc_predicate_algebraMap (R := ℝ) (A := Matrix Unit Unit ℝ) (p := IsSelfAdjoint) y)
    (algebraMap_matrix_le_of_real_le hxy)
  have hmat : (algebraMap ℝ (Matrix Unit Unit ℝ) (f y)) ≤
      algebraMap ℝ (Matrix Unit Unit ℝ) (f x) := by
    simpa only [cfc_algebraMap] using hraw
  exact real_le_of_algebraMap_matrix_le hmat

/-- Adding a constant to an operator-monotone function preserves operator monotonicity. -/
theorem OperatorMonotone.const_add {f : ℝ → ℝ}
    (hf : OperatorMonotone.{uomk, uomn} f) (c : ℝ) :
    OperatorMonotone.{uomk, uomn} (fun t => c + f t) := by
  change OperatorMonotone.{uomk, uomn} ((fun _ : ℝ => c) + f)
  have hconst : OperatorMonotone.{uomk, uomn} (fun _ : ℝ => c) := by
    exact operatorMonotone_const c
  exact @OperatorMonotone.add.{uomk, uomn} (fun _ : ℝ => c) f hconst hf

/-- Adding a constant to an operator-antitone function preserves operator antitonicity. -/
theorem OperatorAntitone.const_add {f : ℝ → ℝ}
    (hf : OperatorAntitone.{uomk, uomn} f) (c : ℝ) :
    OperatorAntitone.{uomk, uomn} (fun t => c + f t) := by
  change OperatorAntitone.{uomk, uomn} ((fun _ : ℝ => c) + f)
  have hconst : OperatorAntitone.{uomk, uomn} (fun _ : ℝ => c) :=
    operatorAntitone_const c
  exact @OperatorAntitone.add.{uomk, uomn} (fun _ : ℝ => c) f hconst hf

/-- A real-valued function `f : ℝ → ℝ` is operator concave on finite Hermitian
matrices if for all `t ∈ [0, 1]` and Hermitian `A B`, the CFC values satisfy
`t · f(A) + (1 - t) · f(B) ≤ f(t · A + (1 - t) · B)`.

This is the natural Lieb-tower-L2 entry point: operator-concave functions are
the right framework for joint concavity statements (Lieb 1973). The full
operator-concave equivalence with operator-monotone via Löwner's integral
representation is multi-month Mathlib work and is NOT proved here. -/
def OperatorConcave (f : ℝ → ℝ) : Prop :=
  ∀ {𝕜 : Type uomk} [RCLike 𝕜] {n : Type uomn} [Fintype n] [DecidableEq n]
    (A B : Matrix n n 𝕜) (_hA : A.IsHermitian) (_hB : B.IsHermitian)
    (t : ℝ) (_ht : t ∈ Set.Icc (0:ℝ) 1),
    t • cfc (R := ℝ) (p := IsSelfAdjoint) f A +
      (1 - t) • cfc (R := ℝ) (p := IsSelfAdjoint) f B ≤
      cfc (R := ℝ) (p := IsSelfAdjoint) f (t • A + (1 - t) • B)

/-- Constants are operator concave (with equality). -/
theorem operatorConcave_const (c : ℝ) : OperatorConcave.{uomk, uomn} (fun _ => c) := by
  intro 𝕜 _ n _ _ A B hA hB t _ht
  have hAs : IsSelfAdjoint A := hA
  have hBs : IsSelfAdjoint B := hB
  have hsum : IsSelfAdjoint (t • A + (1 - t) • B) :=
    ((IsSelfAdjoint.all t).smul hAs).add
      ((IsSelfAdjoint.all (1 - t)).smul hBs)
  rw [cfc_const (R := ℝ) (p := IsSelfAdjoint) c A hAs,
    cfc_const (R := ℝ) (p := IsSelfAdjoint) c B hBs,
    cfc_const (R := ℝ) (p := IsSelfAdjoint) c (t • A + (1 - t) • B) hsum,
    ← add_smul]
  have ht_sum : t + (1 - t) = 1 := by ring
  rw [ht_sum, one_smul]

/-- The identity is operator concave (with equality — affine in t). -/
theorem operatorConcave_id : OperatorConcave.{uomk, uomn} id := by
  intro 𝕜 _ n _ _ A B hA hB t _ht
  have hAs : IsSelfAdjoint A := hA
  have hBs : IsSelfAdjoint B := hB
  have hsum : IsSelfAdjoint (t • A + (1 - t) • B) :=
    ((IsSelfAdjoint.all t).smul hAs).add
      ((IsSelfAdjoint.all (1 - t)).smul hBs)
  rw [cfc_id (R := ℝ) (p := IsSelfAdjoint) A hAs,
      cfc_id (R := ℝ) (p := IsSelfAdjoint) B hBs,
      cfc_id (R := ℝ) (p := IsSelfAdjoint) (t • A + (1 - t) • B) hsum]

end LTFP.MathlibExt.MatrixAnalysis
