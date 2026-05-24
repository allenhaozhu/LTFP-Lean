/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import Mathlib.Analysis.CStarAlgebra.ApproximateUnit
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic.NoncommRing

/-!
# Operator concavity of the shifted resolvent `x ↦ 1 - (1 + x)⁻¹`

This file proves the central operator-concavity lemma

```
CFC.concaveOn_one_sub_one_add_inv_real :
    ConcaveOn ℝ (Set.Ici (0 : A)) (cfcₙ (fun x : ℝ => 1 - (1 + x)⁻¹))
```

for any non-unital C⋆-algebra `A`. This is the operator analogue of the
classical scalar fact that `t ↦ 1 - (1+t)⁻¹` is concave on `[0, ∞)`.

## Proof strategy

We prove the operator AM-HM inequality
```
(u • X + v • Y)⁻¹ ≤ u • X⁻¹ + v • Y⁻¹    (X, Y positive invertible, u+v=1)
```
via the noncommutative Anderson–Trapp algebraic identity
```
u • X⁻¹ + v • Y⁻¹ - (u • X + v • Y)⁻¹
   = (u * v) • (X⁻¹ - Y⁻¹) * S⁻¹ * (X⁻¹ - Y⁻¹)
```
where `S := v • X⁻¹ + u • Y⁻¹`. The RHS is a conjugation of `S⁻¹ ≥ 0` by the
self-adjoint factor `X⁻¹ - Y⁻¹`, hence nonneg. The identity is justified by
the relation `X⁻¹ * (u•X + v•Y) * Y⁻¹ = u•Y⁻¹ + v•X⁻¹ = S` (no commutation
needed — `X⁻¹ X = 1`, `Y Y⁻¹ = 1` are the only steps), so
`(u•X + v•Y)⁻¹ = Y⁻¹ * S⁻¹ * X⁻¹`. Substituting `X⁻¹ = S + u•D` and
`Y⁻¹ = S - v•D` (where `D = X⁻¹ - Y⁻¹`) yields
```
P⁻¹ = (S - v•D) S⁻¹ (S + u•D) = S + u•D - v•D - uv (D S⁻¹ D)
    = u•X⁻¹ + v•Y⁻¹ - uv (D S⁻¹ D),
```
which is the identity.

The non-unital target follows by shifting to `1 + a` in the unitization
`A⁺¹` (always strictly positive when `a ≥ 0`), applying the unital AM-HM
inequality, subtracting from `1` to switch to concavity, and transporting
back to `A` via `Unitization.real_cfcₙ_eq_cfc_inr`.

## Status

**This is the canonical operator-convexity-of-inverse / AM-HM lemma**, the
substantive upstream lemma that unlocks the entire L3 operator-concavity
layer (Lieb 1973 prerequisites, log/rpow operator concavity, etc.).

This file lands the central step. Downstream corollaries (operator-concavity
of `log`, `rpow` for `p ∈ [0,1]`, etc.) are direct consequences once this
shifted-resolvent concavity is available.
-/

@[expose] public section

namespace LTFP.MathlibExt.MatrixAnalysis

open scoped NonUnitalContinuousFunctionalCalculus CStarAlgebra

/-! ### Algebraic identity in a unital ring

The non-commutative AM-HM identity is purely algebraic and lives in any
unital `ℝ`-algebra. The trick is that we cast the identity in terms of
*two-sided inverses* (provided externally as hypotheses), so we never
need to manipulate the symbol `(·)⁻¹` directly. -/

section RingIdentity

variable {R : Type*} [Ring R] [Module ℝ R] [SMulCommClass ℝ R R] [IsScalarTower ℝ R R]

omit [SMulCommClass ℝ R R] [IsScalarTower ℝ R R] in
/-- **Substitution identity, step 1.**
`y' = (v • y' + u • y'') + u • (y' - y'')`, provided `u + v = 1`. -/
private lemma sub_id_left {y' y'' : R} {u v : ℝ} (huv : u + v = 1) :
    y' = (v • y' + u • y'') + u • (y' - y'') := by
  -- v • y' + u • y'' + u • (y' - y'') = (u+v) • y' + 0 • y'' = y'
  have h1 : v • y' + u • y'' + u • (y' - y'') = (u + v) • y' := by
    rw [smul_sub, add_smul]
    abel
  rw [h1, huv, one_smul]

omit [SMulCommClass ℝ R R] [IsScalarTower ℝ R R] in
/-- **Substitution identity, step 2.**
`y'' = (v • y' + u • y'') - v • (y' - y'')`, provided `u + v = 1`. -/
private lemma sub_id_right {y' y'' : R} {u v : ℝ} (huv : u + v = 1) :
    y'' = (v • y' + u • y'') - v • (y' - y'') := by
  have h1 : v • y' + u • y'' - v • (y' - y'') = (u + v) • y'' := by
    rw [smul_sub, add_smul]
    abel
  rw [h1, huv, one_smul]

/-- **Non-commutative AM-HM algebraic identity.**

Given `x y : R` with explicit two-sided inverses `y' y'' : R` (so `y' x = 1`,
`x y' = 1`, `y'' y = 1`, `y y'' = 1`), and scalars `u v : ℝ`, suppose
furthermore the element `S := v • y' + u • y''` has a two-sided inverse
`S_inv`. Then

```
y'' * S_inv * y' = (u • x + v • y)_inv
```

where `(u • x + v • y)_inv` is any two-sided inverse of `u • x + v • y`,
in the sense that

```
(u • x + v • y) * (y'' * S_inv * y') = 1   AND
(y'' * S_inv * y') * (u • x + v • y) = 1.
```

(We prove both directly.) Note: existence of such a candidate inverse on
the LHS implies invertibility of `P := u • x + v • y` in `R`. The
constraint `u + v = 1` is not needed for this formula (the underlying
identity `y' * (u•x + v•y) * y'' = v•y' + u•y''` holds for arbitrary
scalars). -/
private lemma p_inv_formula
    {x y y' y'' S_inv : R} {u v : ℝ}
    (hxy' : x * y' = 1) (hy'x : y' * x = 1)
    (hyy'' : y * y'' = 1) (hy''y : y'' * y = 1)
    (hSinv_l : (v • y' + u • y'') * S_inv = 1)
    (hSinv_r : S_inv * (v • y' + u • y'') = 1) :
    (u • x + v • y) * (y'' * S_inv * y') = 1 ∧
      (y'' * S_inv * y') * (u • x + v • y) = 1 := by
  -- Key intermediate: y' * (u•x + v•y) * y'' = v•y' + u•y'' = S.
  -- This uses only: y' * x = 1 and y * y'' = 1.
  have h_yPy : y' * (u • x + v • y) * y'' = v • y' + u • y'' := by
    rw [mul_add, add_mul]
    rw [show y' * (u • x) = u • (y' * x) from by rw [mul_smul_comm],
        show y' * (v • y) = v • (y' * y) from by rw [mul_smul_comm]]
    rw [show u • (y' * x) * y'' = u • ((y' * x) * y'') from by rw [smul_mul_assoc],
        show v • (y' * y) * y'' = v • ((y' * y) * y'') from by rw [smul_mul_assoc]]
    rw [hy'x, one_mul, mul_assoc, hyy'', mul_one]
    -- Goal: u • y'' + v • y' = v • y' + u • y''
    rw [add_comm]
  -- From h_yPy, get (u•x + v•y) * y'' = y * S (using y'*y = ?), wait
  -- Let me derive the two products differently.
  refine ⟨?_, ?_⟩
  · -- (u•x + v•y) * (y'' * S_inv * y') = 1
    -- = (u•x + v•y) * y'' * S_inv * y'
    -- We need: (u•x + v•y) * y'' = ? * y for some ?
    -- Actually use: y' * (u•x + v•y) * y'' = S, so (u•x + v•y) * y'' = x * S * (some)
    -- since (u•x + v•y) * y'' = x * (y' * (u•x + v•y) * y'') = x * S, using x*y' = 1.
    have h_Py'' : (u • x + v • y) * y'' = x * (v • y' + u • y'') := by
      calc (u • x + v • y) * y'' = x * y' * ((u • x + v • y) * y'') := by
            rw [hxy', one_mul]
        _ = x * (y' * (u • x + v • y) * y'') := by
            rw [mul_assoc, mul_assoc, ← mul_assoc y' _ y'']
        _ = x * (v • y' + u • y'') := by rw [h_yPy]
    -- (u•x+v•y) * (y'' * S_inv * y') = ((u•x+v•y) * y'') * S_inv * y'
    rw [show (u • x + v • y) * (y'' * S_inv * y') =
        ((u • x + v • y) * y'') * S_inv * y' from by
          rw [mul_assoc ((u • x + v • y) * y'') S_inv y',
              mul_assoc (u • x + v • y) y'' (S_inv * y'),
              ← mul_assoc y'' S_inv y']]
    rw [h_Py'']
    -- Goal: x * (v•y' + u•y'') * S_inv * y' = 1
    rw [mul_assoc x _ S_inv, hSinv_l]
    rw [mul_one, hxy']
  · -- (y'' * S_inv * y') * (u•x + v•y) = 1
    have h_y'P : y' * (u • x + v • y) = (v • y' + u • y'') * y := by
      calc y' * (u • x + v • y) = y' * (u • x + v • y) * (y'' * y) := by
            rw [hy''y, mul_one]
        _ = (y' * (u • x + v • y) * y'') * y := by
            rw [mul_assoc (y' * (u • x + v • y)) y'' y]
        _ = (v • y' + u • y'') * y := by rw [h_yPy]
    rw [show (y'' * S_inv * y') * (u • x + v • y) =
        y'' * S_inv * (y' * (u • x + v • y)) from by
          rw [mul_assoc (y'' * S_inv) y' (u • x + v • y)]]
    rw [h_y'P]
    -- Goal: y'' * S_inv * ((v • y' + u • y'') * y) = 1
    -- Rearrange via mul_assoc/← mul_assoc so hSinv_r applies.
    rw [show y'' * S_inv * ((v • y' + u • y'') * y) =
        y'' * (S_inv * (v • y' + u • y'')) * y from by
          rw [mul_assoc y'' S_inv ((v • y' + u • y'') * y),
              ← mul_assoc S_inv (v • y' + u • y'') y,
              ← mul_assoc y'' (S_inv * (v • y' + u • y'')) y]]
    rw [hSinv_r, mul_one, hy''y]

/-- **The Anderson–Trapp algebraic identity.**

In any unital `ℝ`-algebra `R`, given a two-sided inverse `S_inv : R` of
`S := v • y' + u • y''`, with `u + v = 1`, we have

```
u • y' + v • y'' - y'' * S_inv * y' =
    (u * v) • ((y' - y'') * S_inv * (y' - y''))
```

The proof: substitute `y' = S + u • D`, `y'' = S - v • D` (where `D = y' - y''`,
`S = v • y' + u • y''`), expand
`y'' * S_inv * y' = (S - v•D) * S_inv * (S + u•D)
                  = S + u•D - v•D - uv • (D * S_inv * D)`,
using `S * S_inv = S_inv * S = 1`. The linear-in-`D` terms recombine into
`(u-v) • D = u•y' + v•y'' - S`, which cancels with the `S + u•D - v•D` and
the `u•y' + v•y''` on the LHS up to the `uv • (D * S_inv * D)` term.

Note: the two-sided inverse hypotheses on `x` and `y` themselves are not
required for this algebraic identity (only the `S_inv` inverse hypotheses
on `S` and the constraint `u + v = 1` are used). They are needed at the
call site to package `y'' * S_inv * y'` as the inverse of `u • x + v • y`
via `p_inv_formula`, but the identity here is purely on `y', y'', S_inv`. -/
lemma amHm_identity
    {y' y'' S_inv : R} {u v : ℝ}
    (hSinv_l : (v • y' + u • y'') * S_inv = 1)
    (hSinv_r : S_inv * (v • y' + u • y'') = 1)
    (huv : u + v = 1) :
    u • y' + v • y'' - y'' * S_inv * y' =
      (u * v) • ((y' - y'') * S_inv * (y' - y'')) := by
  -- Strategy: substitute y' = S + u•D, y'' = S - v•D into y'' * S_inv * y'.
  set D : R := y' - y'' with hD_def
  set S : R := v • y' + u • y'' with hS_def
  have hy'_eq : y' = S + u • D := sub_id_left huv
  have hy''_eq : y'' = S - v • D := sub_id_right huv
  -- Compute y'' * S_inv * y'  = (S - v•D) * S_inv * (S + u•D)
  -- = S * S_inv * S + u • (S * S_inv * D) - v • (D * S_inv * S) - uv • (D * S_inv * D)
  -- = S + u • D - v • D - uv • (D * S_inv * D)
  have hSSi : S * S_inv = 1 := by rw [hS_def]; exact hSinv_l
  have hSiS : S_inv * S = 1 := by rw [hS_def]; exact hSinv_r
  have h_prod : y'' * S_inv * y' =
      S + u • D - v • D - (u * v) • (D * S_inv * D) := by
    -- Rewrite y'' and y' using their substitutions, then expand.
    rw [hy''_eq, hy'_eq]
    -- (S - v•D) * S_inv * (S + u•D)
    -- Step 1: expand (S - v•D) * S_inv = S*S_inv - (v•D)*S_inv = 1 - v • (D * S_inv).
    have h_left : (S - v • D) * S_inv = 1 - v • (D * S_inv) := by
      rw [sub_mul, hSSi, smul_mul_assoc]
    rw [show (S - v • D) * S_inv * (S + u • D) = ((S - v • D) * S_inv) * (S + u • D)
        from rfl]
    rw [h_left]
    -- Step 2: (1 - v•(D*S_inv)) * (S + u•D) = (S + u•D) - v • (D*S_inv) * (S + u•D)
    rw [sub_mul, one_mul]
    -- Step 3: v • (D*S_inv) * (S + u•D) = v • (D*S_inv*S + u • (D*S_inv*D))
    --                                   = v • (D + u • (D*S_inv*D))
    --                                   = v • D + (v*u) • (D*S_inv*D)
    rw [smul_mul_assoc, mul_add]
    rw [show D * S_inv * S = D from by rw [mul_assoc, hSiS, mul_one]]
    rw [show D * S_inv * (u • D) = u • (D * S_inv * D) from by rw [mul_smul_comm]]
    rw [smul_add, smul_smul]
    -- Goal: S + u • D - (v • D + (v * u) • (D * S_inv * D))
    --     = S + u • D - v • D - (u * v) • (D * S_inv * D)
    rw [mul_comm v u]
    abel
  -- Now compute u • y' + v • y'' = S + (u - v) • D
  have h_lin : u • y' + v • y'' = S + (u - v) • D := by
    -- Conceptual rewrite: u • y' + v • y'' = (S+u•D side) + (S-v•D side, w/ swap)
    -- Use the explicit formulas u•y' = u•S + u²•D, v•y'' = v•S - v²•D.
    -- Then sum = (u+v)•S + (u² - v²)•D = S + (u-v)•D since u² - v² = (u-v)(u+v).
    have hu_y' : u • y' = u • S + (u * u) • D := by
      rw [hy'_eq, smul_add, smul_smul]
    have hv_y'' : v • y'' = v • S - (v * v) • D := by
      rw [hy''_eq, smul_sub, smul_smul]
    rw [hu_y', hv_y'']
    rw [show u • S + (u * u) • D + (v • S - (v * v) • D)
        = (u + v) • S + ((u * u) - (v * v)) • D from by rw [add_smul, sub_smul]; abel]
    rw [huv, one_smul]
    congr 1
    have : u * u - v * v = u - v := by nlinarith [huv]
    rw [this]
  -- Combine h_lin and h_prod:
  -- u • y' + v • y'' - y'' * S_inv * y'
  -- = (S + (u-v)•D) - (S + u•D - v•D - (u*v)•(D*S_inv*D))
  -- = (u-v)•D - u•D + v•D + (u*v)•(D*S_inv*D)
  -- = (u-v-u+v)•D + (u*v)•(D*S_inv*D)
  -- = 0 + (u*v)•(D*S_inv*D)
  -- = (u*v)•(D*S_inv*D)
  rw [h_lin, h_prod]
  -- Goal: S + (u - v) • D - (S + u • D - v • D - (u * v) • (D * S_inv * D))
  --     = (u * v) • ((y' - y'') * S_inv * (y' - y''))
  -- Replace D = y' - y'':
  show S + (u - v) • D - (S + u • D - v • D - (u * v) • (D * S_inv * D))
     = (u * v) • ((y' - y'') * S_inv * (y' - y''))
  have hD' : y' - y'' = D := rfl
  rw [hD']
  -- Goal: S + (u - v) • D - (S + u • D - v • D - (u * v) • (D * S_inv * D))
  --     = (u * v) • (D * S_inv * D)
  -- Linear simplification:
  have : S + (u - v) • D - (S + u • D - v • D - (u * v) • (D * S_inv * D))
       = ((u - v) - u + v) • D + (u * v) • (D * S_inv * D) := by
    rw [show ((u - v) - u + v) • D = (u - v) • D - u • D + v • D from by
          rw [add_smul, sub_smul, sub_smul]]
    abel
  rw [this]
  have h0 : (u - v) - u + v = 0 := by ring
  rw [h0, zero_smul, zero_add]

end RingIdentity

/-! ### Operator AM-HM in a unital C⋆-algebra -/

section UnitalAmHm

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- **Operator AM-HM inequality** in a unital C⋆-algebra.

For positive invertible `X Y : Aˣ` (with `0 ≤ (X : A)` and `0 ≤ (Y : A)`) and
real weights `u v : ℝ` with `0 ≤ u, 0 ≤ v, u + v = 1`, the inequality
```
(u • X + v • Y)⁻¹ ≤ u • X⁻¹ + v • Y⁻¹
```
holds in `A`, where the LHS is the inverse of the (strictly positive) element
`u • X + v • Y`.

The proof packages the algebraic identity `amHm_identity`: the difference
between RHS and LHS equals `(u * v) • (X⁻¹ - Y⁻¹) S⁻¹ (X⁻¹ - Y⁻¹)`, which is
a conjugation of a positive element by a self-adjoint factor, hence nonneg.

The endpoint cases `u = 0` and `v = 0` are handled separately (the inequality
becomes trivial). For the interior `0 < u, 0 < v`, both `u • X + v • Y` and
`v • X⁻¹ + u • Y⁻¹` are strictly positive, hence invertible. -/
theorem CStarAlgebra.amHm_aux
    {X Y : Aˣ} (hX : (0 : A) ≤ X) (hY : (0 : A) ≤ Y)
    {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u + v = 1) :
    ∀ {P : Aˣ}, ((P : A) = u • (X : A) + v • (Y : A)) →
      (((P⁻¹ : Aˣ) : A) ≤ u • ((X⁻¹ : Aˣ) : A) + v • ((Y⁻¹ : Aˣ) : A)) := by
  rcases eq_or_lt_of_le hu with hu0 | hu_pos
  · -- u = 0 case: P = Y, RHS = Y⁻¹.
    intro P hP
    have hv1 : v = 1 := by linarith
    subst hu0
    subst hv1
    -- P = 0•X + 1•Y = Y, so P = Y as units.
    rw [zero_smul, zero_add, one_smul] at hP
    have hPY : (P : A) = (Y : A) := hP
    have hPY_units : P = Y := Units.ext hPY
    rw [hPY_units]
    rw [zero_smul, zero_add, one_smul]
  rcases eq_or_lt_of_le hv with hv0 | hv_pos
  · -- v = 0 case: symmetric.
    intro P hP
    have hu1 : u = 1 := by linarith
    subst hv0
    subst hu1
    rw [zero_smul, add_zero, one_smul] at hP
    have hPX : (P : A) = (X : A) := hP
    have hPX_units : P = X := Units.ext hPX
    rw [hPX_units]
    rw [zero_smul, add_zero, one_smul]
  -- Interior case: 0 < u and 0 < v.
  intro P hP
  -- Set up names.
  set xi : A := ((X⁻¹ : Aˣ) : A) with hxi_def
  set yi : A := ((Y⁻¹ : Aˣ) : A) with hyi_def
  have hxi_nn : (0 : A) ≤ xi := CFC.inv_nonneg_of_nonneg X hX
  have hyi_nn : (0 : A) ≤ yi := CFC.inv_nonneg_of_nonneg Y hY
  have hXi_sp : IsStrictlyPositive xi := X⁻¹.isUnit.isStrictlyPositive hxi_nn
  have hYi_sp : IsStrictlyPositive yi := Y⁻¹.isUnit.isStrictlyPositive hyi_nn
  -- S := v • xi + u • yi is strictly positive.
  have hvxi_sp : IsStrictlyPositive (v • xi) := hXi_sp.smul hv_pos
  have hS_sp : IsStrictlyPositive (v • xi + u • yi) :=
    hvxi_sp.add_nonneg (smul_nonneg hu hyi_nn)
  -- Promote to a unit.
  set S : Aˣ := hS_sp.isUnit.unit with hS_def
  have hSeq : (S : A) = v • xi + u • yi := IsUnit.unit_spec hS_sp.isUnit
  -- Two-sided inverses, packaged for amHm_identity.
  have hX_left : (xi : A) * X = 1 := by
    show ((X⁻¹ : Aˣ) : A) * X = 1
    exact_mod_cast X.inv_mul
  have hX_right : (X : A) * xi = 1 := by
    show (X : A) * ((X⁻¹ : Aˣ) : A) = 1
    exact_mod_cast X.mul_inv
  have hY_left : (yi : A) * Y = 1 := by
    show ((Y⁻¹ : Aˣ) : A) * Y = 1
    exact_mod_cast Y.inv_mul
  have hY_right : (Y : A) * yi = 1 := by
    show (Y : A) * ((Y⁻¹ : Aˣ) : A) = 1
    exact_mod_cast Y.mul_inv
  set Si : A := ((S⁻¹ : Aˣ) : A) with hSi_def
  have hSinv_l : (v • xi + u • yi) * Si = 1 := by
    rw [← hSeq]
    show (S : A) * ((S⁻¹ : Aˣ) : A) = 1
    exact_mod_cast S.mul_inv
  have hSinv_r : Si * (v • xi + u • yi) = 1 := by
    rw [← hSeq]
    show ((S⁻¹ : Aˣ) : A) * (S : A) = 1
    exact_mod_cast S.inv_mul
  -- P inverse formula and P invertibility from p_inv_formula (auxiliary).
  obtain ⟨h_left, h_right⟩ :=
    p_inv_formula (x := (X : A)) (y := (Y : A)) (y' := xi) (y'' := yi)
      (S_inv := Si) (u := u) (v := v)
      hX_right hX_left hY_right hY_left hSinv_l hSinv_r
  have hPinv_eq : ((P⁻¹ : Aˣ) : A) = yi * Si * xi := by
    -- (yi * Si * xi) * P = 1, so it equals P⁻¹.
    have hPmul : (yi * Si * xi) * (P : A) = 1 := by
      rw [hP]; exact h_right
    -- Multiply by P⁻¹ on the right
    have hcalc : (yi * Si * xi) * (P : A) * ((P⁻¹ : Aˣ) : A) =
        1 * ((P⁻¹ : Aˣ) : A) := by
      rw [hPmul]
    rw [mul_assoc] at hcalc
    rw [show (P : A) * ((P⁻¹ : Aˣ) : A) = 1 from by exact_mod_cast P.mul_inv] at hcalc
    rw [mul_one, one_mul] at hcalc
    exact hcalc.symm
  -- Apply the algebraic identity:
  --   u • xi + v • yi - yi*Si*xi = (u*v) • (xi-yi) Si (xi-yi)
  have h_id := amHm_identity
    (y' := xi) (y'' := yi) (S_inv := Si)
    (u := u) (v := v)
    hSinv_l hSinv_r huv
  -- Goal: ((P⁻¹ : Aˣ) : A) ≤ u • xi + v • yi
  rw [hPinv_eq]
  -- Now goal: yi * Si * xi ≤ u • xi + v • yi
  rw [← sub_nonneg]
  rw [h_id]
  -- Goal: 0 ≤ (u * v) • ((xi - yi) * Si * (xi - yi))
  have hD_sa : IsSelfAdjoint (xi - yi) :=
    (IsSelfAdjoint.of_nonneg hxi_nn).sub (IsSelfAdjoint.of_nonneg hyi_nn)
  -- Si is nonneg (inverse of strictly positive unit).
  have hSi_nn : (0 : A) ≤ Si := CFC.inv_nonneg_of_nonneg S hS_sp.nonneg
  -- (xi - yi) * Si * (xi - yi) is a star-left-conjugation, hence nonneg.
  have hquad : (0 : A) ≤ (xi - yi) * Si * (xi - yi) := by
    have h_eq : (xi - yi) * Si * (xi - yi) = star (xi - yi) * Si * (xi - yi) := by
      rw [hD_sa.star_eq]
    rw [h_eq]
    exact star_left_conjugate_nonneg hSi_nn (xi - yi)
  exact smul_nonneg (mul_nonneg hu hv) hquad

/-! ### Operator concavity of `1 - (1 + x)⁻¹` on the unital cone -/

/-- **CFC computation lemma**: for any nonnegative `a` in a unital C⋆-algebra,
`cfc (fun x => 1 - (1+x)⁻¹) a = 1 - ((1 + a) considered as a unit)⁻¹`.

The function `f(x) = 1 - (1+x)⁻¹` decomposes as `1 - (·⁻¹) ∘ (1 + ·)`. Its
value via the real CFC is computed using `cfc_sub` / `cfc_const_one` /
`cfc_comp' (·⁻¹) (1 + ·)`. -/
private lemma cfc_one_sub_one_add_inv_eq {a : A} (ha : 0 ≤ a) :
    cfc (fun x : ℝ => 1 - (1 + x)⁻¹) a =
      1 - ((IsStrictlyPositive.add_nonneg isStrictlyPositive_one ha
            ).isUnit.unit⁻¹ : Aˣ) := by
  set u : Aˣ := (IsStrictlyPositive.add_nonneg isStrictlyPositive_one ha).isUnit.unit
    with hu_def
  have hueq : (u : A) = 1 + a := IsUnit.unit_spec _
  have h_spec_nn : ∀ x ∈ spectrum ℝ a, (0 : ℝ) ≤ x :=
    spectrum_nonneg_of_nonneg ha
  have h1_cont : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (spectrum ℝ a) := continuousOn_const
  have hinv_cont : ContinuousOn (fun x : ℝ => (1 + x)⁻¹) (spectrum ℝ a) := by
    refine (continuousOn_const.add continuousOn_id).inv₀ ?_
    intro x hx
    have hx_nn := h_spec_nn x hx
    simp only [id]
    linarith
  -- cfc (fun x => 1 - (1+x)⁻¹) a = 1 - cfc (fun x => (1+x)⁻¹) a
  rw [cfc_sub (fun _ : ℝ => (1 : ℝ)) (fun x => (1 + x)⁻¹) a h1_cont hinv_cont]
  rw [cfc_const (R := ℝ) (1 : ℝ) a]
  rw [show (algebraMap ℝ A) (1 : ℝ) = (1 : A) from map_one _]
  -- Now: 1 - cfc (fun x => (1+x)⁻¹) a = 1 - ((u⁻¹ : Aˣ) : A)
  congr 1
  -- Goal: cfc (fun x : ℝ => (1 + x)⁻¹) a = ((u⁻¹ : Aˣ) : A)
  have h_image_pos : ∀ y ∈ (fun x : ℝ => 1 + x) '' (spectrum ℝ a), (0 : ℝ) < y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hx_nn := h_spec_nn x hx
    linarith
  -- Apply cfc_comp' with g = ·⁻¹ and f = (1 + ·).
  have h_inv_cont : ContinuousOn (·⁻¹ : ℝ → ℝ) ((fun x : ℝ => 1 + x) '' spectrum ℝ a) := by
    apply continuousOn_id.inv₀
    intro y hy
    have hy_pos := h_image_pos y hy
    simp only [id]
    linarith
  have h_lin_cont : ContinuousOn (fun x : ℝ => 1 + x) (spectrum ℝ a) :=
    continuousOn_const.add continuousOn_id
  rw [show (fun x : ℝ => (1 + x)⁻¹) = (fun x : ℝ => (·⁻¹ : ℝ → ℝ) (1 + x)) from rfl]
  rw [cfc_comp' (·⁻¹ : ℝ → ℝ) (fun x => 1 + x) a h_inv_cont h_lin_cont]
  -- cfc (fun x => 1 + x) a = 1 + a = u
  -- cfc (fun x => 1 + x) a = 1 + a via cfc_const_add
  rw [show (fun x : ℝ => 1 + x) = (fun x : ℝ => (1 : ℝ) + id x) from rfl]
  rw [cfc_const_add (R := ℝ) (1 : ℝ) (id : ℝ → ℝ) a continuousOn_id]
  rw [cfc_id (R := ℝ) a]
  rw [show (algebraMap ℝ A) (1 : ℝ) = (1 : A) from map_one _]
  -- Goal: cfc (·⁻¹) (1 + a) = ((u⁻¹ : Aˣ) : A)
  rw [show (1 + a : A) = (u : A) from hueq.symm]
  exact cfc_inv_id u

end UnitalAmHm

/-! ### Public non-unital target: operator concavity on `Ici 0` -/

section NonUnital

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Unitization

/-- **Operator concavity of the shifted resolvent `x ↦ 1 - (1 + x)⁻¹`.**

For any non-unital C⋆-algebra `A`, the function
`cfcₙ (fun x : ℝ => 1 - (1 + x)⁻¹)` is `ℝ`-concave on `Set.Ici (0 : A)`.

This is the operator analogue of the classical scalar fact that
`t ↦ 1 - (1+t)⁻¹` is concave on `[0, ∞)`. The proof transports the concavity
claim into the unitization `A⁺¹` (where `1` exists), reduces to the
strictly-positive operator AM-HM inequality `CStarAlgebra.amHm_aux`, and
transports back via `Unitization.real_cfcₙ_eq_cfc_inr`. -/
theorem CFC.concaveOn_one_sub_one_add_inv_real :
    ConcaveOn ℝ (Set.Ici (0 : A))
      (cfcₙ (fun x : ℝ => 1 - (1 + x)⁻¹)) := by
  refine ⟨convex_Ici 0, ?_⟩
  intro a (ha : 0 ≤ a) b (hb : 0 ≤ b) u v hu hv huv
  -- Bridge: cfcₙ f a = cfc f (a : A⁺¹) using f 0 = 0.
  have hf0 : (fun x : ℝ => 1 - (1 + x)⁻¹) 0 = 0 := by norm_num
  -- Lift goal to A⁺¹ via inr_le_iff.
  have hab : (0 : A) ≤ u • a + v • b :=
    add_nonneg (smul_nonneg hu ha) (smul_nonneg hv hb)
  -- Self-adjointness for the inr_le_iff application.
  -- cfcₙ at real level produces self-adjoint output (when applied to self-adjoint input).
  have h_lhs_sa : IsSelfAdjoint (u • cfcₙ (fun x : ℝ => 1 - (1 + x)⁻¹) a
      + v • cfcₙ (fun x : ℝ => 1 - (1 + x)⁻¹) b) := by
    refine ((IsSelfAdjoint.all u).smul ?_).add ((IsSelfAdjoint.all v).smul ?_) <;>
      exact cfcₙ_predicate _ _
  have h_rhs_sa : IsSelfAdjoint (cfcₙ (fun x : ℝ => 1 - (1 + x)⁻¹) (u • a + v • b)) :=
    cfcₙ_predicate _ _
  rw [← Unitization.inr_le_iff _ _ h_lhs_sa h_rhs_sa]
  -- Now lift cfcₙ to cfc on A⁺¹.
  -- The LHS has inr on a sum + smul; distribute coercions.
  have h_lhs_dist : ((u • cfcₙ (fun x : ℝ => 1 - (1 + x)⁻¹) a
      + v • cfcₙ (fun x : ℝ => 1 - (1 + x)⁻¹) b : A) : A⁺¹)
    = u • ((cfcₙ (fun x : ℝ => 1 - (1 + x)⁻¹) a : A) : A⁺¹)
      + v • ((cfcₙ (fun x : ℝ => 1 - (1 + x)⁻¹) b : A) : A⁺¹) := by
    rw [Unitization.inr_add ℂ, Unitization.inr_smul ℂ, Unitization.inr_smul ℂ]
  rw [h_lhs_dist]
  rw [Unitization.real_cfcₙ_eq_cfc_inr a _ hf0,
      Unitization.real_cfcₙ_eq_cfc_inr b _ hf0,
      Unitization.real_cfcₙ_eq_cfc_inr (u • a + v • b) _ hf0]
  -- Inr of u•a + v•b = u • (a : A⁺¹) + v • (b : A⁺¹).
  have h_inr_sum : ((u • a + v • b : A) : A⁺¹) = u • (a : A⁺¹) + v • (b : A⁺¹) := by
    rw [Unitization.inr_add ℂ, Unitization.inr_smul ℂ, Unitization.inr_smul ℂ]
  rw [h_inr_sum]
  -- Lift to A⁺¹ — both (a : A⁺¹) and (b : A⁺¹) are nonneg there.
  have ha' : (0 : A⁺¹) ≤ (a : A⁺¹) := inr_nonneg_iff.mpr ha
  have hb' : (0 : A⁺¹) ≤ (b : A⁺¹) := inr_nonneg_iff.mpr hb
  have hab' : (0 : A⁺¹) ≤ u • (a : A⁺¹) + v • (b : A⁺¹) :=
    add_nonneg (smul_nonneg hu ha') (smul_nonneg hv hb')
  -- Rewrite each cfc via cfc_one_sub_one_add_inv_eq.
  rw [cfc_one_sub_one_add_inv_eq ha', cfc_one_sub_one_add_inv_eq hb',
      cfc_one_sub_one_add_inv_eq hab']
  -- Now goal is in terms of u_a := (1 + a)⁻¹, u_b := (1 + b)⁻¹, u_ab := (1 + u•a + v•b)⁻¹.
  -- We need: u • (1 - u_a⁻¹) + v • (1 - u_b⁻¹) ≤ 1 - u_ab⁻¹.
  -- Equivalent: u_ab⁻¹ ≤ u • u_a⁻¹ + v • u_b⁻¹  (after subtracting from 1 and linearity).
  -- Set up the three units.
  set U_a : (A⁺¹)ˣ := (IsStrictlyPositive.add_nonneg isStrictlyPositive_one ha'
      ).isUnit.unit with hU_a_def
  set U_b : (A⁺¹)ˣ := (IsStrictlyPositive.add_nonneg isStrictlyPositive_one hb'
      ).isUnit.unit with hU_b_def
  set U_ab : (A⁺¹)ˣ := (IsStrictlyPositive.add_nonneg isStrictlyPositive_one hab'
      ).isUnit.unit with hU_ab_def
  -- U_a, U_b are positive.
  have hU_a_eq : (U_a : A⁺¹) = 1 + (a : A⁺¹) := IsUnit.unit_spec _
  have hU_b_eq : (U_b : A⁺¹) = 1 + (b : A⁺¹) := IsUnit.unit_spec _
  have hU_ab_eq : (U_ab : A⁺¹) = 1 + (u • (a : A⁺¹) + v • (b : A⁺¹)) := IsUnit.unit_spec _
  have hU_a_pos : (0 : A⁺¹) ≤ (U_a : A⁺¹) := by
    rw [hU_a_eq]; exact (IsStrictlyPositive.add_nonneg isStrictlyPositive_one ha').nonneg
  have hU_b_pos : (0 : A⁺¹) ≤ (U_b : A⁺¹) := by
    rw [hU_b_eq]; exact (IsStrictlyPositive.add_nonneg isStrictlyPositive_one hb').nonneg
  -- Apply amHm_aux: ((U_ab)⁻¹ : A⁺¹) ≤ u • U_a⁻¹ + v • U_b⁻¹.
  have hU_ab_form : (U_ab : A⁺¹) = u • (U_a : A⁺¹) + v • (U_b : A⁺¹) := by
    rw [hU_ab_eq, hU_a_eq, hU_b_eq]
    rw [smul_add, smul_add]
    rw [show u • (1 : A⁺¹) + u • (a : A⁺¹) + (v • (1 : A⁺¹) + v • (b : A⁺¹))
        = (u + v) • (1 : A⁺¹) + (u • (a : A⁺¹) + v • (b : A⁺¹)) from by
          rw [add_smul]; abel]
    rw [huv, one_smul]
  have hamhm :=
    CStarAlgebra.amHm_aux (X := U_a) (Y := U_b) hU_a_pos hU_b_pos hu hv huv hU_ab_form
  -- hamhm : ((U_ab⁻¹ : Aˣ) : A⁺¹) ≤ u • ((U_a⁻¹ : Aˣ) : A⁺¹) + v • ((U_b⁻¹ : Aˣ) : A⁺¹)
  -- Goal: u • (1 - ((U_a⁻¹ : Aˣ) : A⁺¹)) + v • (1 - ((U_b⁻¹ : Aˣ) : A⁺¹))
  --     ≤ 1 - ((U_ab⁻¹ : Aˣ) : A⁺¹)
  -- From hamhm: subtract from u+v=1 on left:
  --   1 - (u • ↑U_a⁻¹ + v • ↑U_b⁻¹) ≤ 1 - ↑U_ab⁻¹
  --   (since 1 = u + v = (u+v)•1 = u•1 + v•1, we have
  --   u•(1 - ↑U_a⁻¹) + v•(1 - ↑U_b⁻¹) = u•1 + v•1 - (u•↑U_a⁻¹ + v•↑U_b⁻¹) = 1 - (...))
  have hLHS : u • ((1 : A⁺¹) - ((U_a⁻¹ : (A⁺¹)ˣ) : A⁺¹))
    + v • ((1 : A⁺¹) - ((U_b⁻¹ : (A⁺¹)ˣ) : A⁺¹))
    = (1 : A⁺¹) - (u • ((U_a⁻¹ : (A⁺¹)ˣ) : A⁺¹)
      + v • ((U_b⁻¹ : (A⁺¹)ˣ) : A⁺¹)) := by
    rw [smul_sub, smul_sub]
    have h1 : u • (1 : A⁺¹) + v • (1 : A⁺¹) = (1 : A⁺¹) := by
      rw [← add_smul, huv, one_smul]
    -- LHS = u•1 - u•U_a⁻¹ + (v•1 - v•U_b⁻¹) = (u•1 + v•1) - (u•U_a⁻¹ + v•U_b⁻¹)
    --     = 1 - (u•U_a⁻¹ + v•U_b⁻¹)
    rw [show u • (1 : A⁺¹) - u • ((U_a⁻¹ : (A⁺¹)ˣ) : A⁺¹)
        + (v • (1 : A⁺¹) - v • ((U_b⁻¹ : (A⁺¹)ˣ) : A⁺¹))
      = u • (1 : A⁺¹) + v • (1 : A⁺¹) - (u • ((U_a⁻¹ : (A⁺¹)ˣ) : A⁺¹)
        + v • ((U_b⁻¹ : (A⁺¹)ˣ) : A⁺¹)) from by abel]
    rw [h1]
  rw [hLHS]
  exact sub_le_sub_left hamhm 1

end NonUnital

end LTFP.MathlibExt.MatrixAnalysis
