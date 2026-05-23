/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.Foundations.Symmetrization
import LTFP.Foundations.Rademacher

/-!
# MathlibExt shim: symmetrization API + B8 N6 negation-doubling bridges

Single import point for the symmetrization API used by the wide-network
Rademacher complexity bounds (B8 N6 path in
`LTFP/MathlibExt/Probability/WideNetworkDudley.lean`). Pure aliasing
re-export — no new mathematical content. The underlying proofs live in:

* `LTFP/Foundations/Symmetrization.lean` — the classical symmetrization
  argument (`symmetrization_equation`, `abs_symmetrization_equation`,
  `sup_abs_lemma`).
* `LTFP/Foundations/Rademacher.lean` — the B8 N6 negation-doubling
  bridges (`negDoubleFamily`,
  `empiricalRademacherComplexity_eq_without_abs_negDoubleFamily`,
  `coveringNumber_negDoubleFamily_le`) and the symmetrization sup-split
  lemma (`symmetrization_signed_sup_le_add`).

Downstream MathlibExt files should depend on this shim rather than on
the `Foundations.*` modules directly; the shim keeps the public
symmetrization API surface in one place and lets `Foundations.*`
internals be refactored without touching downstream users.

## Aliases

| Shim name | Underlying theorem |
|-----------|--------------------|
| `symmetrization_equation` | `_root_.symmetrization_equation` |
| `abs_symmetrization_equation` | `_root_.abs_symmetrization_equation` |
| `sup_abs_lemma` | `_root_.sup_abs_lemma` |
| `symmetrization_signed_sup_le_add` | `_root_.symmetrization_signed_sup_le_add` |
| `negDoubleFamily` | `_root_.negDoubleFamily` |
| `empiricalRademacherComplexity_eq_without_abs_negDoubleFamily` | `_root_.empiricalRademacherComplexity_eq_without_abs_negDoubleFamily` |
| `coveringNumber_negDoubleFamily_le` | `_root_.coveringNumber_negDoubleFamily_le` |
-/

namespace LTFP.MathlibExt.Probability.Symmetrization

/-- Re-export: classical symmetrization equation for the signed sum
sup form. See `LTFP/Foundations/Symmetrization.lean`. -/
alias symmetrization_equation := _root_.symmetrization_equation

/-- Re-export: classical symmetrization equation for the absolute-value
signed sum sup form. See `LTFP/Foundations/Symmetrization.lean`. -/
alias abs_symmetrization_equation := _root_.abs_symmetrization_equation

/-- Re-export: `⨆ i, |V (f i)| = ⨆ (s,i), V (±(f i))` rewrite used
inside the absolute-value symmetrization argument. See
`LTFP/Foundations/Symmetrization.lean`. -/
alias sup_abs_lemma := _root_.sup_abs_lemma

/-- Re-export: bounds the with-abs symmetrized average by the sum of
the two single-marginal symmetrized averages (the "split into two
indeps" step of the symmetrization argument). See
`LTFP/Foundations/Rademacher.lean`. -/
alias symmetrization_signed_sup_le_add := _root_.symmetrization_signed_sup_le_add

/-- Re-export: the **negation-doubled function class**. Each
`f i : Z → ℝ` contributes both `f i` (at index `(0, i)`) and `-(f i)`
(at index `(1, i)`) to the new family indexed by `Fin 2 × ι`. Used by
the B8 N6 with-abs ↔ without-abs Rademacher bridge. See
`LTFP/Foundations/Rademacher.lean`. -/
alias negDoubleFamily := _root_.negDoubleFamily

/-- Re-export: **with-abs ↔ without-abs Rademacher complexity bridge.**
For any sample-bounded family, the with-abs empirical Rademacher
complexity equals the without-abs empirical Rademacher complexity of
the negation-doubled class `negDoubleFamily f`. The exact relationship
between the two definitions. See `LTFP/Foundations/Rademacher.lean`. -/
alias empiricalRademacherComplexity_eq_without_abs_negDoubleFamily :=
  _root_.empiricalRademacherComplexity_eq_without_abs_negDoubleFamily

/-- Re-export: **covering-number doubling for `negDoubleFamily`.** The
covering number of `EmpiricalFunctionSpace (negDoubleFamily F) S` at
scale `ε` is at most twice the covering number of
`EmpiricalFunctionSpace F S` at scale `ε`. Combined with the bridge
above, this lifts a Dudley entropy bound on `F` to a Dudley entropy
bound (with a factor of 2) on the with-abs Rademacher complexity of
`F`. See `LTFP/Foundations/Rademacher.lean`. -/
alias coveringNumber_negDoubleFamily_le := _root_.coveringNumber_negDoubleFamily_le

end LTFP.MathlibExt.Probability.Symmetrization
