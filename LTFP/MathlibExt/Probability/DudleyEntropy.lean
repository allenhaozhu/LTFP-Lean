/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.Foundations.DudleyEntropy
import LTFP.Foundations.Main

/-!
# MathlibExt shim: Dudley entropy integral

Single import point for the Dudley entropy integral API used by the
wide-network Rademacher complexity bounds (B8 N6 path in
`LTFP/MathlibExt/Probability/WideNetworkDudley.lean`). Pure aliasing
re-export — no new mathematical content. The underlying proofs live in:

* `LTFP/Foundations/DudleyEntropy.lean` — the core Dudley entropy
  integral theorem `dudley_entropy_integral'` bounding the without-abs
  empirical Rademacher complexity by `4ε + 12/√m ∫ √log N(x) dx`.
* `LTFP/Foundations/Main.lean` — public wrappers
  `dudley_entropy_integral_bound` (without-abs, name-aligned) and
  `dudley_entropy_integral_bound_with_abs` (B8 N6 with-abs analogue
  via the `negDoubleFamily` doubling bridge from
  `LTFP/Foundations/Rademacher.lean`).

Downstream MathlibExt files should depend on this shim rather than on
the `Foundations.*` modules directly; the shim keeps the public Dudley
API surface in one place and lets `Foundations.*` internals be
refactored without touching downstream users.

## Aliases

| Shim name | Underlying theorem |
|-----------|--------------------|
| `dudley_entropy_integral'` | `_root_.dudley_entropy_integral'` |
| `dudley_entropy_integral_bound` | `_root_.dudley_entropy_integral_bound` |
| `dudley_entropy_integral_bound_with_abs` | `_root_.dudley_entropy_integral_bound_with_abs` |
-/

namespace LTFP.MathlibExt.Probability.DudleyEntropy

/-- Re-export: **Dudley entropy integral upper bound (without-abs
form).** Bounds the without-abs empirical Rademacher complexity of a
totally-bounded function class by `4ε + 12/√m · ∫_ε^{c/2} √log N(x) dx`
where `N(x)` is the covering number of the empirical function space at
scale `x`. See `LTFP/Foundations/DudleyEntropy.lean`. -/
alias dudley_entropy_integral' := _root_.dudley_entropy_integral'

/-- Re-export: **Dudley entropy integral upper bound (without-abs,
public-facing wrapper).** Name-aligned restatement of
`dudley_entropy_integral'` with the empirical sample index parameter
spelled `n` (matching the rest of `LTFP/Foundations/Main.lean`'s API).
See `LTFP/Foundations/Main.lean`. -/
alias dudley_entropy_integral_bound := _root_.dudley_entropy_integral_bound

/-- Re-export: **Dudley entropy integral upper bound (with-abs form).**
Composes the with-abs ↔ without-abs Rademacher bridge
(`empiricalRademacherComplexity_eq_without_abs_negDoubleFamily`) with
`dudley_entropy_integral'` and the negation-closure covering inflation
(`coveringNumber_negDoubleFamily_le`, factor of 2) to bound the
with-abs empirical Rademacher complexity by the same Dudley entropy
integral expressed in covering numbers of the *original* family `F`
(not the doubled `negDoubleFamily F`), at the cost of a `2 ·` factor
inside the `log`. Downstream chains through
`uniform_deviation_expectation_le_two_smul_rademacher_complexity`
which uses the with-abs definition. See `LTFP/Foundations/Main.lean`. -/
alias dudley_entropy_integral_bound_with_abs :=
  _root_.dudley_entropy_integral_bound_with_abs

end LTFP.MathlibExt.Probability.DudleyEntropy
