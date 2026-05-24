/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.Foundations.Main

/-!
# MathlibExt shim: uniform deviation ≤ 2 · Rademacher complexity

Single import point for the symmetrization-based uniform-deviation
Rademacher bound used by the wide-network chains (B8 N6 path in
`LTFP/MathlibExt/Probability/WideNetworkDudley.lean`). Pure aliasing
re-export — no new mathematical content. The underlying proofs live in
`LTFP/Foundations/Main.lean` and chain through the symmetrization API
from `LTFP/Foundations/Rademacher.lean`.

The shim re-exports the **mean-of-uniform-deviation family**:

* the core bound on the *expected* uniform deviation
  (`uniform_deviation_expectation_le_two_smul_rademacher_complexity`),
* the McDiarmid concentration bound on the *centered* uniform deviation
  (`uniform_deviation_mcdiarmid_tail`),
* the four downstream tail bounds combining mean + concentration:
  countable-class and separable-class flavors, each in raw and
  `_of_pos` (optimized `t = 1/(2b²)`) form.

Downstream MathlibExt files should depend on this shim rather than on
`LTFP.Foundations.Main` directly; the shim keeps the public uniform-
deviation API surface in one place and lets `Foundations.*` internals
be refactored without touching downstream users.

## Aliases

| Shim name | Underlying theorem |
|-----------|--------------------|
| `uniform_deviation_expectation_le_two_smul_rademacher_complexity` | `_root_.uniform_deviation_expectation_le_two_smul_rademacher_complexity` |
| `uniform_deviation_mcdiarmid_tail` | `_root_.uniform_deviation_mcdiarmid_tail` |
| `uniform_deviation_tail_bound_countable` | `_root_.uniform_deviation_tail_bound_countable` |
| `uniform_deviation_tail_bound_countable_of_pos` | `_root_.uniform_deviation_tail_bound_countable_of_pos` |
| `uniform_deviation_tail_bound_separable` | `_root_.uniform_deviation_tail_bound_separable` |
| `uniform_deviation_tail_bound_separable_of_pos` | `_root_.uniform_deviation_tail_bound_separable_of_pos` |
-/

namespace LTFP.MathlibExt.Probability.UniformDeviationRademacher

/-- Re-export: **mean uniform deviation ≤ 2 · Rademacher complexity.**
The expected empirical uniform deviation under the product measure
`μⁿ` is bounded by twice the population Rademacher complexity of the
function class. The symmetrization argument feeding the B8 N6 with-abs
Dudley chain. See `LTFP/Foundations/Main.lean`. -/
alias uniform_deviation_expectation_le_two_smul_rademacher_complexity :=
  _root_.uniform_deviation_expectation_le_two_smul_rademacher_complexity

/-- Re-export: **McDiarmid tail bound on the centered uniform
deviation.** For a class of `[−b, b]`-bounded measurable functions,
the probability that the empirical uniform deviation exceeds its mean
by `ε` is at most `exp(−ε²·t·n)` whenever `t · b² ≤ 1/2`. See
`LTFP/Foundations/Main.lean`. -/
alias uniform_deviation_mcdiarmid_tail :=
  _root_.uniform_deviation_mcdiarmid_tail

/-- Re-export: **countable-class tail bound on the uniform deviation.**
Combines `uniform_deviation_expectation_le_two_smul_rademacher_complexity`
with `uniform_deviation_mcdiarmid_tail` to obtain
`P(2·Rad + ε ≤ supDev) ≤ exp(−ε²·t·n)` for a countable family of
bounded measurable functions. See `LTFP/Foundations/Main.lean`. -/
alias uniform_deviation_tail_bound_countable :=
  _root_.uniform_deviation_tail_bound_countable

/-- Re-export: **optimized countable-class tail bound** with the
explicit choice `t = 1 / (2 b²)`, giving the closed-form rate
`exp(−ε²·n / (2 b²))`. See `LTFP/Foundations/Main.lean`. -/
alias uniform_deviation_tail_bound_countable_of_pos :=
  _root_.uniform_deviation_tail_bound_countable_of_pos

/-- Re-export: **separable-class tail bound on the uniform deviation.**
Lifts the countable tail bound to a separable index space via a dense
sequence and continuity of the family pointwise in the index. See
`LTFP/Foundations/Main.lean`. -/
alias uniform_deviation_tail_bound_separable :=
  _root_.uniform_deviation_tail_bound_separable

/-- Re-export: **optimized separable-class tail bound** with
`t = 1 / (2 b²)`. See `LTFP/Foundations/Main.lean`. -/
alias uniform_deviation_tail_bound_separable_of_pos :=
  _root_.uniform_deviation_tail_bound_separable_of_pos

end LTFP.MathlibExt.Probability.UniformDeviationRademacher
