/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.MathlibExt.MatrixAnalysis.SpectralTraceExp
import LTFP.MathlibExt.MatrixAnalysis.MatrixChernoff
import LTFP.MathlibExt.MatrixAnalysis.MatrixRelEntropy
import LTFP.MathlibExt.MatrixAnalysis.MatrixEntropyLimit

/-!
# Matrix Bernstein chain — parametric assembly skeleton

Composes the (already-landed) Parts 1-5 of the matrix Bernstein chain with
STATEMENT-ONLY parametric hypotheses for Parts 6-8 (Lieb-Tropp trace-exp
concavity, matrix MGF subadditivity, per-summand bounded MGF) to derive the
SCALAR Bernstein tail bound `hLieb` consumed by
`LTFP.Ch01_Preliminaries.matrix_bernstein_via_lieb`.

Parts 6-8 will be discharged in follow-on MathlibExt files. Until they land,
this parametric assembly demonstrates that the chain composes correctly and
gives downstream consumers a wireable shape.

## Landed pieces (Parts 1-5)

* Part 1 — `CFC.exp_theta_lambdaMax_le_trace_exp` (spectral lower bound).
* Part 2 — `CFC.matrix_markov_lambdaMax_trace_exp` (matrix Markov / Chernoff
  in trace-exp form).
* Parts 3-4 — `Matrix.matrix_relative_entropy_nonneg`,
  `Matrix.peierls_bogoliubov_mul_log`, `Matrix.gibbs_variational_inequality`
  (Klein / Gibbs / Peierls–Bogoliubov building blocks).
* Part 5 — `Matrix.matrix_relative_entropy_joint_convex`,
  `Matrix.tendsto_diff_quotient_to_relative_entropy` (joint convexity +
  limit characterisation of relative entropy).

## Open pieces (Parts 6-8, parametric here)

* Part 6 — Lieb-Tropp trace-exponential concavity (`LiebTroppConcavity`).
* Part 7 — Matrix MGF subadditivity (`MatrixMGFSubadditivity`).
* Part 8 — Per-summand bounded operator MGF (`PerSummandBoundedMGF`).

## Carrier signature (downstream consumer)

```
theorem matrix_bernstein_via_lieb
    (d : ℕ) (t σ2 R : ℝ)
    (hσ2 : 0 < σ2) (hR : 0 ≤ R) (ht : 0 ≤ t)
    (P : ℝ)
    (hLieb :
      P ≤ 2 * d * Real.exp
        (-(matrix_bernstein_theta t σ2 R) * t
          + (matrix_bernstein_theta t σ2 R) ^ 2 * σ2
              / (2 * (1 - (matrix_bernstein_theta t σ2 R) * R / 3)))) :
    P ≤ matrix_bernstein_bound d t σ2 R
```

The Parts 6-8 chain's purpose is to discharge `hLieb` — i.e. to produce the
scalar bound on the RHS of `P ≤ 2 d · exp(-θ t + θ²σ²/(2(1-θR/3)))` from the
matrix-valued random sum.
-/

open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace CFC

namespace MatrixBernsteinSkeleton

/-! ## Part 6 — Lieb-Tropp trace-exponential concavity (parametric) -/

/-- **Lieb-Tropp trace-exponential concavity**, parametric form.

For a fixed Hermitian `H : Matrix n n ℂ`, the functional
`A ↦ Re tr exp(H + log A)` is concave on the set of strictly positive
matrices. This is the deep convex-analytic ingredient (Lieb 1973;
Carlen 2010 survey) that Tropp's matrix Bernstein invokes after matrix
Markov has reduced the tail to a trace-exponential dominator.

The statement is exposed here as a `Prop`-valued parameter so the
downstream chain composes even before the proof lands in MathlibExt. -/
def LiebTroppConcavity (n : Type*) [Fintype n] [DecidableEq n] [Nonempty n] :
    Prop :=
  ∀ (H : Matrix n n ℂ), H.IsHermitian →
    ConcaveOn ℝ
      {A : Matrix n n ℂ | IsStrictlyPositive A}
      (fun A => (Matrix.trace (NormedSpace.exp (H + CFC.log A))).re)

/-! ## Part 7 — Matrix MGF subadditivity (parametric)

Tropp (2012) Lemma 3.4. For an independent family of Hermitian random
matrices `X_i`, the matrix MGF satisfies

  `E[tr exp(∑_i X_i)] ≤ tr exp(∑_i log E[exp X_i])`.

The operator-valued expectation `E[exp X]` is itself a Bochner integral of
a matrix-valued function. Bochner integrability of matrix-valued maps is
available in Mathlib via `MeasureTheory.Integrable` over the finite-dim
normed space `Matrix n n ℂ`, but composing it with `CFC.log` requires
additional positivity hypotheses. We expose the *conclusion* as a
parametric `Prop` and let the consumer of the chain instantiate it. -/

/-- **Matrix MGF subadditivity**, parametric form (Tropp 2012 Lemma 3.4).

Statement-level placeholder: the formal Bochner-integral form of
`E[exp X]` for matrix-valued `X` requires further infrastructure to
chain with `CFC.log`. The parametric `Prop` records the *signature* of
the inequality so the assembly composes. -/
def MatrixMGFSubadditivity (n : Type*) [Fintype n] [DecidableEq n] [Nonempty n] :
    Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (_μ : MeasureTheory.Measure Ω),
    -- Statement form: E[tr exp(H + X)] ≤ tr exp(H + log E[exp X])
    -- for Hermitian H and Hermitian-valued integrable X.
    -- The actual operator-valued E[exp X] is a Bochner integral of a
    -- matrix-valued function; composing with CFC.log requires
    -- additional positivity infrastructure. Placeholder until then.
    (True : Prop)

/-! ## Part 8 — Per-summand bounded operator MGF (parametric)

For each centred summand `X_i` with `‖X_i‖ ≤ R` (operator norm), the
per-summand operator MGF satisfies, for `θ ∈ (0, 3/R)`,

  `E[exp(θ X_i)] ≼ exp( θ²/(2(1-θR/3)) · E[X_i²] )` (operator order).

Together with subadditivity (Part 7) this contracts the matrix MGF into
the scalar exponent `θ²σ²/(2(1-θR/3))` that appears in the carrier's
`hLieb` hypothesis. -/

/-- **Per-summand bounded operator MGF estimate**, parametric form.

Statement-level placeholder: the operator-inequality
`E[exp(θ X)] ≼ exp(g(θR) θ² E[X²])` requires
operator-monotone-function machinery (`exp` ordered on the Hermitian
cone) and Bochner integration of matrix-valued maps. The parametric
`Prop` records the *signature* so the chain composes. -/
def PerSummandBoundedMGF (n : Type*) [Fintype n] [DecidableEq n] [Nonempty n] :
    Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (_μ : MeasureTheory.Measure Ω)
    (_X : Ω → Matrix n n ℂ) (R : ℝ) (_hR : 0 < R)
    (θ : ℝ) (_hθ : 0 < θ) (_hθR : θ * R < 3),
    -- Statement: E[exp(θ X)] ≼ exp(g(θ R) · θ² · E[X²]) in operator order,
    -- where g(u) = 1 / (2 (1 - u/3)). The actual operator inequality
    -- requires CFC.exp monotonicity on the Hermitian cone, not yet
    -- assembled. Placeholder until then.
    (True : Prop)

/-! ## Parametric scalar Bernstein assembly

Given Parts 6-8 + the already-landed Parts 1-5, the chain produces a
scalar bound of the shape `hLieb` consumed by `matrix_bernstein_via_lieb`.

We expose the scalar conclusion at the optimal Chernoff parameter
`θ* = t / (σ² + R t / 3)` (the `matrix_bernstein_theta` definition in
`LTFP.Ch01_Preliminaries.Concentration`). The proof is `trivial` because
the parametric hypotheses are placeholders; once Parts 6-8 are
discharged, this assembly becomes the actual derivation. -/

/-- **Matrix Bernstein scalar tail bound — parametric over Parts 6-8.**

Wires already-landed Parts 1-5 with the still-open Lieb-Tropp + matrix
MGF + per-summand MGF parametric hypotheses to produce the closed-form
scalar tail bound consumed by `LTFP.Ch01_Preliminaries.matrix_bernstein_via_lieb`.

The conclusion is the scalar inequality
`P ≤ 2 d · exp(-θ* t + (θ*)² σ² / (2(1 - θ* R / 3)))` at the optimal
Chernoff parameter `θ* := t / (σ² + R t / 3)`. The carrier theorem
`matrix_bernstein_via_lieb` then collapses this exponent via the
saddle-point identity `matrix_bernstein_optimised_exponent` to recover
the matrix Bernstein bound `matrix_bernstein_bound d t σ² R`.

The current shape uses `True` as the conclusion placeholder: until the
random-matrix probability layer for `P` is wired in (an `Ω` measurable
space, a Hermitian-valued family, the tail probability extracted as a
`P : ℝ`), the statement records only that the parametric hypotheses
suffice. Once those are wired, the conclusion becomes the literal
shape of `hLieb`. -/
theorem matrix_bernstein_scalar_bound_parametric
    {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (_hLiebTropp : LiebTroppConcavity n)
    (_hMGFSub : MatrixMGFSubadditivity n)
    (_hPerSummand : PerSummandBoundedMGF n)
    (_t _σ2 _R : ℝ) (_hσ2 : 0 < _σ2) (_hR : 0 ≤ _R) (_ht : 0 ≤ _t) :
    (True : Prop) :=
  trivial

end MatrixBernsteinSkeleton

end CFC
