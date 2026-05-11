/-
LTFP foundation: information theory (re-exports Mathlib KL).

Phase-3a anchor for chapters that need information-theoretic
quantities: Ch 14 (PAC-Bayes — uses KL between posterior and prior)
and Ch 15 (Le Cam / Fano lower bounds — use KL between two
candidate distributions).

Most content here is a thin LTFP-namespace alias over Mathlib's
`InformationTheory.KullbackLeibler` module — we **reuse**.
-/
import Mathlib.InformationTheory.KullbackLeibler.Basic

namespace LTFP

open MeasureTheory InformationTheory

variable {α : Type*} [MeasurableSpace α]

open scoped ENNReal

/-- LTFP alias: KL divergence `D(μ ‖ ν)` between two measures.
    Re-export of `InformationTheory.klDiv` (an `ENNReal`-valued
    `irreducible_def`). Used by Ch 14 (PAC-Bayes) and Ch 15
    (statistical lower bounds). -/
noncomputable abbrev kl (μ ν : Measure α) : ENNReal := klDiv μ ν

/-- §F5 sanity lemma: `D(μ ‖ μ) = 0` for any sigma-finite measure.
    One-liner via `InformationTheory.klDiv_self`. -/
theorem kl_self (μ : Measure α) [SigmaFinite μ] : kl μ μ = 0 :=
  klDiv_self μ

/-- §F5 — KL is `∞` when the first measure is not absolutely
    continuous w.r.t. the second.  Re-export of
    `InformationTheory.klDiv_of_not_ac`. -/
theorem kl_of_not_ac (μ ν : Measure α) (h : ¬ μ ≪ ν) : kl μ ν = ∞ :=
  klDiv_of_not_ac h

/-- §F5 — KL with infinite divergence on right side. -/
theorem kl_zero_right (μ : Measure α) [NeZero μ] : kl μ 0 = ∞ :=
  klDiv_zero_right

/-- §F5 — KL is `∞` ↔ either not absolutely continuous or non-integrable. -/
theorem kl_eq_top_iff (μ ν : Measure α) :
    kl μ ν = ∞ ↔ (μ ≪ ν → ¬ Integrable (llr μ ν) μ) :=
  klDiv_eq_top_iff

/-- §F5 — KL is non-top iff absolutely continuous and integrable. -/
theorem kl_ne_top_iff (μ ν : Measure α) :
    kl μ ν ≠ ∞ ↔ μ ≪ ν ∧ Integrable (llr μ ν) μ :=
  klDiv_ne_top_iff

end LTFP
