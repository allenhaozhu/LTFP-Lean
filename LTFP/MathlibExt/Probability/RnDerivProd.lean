/-
Copyright (c) 2026 LTFP-Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LTFP-Lean contributors
-/
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Radon–Nikodym derivative on product measures

This module proves the product-measure Radon–Nikodym derivative identity
for binary products of σ-finite measures: if `μ ≪ ν` on `α` and `ρ ≪ τ`
on `β`, then the RN derivative of the product measure `μ.prod ρ` with
respect to `ν.prod τ` is the product of the coordinate RN derivatives:

```
(μ.prod ρ).rnDeriv (ν.prod τ)
  =ᵐ[ν.prod τ] fun p ↦ μ.rnDeriv ν p.1 * ρ.rnDeriv τ p.2
```

This is the binary base case for the more general `Measure.rnDeriv_pi`
identity over a finite product (see `RnDerivPi.lean`).

## Main results

* `MeasureTheory.Measure.rnDeriv_prod`: the product-measure RN derivative
  factorisation, stated as an a.e. equality with respect to the
  dominating product measure.

## Proof strategy

The proof is a 3-step composition:

1. Rewrite `μ = ν.withDensity (μ.rnDeriv ν)` and `ρ = τ.withDensity
   (ρ.rnDeriv τ)` via `Measure.withDensity_rnDeriv_eq`.
2. Apply `MeasureTheory.prod_withDensity` to identify
   `μ.prod ρ = (ν.prod τ).withDensity (fun z ↦ μ.rnDeriv ν z.1 * ρ.rnDeriv τ z.2)`.
3. Apply `Measure.rnDeriv_withDensity` to read off the RN derivative.

The σ-finiteness hypotheses on all four measures are needed because
`withDensity_rnDeriv_eq` rests on `HaveLebesgueDecomposition`, whose
canonical instance derives from `[SFinite μ] [SigmaFinite ν]`, and
because the `Measure.prod` construction interacts cleanly with
`withDensity` only under σ-finiteness.

-/

noncomputable section

open MeasureTheory

namespace MeasureTheory

namespace Measure

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- **Radon–Nikodym derivative of a product measure.** If `μ ≪ ν` on `α`
and `ρ ≪ τ` on `β`, with `ν, τ` σ-finite and `μ, ρ` s-finite, then the
Radon–Nikodym derivative of the product `μ.prod ρ` with respect to
`ν.prod τ` factors as the product of the coordinate Radon–Nikodym
derivatives. -/
theorem rnDeriv_prod
    (μ : Measure α) (ν : Measure α) (ρ : Measure β) (τ : Measure β)
    [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ρ] [SigmaFinite τ]
    (hμν : μ ≪ ν) (hρτ : ρ ≪ τ) :
    (μ.prod ρ).rnDeriv (ν.prod τ)
      =ᵐ[ν.prod τ] (fun p : α × β => μ.rnDeriv ν p.1 * ρ.rnDeriv τ p.2) := by
  -- Step 1: rewrite μ and ρ as withDensity of their RN derivatives.
  have hμ : μ = ν.withDensity (μ.rnDeriv ν) := (withDensity_rnDeriv_eq μ ν hμν).symm
  have hρ : ρ = τ.withDensity (ρ.rnDeriv τ) := (withDensity_rnDeriv_eq ρ τ hρτ).symm
  -- Step 2: use prod_withDensity to combine.
  have h_meas_μ : Measurable (μ.rnDeriv ν) := measurable_rnDeriv μ ν
  have h_meas_ρ : Measurable (ρ.rnDeriv τ) := measurable_rnDeriv ρ τ
  have h_prod_eq : μ.prod ρ
      = (ν.prod τ).withDensity (fun z : α × β => μ.rnDeriv ν z.1 * ρ.rnDeriv τ z.2) := by
    conv_lhs => rw [hμ, hρ]
    exact prod_withDensity h_meas_μ h_meas_ρ
  -- Step 3: read off the RN derivative via rnDeriv_withDensity.
  rw [h_prod_eq]
  have h_meas_prod : Measurable
      (fun z : α × β => μ.rnDeriv ν z.1 * ρ.rnDeriv τ z.2) := by
    exact (h_meas_μ.comp measurable_fst).mul (h_meas_ρ.comp measurable_snd)
  exact rnDeriv_withDensity (ν.prod τ) h_meas_prod

end Measure

end MeasureTheory
