/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
import LTFP.Ch14_Probabilistic.PACBayes

/-!
# LTlib example — Bach §14.4.2 McAllester PAC-Bayes 4-step chain

This file is a *worked walkthrough* of **McAllester's PAC-Bayes bound**
as presented in Bach (2024), *Learning Theory from First Principles*,
§14.4.2, pp. 423-426. We use the named carriers landed in
`LTFP/Ch14_Probabilistic/PACBayes.lean`:

* `LTFP.pac_bayes_bach_step1_hoeffding_per_theta` — Bach Step 1
  (Hoeffding's MGF bound per-θ, Bach Eq. (14.4));
* `LTFP.pac_bayes_bach_step2_integrate_prior` — Bach Step 2
  (integrate the per-θ MGF bound over the prior `q`);
* `LTFP.pac_bayes_mcallester_bach_path_a_class` — the A-class
  carrier composing all four steps into McAllester's bound
  (Bach Eq. (14.6)).

It is **pedagogical**: every `example` here unfolds a named step,
with rich inline commentary tying each step back to Bach's textbook
derivation.

## How to read this file

Open it in VS Code with the Lean 4 extension. Place the cursor on each
`example`, `#check`, or `exact` and the infoview shows the goal at
that step. Reading load: ≈1 hour. This is the heaviest of the three
walkthroughs because Bach's proof has four conceptual steps.

## Bach's 4-step proof of McAllester's PAC-Bayes (book pp. 423-426)

Bach derives McAllester's posterior-vs-prior PAC-Bayes bound from
four textbook steps. Throughout, let:

* `D` = data distribution on the input space `𝒳`;
* `Θ` = hypothesis-index space;
* `q` = a fixed *prior* on Θ;
* `ρ` = the (chosen) *posterior* on Θ, with `ρ ≪ q`;
* `ℓ : Θ → 𝒳 → ℝ` = the bounded loss family,
  `ℓ(θ, x) ∈ [0, ℓ∞]` a.s.;
* `gap(θ, S) := R(θ) − R̂ₙ(θ, S) = ∫ ℓ(θ, x) dD(x) − (1/n) Σ ℓ(θ, Sᵢ)`.

### Step 1 — Per-θ Hoeffding MGF bound (Bach Eq. (14.4))

For each fixed θ, the centered gap `gap(θ, ·)` is a bounded iid
average; Hoeffding's MGF lemma gives
    `∫ exp(s · gap(θ, S)) dDⁿ(S)  ≤  exp(s² · ℓ∞² / (8 n))`.
Formalised: `pac_bayes_bach_step1_hoeffding_per_theta`.

### Step 2 — Integrate over the prior `q` (Bach §14.4.2 line 2 of proof)

Since the Step 1 bound is uniform in θ, integrating against the prior
`q` (a probability measure) preserves it:
    `∫ ∫ exp(s · gap(θ, S)) dDⁿ(S) dq(θ)  ≤  exp(s² · ℓ∞² / (8 n))`.
Formalised: `pac_bayes_bach_step2_integrate_prior`.

### Step 3 — Donsker–Varadhan per-sample (Bach Eq. (14.5))

For each fixed sample `S`, the **Donsker–Varadhan variational
inequality** lifts the integrated MGF bound to a per-posterior bound:
    `s · ∫ gap(θ, S) dρ(θ)  ≤  KL(ρ ‖ q) + log(∫ exp(s · gap) dq)`.
Combined with the integrated MGF bound from Step 2, this gives the
post-Chernoff form (per-sample):
    `s · ∫ gap dρ  −  KL(ρ ‖ q)  ≤  s² · ℓ∞² / (8 n)`.

### Step 4 — Optimise `s` and average over `S` (Bach Eq. (14.6))

Choosing the optimal Chernoff exponent collapses the bound; averaging
over `S ∼ Dⁿ` and dividing by `s` gives the McAllester bound:
    `E_S [ ∫ gap dρ ]  ≤  KL(ρ ‖ q) / s  +  s · ℓ∞² / (8 n)`.

The A-class carrier `pac_bayes_mcallester_bach_path_a_class` discharges
all four steps; intermediates are exposed as their own theorems for
pedagogy and for downstream callers who want to plug in a different
sub-step (e.g., a different MGF bound).

## The carrier theorems used

```text
LTFP.pac_bayes_bach_step1_hoeffding_per_theta
  {𝒳 : Type*} [MeasurableSpace 𝒳]
  (D : Measure 𝒳) [IsProbabilityMeasure D]
  (ℓ : 𝒳 → ℝ) (hℓ_meas : Measurable ℓ)
  (linf : ℝ) (hbdd : ∀ᵐ x ∂D, ℓ x ∈ Set.Icc (0 : ℝ) linf)
  {n : ℕ} (hn : 0 < n) (s : ℝ) :
    ∫ S, Real.exp (s * ((∫ x, ℓ x ∂D) -
            (1 / (n : ℝ)) * ∑ i : Fin n, ℓ (S i)))
          ∂(Measure.pi (fun _ : Fin n => D))
      ≤ Real.exp (s ^ 2 * (linf ^ 2 / (8 * (n : ℝ))))

LTFP.pac_bayes_bach_step2_integrate_prior
  {Θ S : Type*} [MeasurableSpace Θ] [MeasurableSpace S]
  (q : Measure Θ) [IsProbabilityMeasure q]
  (P_S : Measure S) (gap : Θ → S → ℝ) (s K : ℝ)
  (h_per_θ : ∀ θ, ∫ x, Real.exp (s * gap θ x) ∂P_S ≤ Real.exp (s ^ 2 * K))
  (h_inner_int : Integrable (fun θ => ∫ x, Real.exp (s * gap θ x) ∂P_S) q) :
    ∫ θ, (∫ x, Real.exp (s * gap θ x) ∂P_S) ∂q ≤ Real.exp (s ^ 2 * K)
```

The A-class composition is exposed as
`LTFP.pac_bayes_mcallester_bach_path_a_class`; see its docstring in
`PACBayes.lean` for the (long) signature.

-/

open MeasureTheory InformationTheory

namespace LTFP.Examples.PACBayesMcAllester

universe u v

variable {𝒳 Θ : Type u} [MeasurableSpace 𝒳] [MeasurableSpace Θ]

/-! ### Step 0 — Sanity-check the named carriers exist with the
expected signatures. -/

-- Step 1 — Hoeffding MGF per-θ (Bach Eq. (14.4)).
#check @LTFP.pac_bayes_bach_step1_hoeffding_per_theta

-- Step 2 — Integrate the per-θ MGF bound over the prior `q`.
#check @LTFP.pac_bayes_bach_step2_integrate_prior

-- Step 1+2+3+4 — McAllester PAC-Bayes (Bach Eq. (14.6), A-class).
#check @LTFP.pac_bayes_mcallester_bach_path_a_class

/-! ### Step 1 walkthrough — per-θ Hoeffding MGF bound.

For a single hypothesis θ, the centered gap is iid-average-shaped, so
Hoeffding's MGF lemma applies directly. The exponent is the
**Bach-Hoeffding constant** `ℓ∞² / (8n)`, which is the Hoeffding
sub-Gaussian variance proxy for a `[0, ℓ∞]`-bounded random variable
averaged over `n` iid samples.

We expose the call shape exactly as Bach writes it on p. 423.
-/

example
    (D : Measure 𝒳) [IsProbabilityMeasure D]
    (ℓ : 𝒳 → ℝ) (hℓ_meas : Measurable ℓ)
    (linf : ℝ)
    (hbdd : ∀ᵐ x ∂D, ℓ x ∈ Set.Icc (0 : ℝ) linf)
    {n : ℕ} (hn : 0 < n) (s : ℝ) :
    ∫ S, Real.exp (s * ((∫ x, ℓ x ∂D) -
            (1 / (n : ℝ)) * ∑ i : Fin n, ℓ (S i)))
          ∂(Measure.pi (fun _ : Fin n => D))
      ≤ Real.exp (s ^ 2 * (linf ^ 2 / (8 * (n : ℝ)))) := by
  -- Discharge with the named carrier. The proof inside the carrier is
  -- the standard Mathlib `HasSubgaussianMGF.sum_of_iIndepFun` chain
  -- applied to centered summands `Yᵢ(S) := R(θ) - ℓ(Sᵢ)`.
  exact LTFP.pac_bayes_bach_step1_hoeffding_per_theta D ℓ hℓ_meas linf
    hbdd hn s

/-! ### Step 2 walkthrough — integrate the Step-1 bound over a prior.

Step 2 takes the per-θ Hoeffding MGF bound (Step 1's output) and
integrates over a prior `q` on Θ. Because `q` is a *probability*
measure and the Step-1 RHS is θ-free, the integration is trivial — the
constant `exp(s²K)` passes through `∫ · dq` unchanged.

The mathematical content of Step 2 is **zero new probability**; it is
purely a "for-each-θ → expectation-over-θ" lifting. We expose it as a
named theorem because it is a load-bearing step in Bach's textbook
derivation and a clean abstraction for callers.
-/

example
    {S : Type v} [MeasurableSpace S]
    (q : Measure Θ) [IsProbabilityMeasure q]
    (P_S : Measure S)
    (gap : Θ → S → ℝ) (s K : ℝ)
    (h_per_θ :
      ∀ θ, ∫ x, Real.exp (s * gap θ x) ∂P_S ≤ Real.exp (s ^ 2 * K))
    (h_inner_int :
      Integrable (fun θ => ∫ x, Real.exp (s * gap θ x) ∂P_S) q) :
    ∫ θ, (∫ x, Real.exp (s * gap θ x) ∂P_S) ∂q
      ≤ Real.exp (s ^ 2 * K) := by
  -- Single-line discharge — the carrier's proof is
  -- `integral_mono_ae` against the constant `exp(s²K)`, then
  -- `integral_const` collapses the outer `∫ _ dq`.
  exact LTFP.pac_bayes_bach_step2_integrate_prior q P_S gap s K
    h_per_θ h_inner_int

/-! ### Step 1+2 composed — the joint MGF bound feeding into Step 3.

This `example` shows how Steps 1 and 2 chain. We rely *only* on Step 1
to discharge the per-θ hypothesis of Step 2, then invoke Step 2.

(Note: in Bach's textbook the chain ends with a Fubini swap that is
absorbed inside the A-class carrier
`pac_bayes_mcallester_bach_path_a_class`; we do not redo it here.
This example shows the inner `∫_θ ∫_S` form, *before* the swap.)
-/

example
    (D : Measure 𝒳) [IsProbabilityMeasure D]
    (q : Measure Θ) [IsProbabilityMeasure q]
    (ℓ : Θ → 𝒳 → ℝ) (hℓ_meas : ∀ θ, Measurable (ℓ θ))
    (linf : ℝ)
    (hbdd : ∀ θ, ∀ᵐ x ∂D, ℓ θ x ∈ Set.Icc (0 : ℝ) linf)
    {n : ℕ} (hn : 0 < n) (s : ℝ)
    (h_inner_int :
      Integrable (fun θ =>
        ∫ S, Real.exp (s * ((∫ x, ℓ θ x ∂D)
              - (1 / (n : ℝ)) * ∑ i : Fin n, ℓ θ (S i)))
            ∂(Measure.pi (fun _ : Fin n => D))) q) :
    ∫ θ, (∫ S, Real.exp (s * ((∫ x, ℓ θ x ∂D)
            - (1 / (n : ℝ)) * ∑ i : Fin n, ℓ θ (S i)))
          ∂(Measure.pi (fun _ : Fin n => D))) ∂q
      ≤ Real.exp (s ^ 2 * (linf ^ 2 / (8 * (n : ℝ)))) := by
  -- Apply Step 2 with `gap θ S = R(θ) - R̂ₙ(θ, S)` and
  -- `K = ℓ∞² / (8n)`. The per-θ hypothesis is exactly Step 1.
  refine LTFP.pac_bayes_bach_step2_integrate_prior
    (gap := fun θ S => (∫ x, ℓ θ x ∂D)
            - (1 / (n : ℝ)) * ∑ i : Fin n, ℓ θ (S i))
    (K := linf ^ 2 / (8 * (n : ℝ)))
    q (Measure.pi (fun _ : Fin n => D)) s ?_ h_inner_int
  -- The per-θ hypothesis is Step 1, applied uniformly in θ.
  intro θ
  exact LTFP.pac_bayes_bach_step1_hoeffding_per_theta D (ℓ θ)
    (hℓ_meas θ) linf (hbdd θ) hn s

/-! ### Steps 3+4 — the McAllester A-class carrier.

The full McAllester bound (Bach Eq. (14.6)) composes Steps 1–2 above
with Step 3 (Donsker–Varadhan per-sample) and Step 4 (Chernoff
optimisation, averaged over `S ∼ Dⁿ`). The A-class carrier
`pac_bayes_mcallester_bach_path_a_class` discharges all four steps.

The only hypotheses left are the **standard probability-theoretic
integrability conditions** required by Fubini and Donsker–Varadhan;
no Bach-specific named hypotheses remain.

Read this `example` as the **statement** of Bach's McAllester PAC-Bayes
theorem, with the proof outsourced to the named carrier.
-/

example
    (D : Measure 𝒳) [IsProbabilityMeasure D]
    (q ρ : Measure Θ)
    [IsProbabilityMeasure q] [IsProbabilityMeasure ρ]
    (hρq : ρ.AbsolutelyContinuous q)
    (ℓ : Θ → 𝒳 → ℝ) (hℓ_meas : ∀ θ, Measurable (ℓ θ))
    (linf : ℝ)
    (hbdd : ∀ θ, ∀ᵐ x ∂D, ℓ θ x ∈ Set.Icc (0 : ℝ) linf)
    {n : ℕ} (hn : 0 < n)
    {s : ℝ} (hs_pos : 0 < s)
    (h_exp_joint_int :
      Integrable
        (fun p : Θ × (Fin n → 𝒳) =>
          Real.exp (s * ((∫ x, ℓ p.1 x ∂D)
            - (1 / (n : ℝ)) * ∑ i : Fin n, ℓ p.1 (p.2 i))))
        (q.prod (Measure.pi (fun _ : Fin n => D))))
    (h_gap_joint_int :
      Integrable
        (fun p : Θ × (Fin n → 𝒳) =>
          (∫ x, ℓ p.1 x ∂D)
            - (1 / (n : ℝ)) * ∑ i : Fin n, ℓ p.1 (p.2 i))
        (ρ.prod (Measure.pi (fun _ : Fin n => D))))
    (hllr_int : Integrable (MeasureTheory.llr ρ q) ρ)
    (hMGF_int_PS :
      Integrable
        (fun S : Fin n → 𝒳 =>
          Real.log (∫ θ, Real.exp (s * ((∫ x, ℓ θ x ∂D)
              - (1 / (n : ℝ)) * ∑ i : Fin n, ℓ θ (S i))) ∂q))
        (Measure.pi (fun _ : Fin n => D))) :
    ∫ S, (∫ θ, ((∫ x, ℓ θ x ∂D)
          - (1 / (n : ℝ)) * ∑ i : Fin n, ℓ θ (S i)) ∂ρ)
        ∂(Measure.pi (fun _ : Fin n => D))
      ≤ (klDiv ρ q).toReal / s
          + s * (linf ^ 2 / (8 * (n : ℝ))) := by
  -- The four-step Bach proof — Hoeffding MGF per-θ → integrate over q
  -- → Fubini swap → Donsker–Varadhan per-sample → Chernoff
  -- optimisation averaged over S — is fully encapsulated by the named
  -- A-class carrier. Cursor on `pac_bayes_mcallester_bach_path_a_class`
  -- and the infoview shows the exact 13-hypothesis signature.
  exact LTFP.pac_bayes_mcallester_bach_path_a_class D q ρ hρq ℓ
    hℓ_meas linf hbdd hn hs_pos h_exp_joint_int h_gap_joint_int
    hllr_int hMGF_int_PS

end LTFP.Examples.PACBayesMcAllester
