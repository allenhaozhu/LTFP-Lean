# Walkthrough: Bach §14.4.2 McAllester PAC-Bayes (textbook-strict)

This walkthrough re-tells the proof carried by
[`LTFP/Examples/PACBayesMcAllester.lean`](https://github.com/allenhaozhu/LTFP-Lean/blob/textbook-strict/LTFP/Examples/PACBayesMcAllester.lean)
in prose, with Lean code snippets interspersed. It is meant to be read
**alongside** the Lean file: open the file in VS Code with the Lean 4
extension and step through with the infoview while reading this
narrative.

Reference: Francis Bach (2024), *Learning Theory from First Principles*
(MIT Press), §14.4.2, pp. 423-426.

## What PAC-Bayes is, and why this matters

Classical PAC bounds control the generalization gap of a *single*
hypothesis. PAC-Bayes bounds the **expected gap under a distribution
over hypotheses** --- a *posterior* `ρ` selected after seeing the data,
relative to a *prior* `q` fixed before. The first such bound is due to
McAllester (1998-1999); Bach (§14.4.2) presents the modern derivation
via four steps: per-θ Hoeffding MGF, integrate over the prior,
Donsker-Varadhan variational inequality, and Chernoff optimization.

PAC-Bayes is the deepest of the three flagship examples in
`LTFP/Examples/` because each of the four steps is a non-trivial
probability-theoretic statement, and the composition requires careful
Fubini accounting. The textbook handles this in a few paragraphs; the
Lean port surfaces every measurability and integrability hypothesis
explicitly, which is what makes it a useful pedagogical reading.

## Notation

Throughout this walkthrough and the corresponding Lean file:

* `D` --- the data distribution on input space `𝒳`;
* `Θ` --- the hypothesis-index space;
* `q : Measure Θ` --- the fixed *prior* on Θ;
* `ρ : Measure Θ` --- the chosen *posterior* on Θ, with `ρ ≪ q`;
* `ℓ : Θ → 𝒳 → ℝ` --- the bounded loss family, with `ℓ(θ, x) ∈ [0, ℓ∞]`
  a.s. under `D`;
* `R(θ) := ∫ ℓ(θ, x) dD(x)` --- the population risk of hypothesis θ;
* `R̂ₙ(θ, S) := (1/n) Σᵢ ℓ(θ, Sᵢ)` --- the empirical risk on sample
  `S = (S₁, …, Sₙ)`;
* `gap(θ, S) := R(θ) − R̂ₙ(θ, S)` --- the centered generalization gap.

The goal: prove

```
E_{S ∼ Dⁿ} [ ∫ gap(θ, S) dρ(θ) ]  ≤  KL(ρ ‖ q) / s  +  s · ℓ∞² / (8n)
```

for every `s > 0` (Bach Eq. 14.6). Optimizing in `s` recovers the
standard McAllester form `2√( KL(ρ ‖ q) · ℓ∞² / (8n) )`, but the
non-optimized form above is the one the carrier proves.

## The four-step proof structure

Each step is formalized as its own named carrier. The full bound is
the composition.

| Step | Name | What it says |
|---|---|---|
| 1 | `pac_bayes_bach_step1_hoeffding_per_theta` | Per-θ Hoeffding MGF |
| 2 | `pac_bayes_bach_step2_integrate_prior` | Integrate Step 1 over q |
| 3 | (Donsker-Varadhan, in carrier) | Variational dual for KL |
| 4 | (Chernoff, in carrier) | Optimize the MGF exponent |
| 1+2+3+4 | `pac_bayes_mcallester_bach_path_a_class` | A-class composite |

## Step 1 --- Per-θ Hoeffding MGF (Bach Eq. 14.4)

**Claim.** Fix a hypothesis θ. The centered gap `gap(θ, ·)` is an
average of `n` iid `[−ℓ∞, ℓ∞]`-bounded random variables (each
`ℓ(θ, Sᵢ) - R(θ)`), so Hoeffding's MGF lemma applies:

```
E_{S ∼ Dⁿ} [ exp(s · gap(θ, S)) ]  ≤  exp( s² · ℓ∞² / (8n) ).
```

The `ℓ∞² / (8n)` is the **Hoeffding sub-Gaussian variance proxy** for a
`[0, ℓ∞]`-bounded random variable averaged over `n` samples: the `8`
comes from the standard Hoeffding lemma `Var ≤ (b-a)²/4` combined with
the `1/(2n)` from averaging.

**Lean signature.**

```lean
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
  exact LTFP.pac_bayes_bach_step1_hoeffding_per_theta D ℓ hℓ_meas linf
    hbdd hn s
```

**Proof idea.** The carrier internally invokes Mathlib's generic
sub-Gaussian summation machinery
(`HasSubgaussianMGF.sum_of_iIndepFun`) on the centered summands
`Yᵢ(S) := R(θ) - ℓ(θ, Sᵢ)`. Each `Yᵢ` is bounded by `ℓ∞`, has zero
mean (by definition of `R(θ)`), and is independent of the others under
the product measure `Dⁿ`. The sub-Gaussian variance proxy of the
average is the per-summand proxy divided by `n` --- yielding
`ℓ∞² / (8n)`.

**Why we name this step.** The mathematical content is "Hoeffding's
MGF, instantiated at our specific shape `R(θ) - R̂ₙ(θ, S)`". The naming
exists so downstream callers who want to replace Hoeffding with a
different MGF (e.g., the Bernstein MGF from
`LTFP/Examples/Bernstein.lean`) can swap Step 1 alone, leaving Steps
2-4 untouched.

## Step 2 --- Integrate the per-θ bound over the prior

**Claim.** Step 1's bound is uniform in θ. Integrating against a
probability measure `q` on Θ therefore preserves the bound:

```
∫_θ E_{S ∼ Dⁿ} [ exp(s · gap(θ, S)) ] dq(θ)  ≤  exp( s² · ℓ∞² / (8n) ).
```

**Lean signature.**

```lean
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
  exact LTFP.pac_bayes_bach_step2_integrate_prior q P_S gap s K
    h_per_θ h_inner_int
```

**Proof idea.** The carrier's proof is `integral_mono_ae` against the
constant `exp(s²K)`, then `integral_const` collapses the outer integral
against `q` (a probability measure) back to the constant. The
integrability hypothesis `h_inner_int` is needed to apply
`integral_mono_ae`; in practice it follows from the boundedness
hypothesis on `ℓ`, but we expose it explicitly because nothing in the
abstract `gap : Θ → S → ℝ` signature constrains it.

**Why we name this step.** The mathematical content is zero new
probability --- it is purely a "for-each-θ ↦ expectation-over-θ"
lifting. We name it because it is a textbook step in Bach's chain
(Bach §14.4.2 line 2 of the proof: "integrating against `q`...") and
because abstracting it lets us state the per-sample bound that feeds
Step 3.

## Step 1 + Step 2 composed

The composition gives a joint MGF bound integrated over both θ and S:

```lean
example
    (D : Measure 𝒳) [IsProbabilityMeasure D]
    (q : Measure Θ) [IsProbabilityMeasure q]
    (ℓ : Θ → 𝒳 → ℝ) (hℓ_meas : ∀ θ, Measurable (ℓ θ))
    (linf : ℝ)
    (hbdd : ∀ θ, ∀ᵐ x ∂D, ℓ θ x ∈ Set.Icc (0 : ℝ) linf)
    {n : ℕ} (hn : 0 < n) (s : ℝ)
    (h_inner_int : Integrable (fun θ => ...) q) :
    ∫ θ, (∫ S, Real.exp (s * ((∫ x, ℓ θ x ∂D)
            - (1 / (n : ℝ)) * ∑ i : Fin n, ℓ θ (S i)))
          ∂(Measure.pi (fun _ : Fin n => D))) ∂q
      ≤ Real.exp (s ^ 2 * (linf ^ 2 / (8 * (n : ℝ)))) := by
  refine LTFP.pac_bayes_bach_step2_integrate_prior
    (gap := fun θ S => (∫ x, ℓ θ x ∂D)
            - (1 / (n : ℝ)) * ∑ i : Fin n, ℓ θ (S i))
    (K := linf ^ 2 / (8 * (n : ℝ)))
    q (Measure.pi (fun _ : Fin n => D)) s ?_ h_inner_int
  intro θ
  exact LTFP.pac_bayes_bach_step1_hoeffding_per_theta D (ℓ θ)
    (hℓ_meas θ) linf (hbdd θ) hn s
```

Note the shape: Step 2's "per-θ" hypothesis is discharged by feeding
Step 1 at each θ. This is the textbook "Step 1 ↦ Step 2" composition.
The Lean version makes the discharge explicit; the textbook glosses
over it with "since the bound is uniform in θ...".

A **Fubini swap** happens between this `∫_θ ∫_S` form and the
`∫_S ∫_θ` form that feeds Step 3. The swap is absorbed inside the
A-class carrier `pac_bayes_mcallester_bach_path_a_class`; the example
above shows the inner pre-swap form for pedagogy. Fubini requires the
joint integrability hypothesis `h_exp_joint_int` exposed in the
A-class signature below.

## Step 3 --- Donsker-Varadhan variational inequality

**Claim.** The Donsker-Varadhan inequality states that for any
measurable `f : Θ → ℝ` and any probability measures `ρ ≪ q` on Θ,

```
∫ f dρ  ≤  KL(ρ ‖ q)  +  log ( ∫ exp(f) dq ).
```

This is the **dual representation** of KL divergence and the load-
bearing tool that lifts a bound on `q` to a bound on the posterior `ρ`.

Applied to `f := s · gap(θ, S)` for fixed S, with the post-Fubini form
of the Step 1 + 2 bound `∫_θ exp(s·gap(θ,S)) dq ≤ exp(s²K)`, we get
(taking `log` of both sides on the RHS):

```
s · ∫_θ gap(θ, S) dρ(θ)  ≤  KL(ρ ‖ q)  +  log( ∫_θ exp(s·gap(θ,S)) dq )
                          ≤  KL(ρ ‖ q)  +  s² · K   (where K := ℓ∞²/(8n)).
```

**Why the `log` step matters.** Donsker-Varadhan introduces a `log` ---
this is what couples the MGF bound (Step 1 + 2) to the bound on the
*posterior* expectation. Without it, we would have a bound on
`∫ ρ · exp(s·gap) dq`, which is *not* what PAC-Bayes wants.

The Lean carrier inside `pac_bayes_mcallester_bach_path_a_class`
invokes Mathlib's `MeasureTheory.integral_log_exp_le_klDiv_add_log`
(the Donsker-Varadhan form for KL), which is itself a non-trivial
information-theoretic lemma. Its hypotheses (`ρ ≪ q`, `hllr_int`,
`hMGF_int_PS`) are exposed in the A-class signature below.

## Step 4 --- Chernoff optimization and averaging over S

**Claim.** Dividing the Step 3 bound by `s` (positive) gives:

```
∫_θ gap(θ, S) dρ(θ)  ≤  KL(ρ ‖ q) / s  +  s · K.
```

Averaging over `S ∼ Dⁿ`:

```
E_{S ∼ Dⁿ} [ ∫_θ gap(θ, S) dρ(θ) ]  ≤  E_{S} [ KL(ρ ‖ q) / s  +  s · K ]
                                    =  KL(ρ ‖ q) / s  +  s · K,
```

since `KL(ρ ‖ q)` does not depend on S.

**Why the averaging is on the outside.** McAllester's bound is "in
expectation over S". The high-probability form requires a separate
Markov step; the carrier above is the in-expectation form.

## The full A-class carrier

```lean
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
    (h_exp_joint_int : Integrable ... (q.prod (Measure.pi ...)))
    (h_gap_joint_int : Integrable ... (ρ.prod (Measure.pi ...)))
    (hllr_int : Integrable (MeasureTheory.llr ρ q) ρ)
    (hMGF_int_PS : Integrable ... (Measure.pi ...)) :
    ∫ S, (∫ θ, ((∫ x, ℓ θ x ∂D)
          - (1 / (n : ℝ)) * ∑ i : Fin n, ℓ θ (S i)) ∂ρ)
        ∂(Measure.pi (fun _ : Fin n => D))
      ≤ (klDiv ρ q).toReal / s
          + s * (linf ^ 2 / (8 * (n : ℝ))) := by
  exact LTFP.pac_bayes_mcallester_bach_path_a_class D q ρ hρq ℓ
    hℓ_meas linf hbdd hn hs_pos h_exp_joint_int h_gap_joint_int
    hllr_int hMGF_int_PS
```

The 13-hypothesis signature looks intimidating. Breaking it down:

* **Probability hypotheses** (`[IsProbabilityMeasure D/q/ρ]`,
  `hρq : ρ ≪ q`): the modeling setup.
* **Loss-family hypotheses** (`ℓ`, `hℓ_meas`, `linf`, `hbdd`): the
  bounded loss assumption.
* **Sample-size hypothesis** (`hn : 0 < n`): trivially needed for the
  `1/n` average.
* **Optimization scalar** (`hs_pos : 0 < s`): we need to divide by `s`
  in Step 4.
* **Joint integrability** (`h_exp_joint_int`, `h_gap_joint_int`,
  `hMGF_int_PS`): Fubini and Donsker-Varadhan both need these.
* **Log-likelihood integrability** (`hllr_int`): Donsker-Varadhan's
  KL representation needs `log(dρ/dq)` to be ρ-integrable.

The textbook glosses these integrability conditions ("under suitable
regularity..."); the formalization surfaces each one. In practice, for
bounded loss and absolutely continuous ρ ≪ q, all four integrability
conditions follow from boundedness of `ℓ` and finiteness of
`KL(ρ ‖ q)`.

## What students should take away

* **PAC-Bayes is just four ingredients.** Per-θ MGF, integrate over
  prior, Donsker-Varadhan, Chernoff. Each is a textbook tool; the
  novelty is in their composition.
* **Donsker-Varadhan is the lifting step.** Without it, you only have
  a bound on the prior expectation. DV is what makes the posterior
  bound possible --- and DV is exactly the dual representation of KL.
* **Hoeffding gives `ℓ∞² / (8n)`.** If your loss is small-variance,
  switch Step 1 to a Bernstein MGF and you get a tighter bound. The
  modular naming in LTlib supports this swap.
* **Integrability hypotheses matter.** The Lean signature surfaces
  four integrability conditions that the textbook elides. Each
  corresponds to a real measure-theoretic check (Fubini × 2, DV × 1,
  Bochner × 1).
* **The bound is uniform in `s`.** Bach's Eq. 14.6 includes the `s`
  freely. Optimizing in `s` is a separate calculation
  `s* = √( 8n · KL(ρ ‖ q) / ℓ∞² )`, which collapses the bound to
  `2√( KL · ℓ∞² / (8n) )`; this is McAllester's classical statement.

## What this example does NOT cover

* **Catoni's PAC-Bayes form.** Catoni (2007) gives a tighter bound for
  bounded loss using a different optimization. Not in LTlib yet.
* **High-probability vs in-expectation.** This carrier is the
  in-expectation form. The high-probability version (Bach Eq. 14.7)
  requires Markov on top.
* **Data-dependent posteriors.** Bach §14.4.3 covers the case where ρ
  depends on the sample; the carrier above treats ρ as a fixed (data-
  independent) measure, with the data-dependent extension addressed
  by a separate lemma.

For a different worked example showing the Taylor-expansion MGF tool
in isolation, see [`walkthrough-bernstein.md`](walkthrough-bernstein.md).
For the curriculum guide listing all problem sets including the
PAC-Bayes Step-1-only exercise, see
[`problem-sets.md`](problem-sets.md).
