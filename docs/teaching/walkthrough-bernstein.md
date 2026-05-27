# Walkthrough: Bach §1.2.3 Bernstein inequality (textbook-strict)

This walkthrough re-tells the proof carried by
[`LTFP/Examples/Bernstein.lean`](https://github.com/allenhaozhu/LTFP-Lean/blob/textbook-strict/LTFP/Examples/Bernstein.lean) in
prose, with Lean code snippets interspersed. It is meant to be read
**alongside** the Lean file: open the file in VS Code with the Lean 4
extension and step through with the infoview while reading this
narrative.

Reference: Francis Bach (2024), *Learning Theory from First Principles*
(MIT Press), §1.2.3, pp. 14-15.

## Where this sits in the textbook

Bach (2024) introduces concentration inequalities in §1.2. Markov gives
the loosest possible bound (`P(X ≥ ε) ≤ E[X]/ε`); Chebyshev tightens it
using the variance; Hoeffding tightens further using the moment-
generating function (MGF) of a bounded random variable; **Bernstein**
sharpens Hoeffding when the variance σ² is small compared to the
amplitude `c`. The Bernstein bound is the one to remember: it
interpolates between a sub-Gaussian regime (when nσ² dominates) and a
sub-exponential regime (when cε dominates), and it dominates Hoeffding
whenever σ² < c²/4.

Bach's exposition of Bernstein hinges on a single technical lemma ---
**Lemma 1.2.3(a)**, the Taylor-expansion MGF bound. Once that lemma is
in hand, the iid sum and Chernoff optimization are routine. The Lean
formalization preserves this structure: a per-summand carrier
`bach_taylor_mgf`, an iid-sum upgrade `bach_taylor_mgf_iid_sum`, and a
final tail bound `bach_bernstein_tail_one_sided`.

## The statement

Let `Z₁, …, Zₙ : Ω → ℝ` be iid, centered, and bounded by `c` almost
surely under a probability measure `μ`, with common variance
`σ² = ∫ Zᵢ² dμ`. Then for every `ε > 0`:

```
μ { ω : ε ≤ ∑ᵢ Zᵢ(ω) }  ≤  exp( -ε² / (2 (nσ² + cε/3)) ).
```

In Lean:

```lean
ProbabilityTheory.bach_bernstein_tail_one_sided
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n : ℕ} (hn : 0 < n) (Z : Fin n → Ω → ℝ)
  (h_indep : iIndepFun Z μ) (h_meas : ∀ i, Measurable (Z i))
  (c : ℝ) (hc : 0 ≤ c) (h_bdd : ∀ i, ∀ᵐ ω ∂μ, |Z i ω| ≤ c)
  (h_centered : ∀ i, ∫ ω, Z i ω ∂μ = 0)
  (sigma2 : ℝ) (hsigma2_pos : 0 < sigma2)
  (h_ident : ∀ i, sigma2 = ∫ ω, (Z i ω) ^ 2 ∂μ)
  (ε : ℝ) (hε : 0 < ε) :
    μ.real {ω | ε ≤ ∑ i : Fin n, Z i ω} ≤
      Real.exp (-ε ^ 2 / (2 * ((n : ℝ) * sigma2 + c * ε / 3)))
```

The 12-hypothesis signature looks heavy, but every hypothesis
corresponds directly to a sentence in Bach's textbook:

* `hn : 0 < n` --- "for a sample of size n";
* `h_indep` --- "let Z₁, …, Zₙ be independent";
* `h_meas` --- "Zᵢ a real-valued random variable" (measurability is
  implicit in the textbook);
* `c`, `hc`, `h_bdd` --- "with `|Zᵢ| ≤ c` a.s.";
* `h_centered` --- "centered" (`E[Zᵢ] = 0`);
* `sigma2`, `hsigma2_pos`, `h_ident` --- "with variance σ²" (in Bach,
  the variance is denoted `σ²` and assumed identical across i);
* `ε`, `hε` --- "for any ε > 0".

The textbook hides the positivity of `σ²`; the Lean port surfaces it
because the proof divides by `σ²` at the Chernoff optimization step.

## The three-step proof structure

Bach proves the Bernstein tail from three textbook lemmas, each
formalized as its own carrier theorem:

1. **Per-summand Taylor-MGF bound** (Lemma 1.2.3(a), `bach_taylor_mgf`).
2. **iid Sum MGF bound** (`bach_taylor_mgf_iid_sum`).
3. **Chernoff optimization** (a single application of the standard
   Chernoff inequality `ProbabilityTheory.measure_ge_le_exp_mul_mgf`).

We walk each step.

## Step 1 --- The per-summand Taylor-MGF bound

**Claim** (Bach Lemma 1.2.3(a)). For a centered random variable `Z`
with `|Z| ≤ c` almost surely and variance `σ² = ∫ Z² dμ`, and for any
real `s` with `|s|·c < 3`,

```
∫ exp(s·Z) dμ  ≤  exp( s²σ² / (2(1 - |s|·c/3)) ).
```

**Lean signature.**

```lean
example
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Z : Ω → ℝ) (hZ_meas : Measurable Z)
    (c : ℝ) (hc : 0 ≤ c)
    (h_bdd : ∀ᵐ ω ∂μ, |Z ω| ≤ c)
    (h_centered : ∫ ω, Z ω ∂μ = 0)
    (sigma2 : ℝ) (hsigma2_def : sigma2 = ∫ ω, (Z ω) ^ 2 ∂μ)
    (s : ℝ) (hsc : |s| * c < 3) :
    ∫ ω, Real.exp (s * Z ω) ∂μ ≤
      Real.exp (s ^ 2 * sigma2 / (2 * (1 - |s| * c / 3))) := by
  exact bach_taylor_mgf Z hZ_meas c hc h_bdd h_centered sigma2
    hsigma2_def s hsc
```

**Proof idea (Bach, p. 14).** The key analytic ingredient is the scalar
inequality

```
exp(y)  ≤  1 + y + y² / (2(1 - |y|/3))   for all |y| < 3,
```

which is the Bach-Bernstein remainder bound. Formalized in
`LTFP.MathlibExt.Analysis.Exp.BernsteinRemainder` as
`Real.exp_le_one_add_self_add_sq_div_of_abs_le`. Apply this pointwise
at `y := s·Z(ω)` and `b := |s|·c`; the hypothesis `|s|·c < 3` ensures
`|y| < 3` almost surely. Integrate over `μ`:

* The constant `1` integrates to `1`;
* The linear term `s·Z(ω)` integrates to `s · ∫ Z dμ = 0` by
  `h_centered`;
* The quadratic term `(s·Z(ω))² / (2(1 - |s|·c/3))` integrates to
  `s² · σ² / (2(1 - |s|·c/3))` by definition of `σ²`.

The result is

```
∫ exp(s·Z) dμ  ≤  1 + s²σ²/(2(1 - |s|·c/3))
              ≤  exp( s²σ²/(2(1 - |s|·c/3)) ),
```

where the last step uses the universal `1 + α ≤ exp α`.

**Why the `3`?** The Bach-Bernstein remainder bound uses the geometric
tail estimate `(m+2)! ≥ 2 · 3^m` (for the Taylor expansion of `exp`).
This produces the `/3` denominator in the lemma --- it is *not* a free
constant; it traces back to a specific factorial estimate. Bach's
`3` is the same constant as in any standard probability text.

## Step 2 --- The iid sum upgrade

**Claim.** For iid centered `Z₁, …, Zₙ` with shared `c` and `σ²`, the
MGF of the sum factors through independence:

```
∫ exp(s · ∑ᵢ Zᵢ) dμ  =  ∏ᵢ ∫ exp(s · Zᵢ) dμ  ≤  exp( n · s²σ² / (2(1 - |s|·c/3)) ).
```

This is the textbook step between Lemma 1.2.3(a) and the displayed
Bernstein tail; Bach handles it implicitly by writing
"`exp(s · ∑ᵢ Zᵢ) = ∏ᵢ exp(s · Zᵢ)` and the iid expectation factors".
The Lean formalization names it `bach_taylor_mgf_iid_sum`.

The proof composes:

* The Mathlib lemma `MeasureTheory.iIndepFun.integral_prod_mul`, which
  factors `∫ ∏ᵢ fᵢ` into `∏ᵢ ∫ fᵢ` under independence;
* `n` copies of Step 1 (one per summand);
* The exponent collapse `(exp α)^n = exp(n·α)`.

This is purely mechanical, but it is named separately because
downstream callers may want to plug in a different per-summand MGF
bound (e.g., the Hoeffding form `exp(s²c²/2)` for the symmetric
sub-Gaussian case) while keeping the rest of the chain.

## Step 3 --- Chernoff optimization

**Claim.** Chaining the iid-sum MGF bound with Chernoff's inequality
and optimizing in `s` gives the Bernstein tail.

**Chernoff** is the standard scalar inequality:

```
μ { ω : ε ≤ X(ω) }  ≤  exp(-s·ε) · ∫ exp(s·X) dμ      for any s > 0.
```

In Lean: `ProbabilityTheory.measure_ge_le_exp_mul_mgf`. Applied with
`X := ∑ᵢ Zᵢ` and the Step 2 bound `∫ exp(s · ∑ᵢ Zᵢ) ≤ exp(ns²σ² /
(2(1 - sc/3)))`:

```
μ { ω : ε ≤ ∑ᵢ Zᵢ(ω) }  ≤  exp( -sε + ns²σ² / (2(1 - sc/3)) ).
```

To minimize the exponent in `s`, take the derivative and set to zero.
The optimal `s` is

```
s*  =  ε / (nσ² + cε/3).
```

Substituting `s*` back collapses the exponent to:

```
-ε² / (2 (nσ² + cε/3)),
```

giving Bach's displayed Bernstein tail. The Lean carrier
`bach_bernstein_tail_one_sided` performs this optimization internally
--- it is a long algebraic manipulation that does not benefit from being
named separately.

## The two-sided version

A union bound on `{|S| ≥ ε} ⊆ {S ≥ ε} ∪ {-S ≥ ε}` gives the two-sided
form with an extra factor of 2:

```lean
example
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} (hn : 0 < n) (Z : Fin n → Ω → ℝ)
    (h_indep : iIndepFun Z μ) (h_meas : ∀ i, Measurable (Z i))
    (c : ℝ) (hc : 0 ≤ c)
    (h_bdd : ∀ i, ∀ᵐ ω ∂μ, |Z i ω| ≤ c)
    (h_centered : ∀ i, ∫ ω, Z i ω ∂μ = 0)
    (sigma2 : ℝ) (hsigma2_pos : 0 < sigma2)
    (h_ident : ∀ i, sigma2 = ∫ ω, (Z i ω) ^ 2 ∂μ)
    (ε : ℝ) (hε : 0 < ε) :
    μ.real {ω | (ε : ℝ) ≤ |∑ i : Fin n, Z i ω|} ≤
      2 * Real.exp (-ε ^ 2 /
        (2 * ((n : ℝ) * sigma2 + c * ε / 3))) := by
  exact bach_bernstein_tail_two_sided hn Z h_indep h_meas c hc h_bdd
    h_centered sigma2 hsigma2_pos h_ident ε hε
```

The carrier `bach_bernstein_tail_two_sided` applies
`bach_bernstein_tail_one_sided` to `Z` and to `-Z`, then takes the
union bound. The `-Z` invocation requires checking that the
hypotheses are preserved under negation: `|−Z| ≤ c` is unchanged,
`∫ -Z = -∫ Z = 0`, and `∫ (-Z)² = ∫ Z² = σ²`. These three checks are
inside the carrier; the example invocation is one line.

## What students should take away

* **Bernstein dominates Hoeffding when σ² is small.** Hoeffding gives
  `exp(-2ε²/(nc²))`; Bernstein gives `exp(-ε²/(2nσ²))` in the small-ε
  regime where `nσ² ≫ cε`. If σ² ≪ c², the gain is substantial.
* **The `c·ε/3` term encodes the sub-exponential regime.** When ε is
  large, `cε/3` dominates `nσ²`, and the exponent decays only
  linearly in ε --- characteristic of sub-exponential (rather than
  sub-Gaussian) tails.
* **Every hypothesis matters.** The Lean proof breaks if any of `iid`,
  `centered`, `bounded`, or `σ² > 0` is dropped. The textbook
  exposition compresses these into a single sentence; the
  formalization makes the dependence explicit.
* **The `3` is not arbitrary.** It is the geometric ratio in the
  Taylor remainder estimate `(m+2)! ≥ 2·3^m`; chasing the constant
  back to its source is a useful exercise.

## What this example does NOT cover

* **Matrix Bernstein.** Bach (2024) §1.2.3 states a non-commutative
  matrix Bernstein bound (Proposition 1.7). The formalization is in
  progress: see `docs/ERRATA.md` for a note on a hypothesis that the
  textbook leaves implicit. The walkthrough above only covers the
  scalar case.
* **Empirical Bernstein.** Audibert-Munos-Szepesvari's data-dependent
  variant (where σ² is replaced by the empirical variance) is in
  Bach §1.2.4 and not yet in LTlib.
* **Sub-exponential class.** A general framework for sub-exponential
  random variables is in
  `LTFP/MathlibExt/Probability/Moments/SubExponential.lean`; Bernstein
  is one instance.

For a different worked example showing how a multi-step proof composes
across information-theoretic steps, see
[`walkthrough-pacbayes.md`](walkthrough-pacbayes.md).
