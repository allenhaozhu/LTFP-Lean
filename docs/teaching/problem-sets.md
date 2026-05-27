# Problem-set curriculum guide

This document is the teacher-facing companion to
[`tasks/student-problems/README.md`](https://github.com/allenhaozhu/LTFP-Lean/blob/textbook-strict/tasks/student-problems/README.md).
It expands each problem with a per-problem rubric, suggested grading
notes, and pointers to alternative proof routes.

The starter pack contains five problems spanning Bach (2024) Chapters
1, 5, 7, 14, and 15. They are chosen to give a representative slice of
LTlib's chapter coverage without requiring students to install or
understand the full Mathlib stack.

| # | Bach | File | Difficulty | Expected length |
|---|---|---|---|---|
| 1 | §1.2.1 | `ch01-bernstein-warmup.lean` | Easy | 1-3 lines |
| 2 | §5.1 | `ch05-gd-descent.lean` | Medium | 3-6 lines |
| 3 | §7.2 | `ch07-representer.lean` | Medium | 2-4 lines |
| 4 | §14.4.2 | `ch14-pac-bayes-step1.lean` | Medium-Hard | 1-3 lines |
| 5 | §15.1 | `ch15-pinsker-bh.lean` | Medium-Hard | 1-2 lines |

The "Easy" vs "Medium" vs "Medium-Hard" rating reflects **finding the
right tactic and Mathlib lemma**, not the underlying mathematical
content. Mathematically, all five are textbook lemmas a student would
recognize.

## Grading protocol

All five problems are designed to grade mechanically via `lake build`,
with a follow-up visual inspection to confirm the student did not
introduce escape hatches.

**Step 1 (mechanical).** Run `lake build LTFP.<module>` from the repo
root after replacing `sorry` with the student's proof. If the build
succeeds (exit 0), the proof type-checks against the rest of LTlib.

**Step 2 (visual inspection).** Open the student's file and check for:

* No `sorry`, `admit`, or `#exit` anywhere in the file.
* No `axiom` declarations.
* If the student introduced any `have` or auxiliary lemma, it is
  fully proved (no nested `sorry`).
* The proof does not use `decide` on a goal that requires actual
  reasoning (a common shortcut on classical-logic flagged goals).

**Step 3 (optional, recommended).** Run `#print axioms
student_problem_chXX_<name>` and confirm only the standard Mathlib
axioms appear (typically `propext`, `Classical.choice`, `Quot.sound`).
Any additional axiom is a red flag.

Faculty are encouraged to maintain a solution branch in a private fork
for grading reference; the public repository contains stubs only.

## Problem 1 --- Bach §1.2.1 Bernstein/Hoeffding MGF warm-up

**File.** [`tasks/student-problems/ch01-bernstein-warmup.lean`](https://github.com/allenhaozhu/LTFP-Lean/blob/textbook-strict/tasks/student-problems/ch01-bernstein-warmup.lean)

**Difficulty.** Easy.

**Expected proof length.** 1-3 lines.

**Bach reference.** §1.2.3, p. 14, Lemma 1.2.3(a) (the textbook-strict
Taylor-expansion MGF bound for a centered, bounded random variable).

**What the problem asks.** Given a centered random variable
`Z : Ω → ℝ` with `|Z| ≤ c` a.s., variance `σ² = ∫ Z² dμ`, and a real
`s` with `|s|·c < 3`, prove that

```
∫ exp(s·Z) dμ  ≤  exp( s² · σ² / (2(1 - |s|·c/3)) ).
```

**Suggested LTlib lemma.** `ProbabilityTheory.bach_taylor_mgf` in
`LTFP/MathlibExt/Probability/Moments/BernsteinTextbook.lean`. The
carrier's conclusion matches the target exactly when σ² is supplied
together with its definitional equation `hsigma2_def : sigma2 = ∫ Z² dμ`.

**Reference solution sketch.**

```lean
theorem student_problem_ch01_bernstein_mgf ... := by
  refine bach_taylor_mgf Z hZ_meas c hc h_bdd h_centered
    (∫ ω, (Z ω) ^ 2 ∂μ) rfl s hsc
```

The trick is supplying `rfl` as `hsigma2_def`, since the goal uses
`∫ Z² dμ` directly rather than introducing a named `sigma2` variable.

**Common pitfalls.**

* Students may try to invoke a Mathlib Hoeffding lemma directly
  (`ProbabilityTheory.HasSubgaussianMGF.mgf_le`) and get stuck because
  the LTlib statement uses Bach's specific `(2(1 - |s|c/3))` form,
  not the standard `s²c²/2` Hoeffding form. Steer them toward the
  textbook-strict carrier `bach_taylor_mgf`.
* Forgetting the `hsigma2_def` argument and getting a type-mismatch
  error. The carrier needs σ² supplied as an argument together with
  its definitional equation.

**Rubric.** Full credit: build passes, `#print axioms` clean, proof is
≤ 3 lines. Partial credit (75%): build passes but proof is unusually
long (>10 lines) or uses unnecessary intermediate `have` blocks.
Partial credit (50%): proof has a single substantive `sorry`-like gap
(e.g., `linarith` failure that the student worked around with
`decide`). Zero credit: any `sorry` or `admit`.

## Problem 2 --- Bach §5.1 GD canonical-step descent

**File.** [`tasks/student-problems/ch05-gd-descent.lean`](https://github.com/allenhaozhu/LTFP-Lean/blob/textbook-strict/tasks/student-problems/ch05-gd-descent.lean)

**Difficulty.** Medium.

**Expected proof length.** 3-6 lines.

**Bach reference.** §5.1, p. 142 (the L-smooth descent lemma at the
canonical step `η = 1/L`).

**What the problem asks.** For an L-smooth function `f : E → ℝ` on an
inner-product space, one step of gradient descent at the canonical step
`η = 1/L` yields

```
f(x - (1/L) ∇f(x))  ≤  f(x) - (1/(2L)) · ‖∇f(x)‖².
```

The general-step version
`LTFP.gd_descent_lemma_of_lipschitz_gradient_diff` covers any admissible
`η ∈ [0, 2/L]`. The exercise is to instantiate at `η = 1/L` and verify
that the prefactor `η(1 - Lη/2)` collapses to `1/(2L)`.

**Suggested LTlib lemma.**
`LTFP.gd_descent_lemma_of_lipschitz_gradient_diff` in
`LTFP/Ch05_Optimization/GD.lean`.

**Reference solution sketch.**

```lean
theorem student_problem_ch05_gd_canonical_descent ... := by
  have h := LTFP.gd_descent_lemma_of_lipschitz_gradient_diff
    f L x (1 / (L : ℝ)) hDiff hLip
    (by positivity) (by ...)
  have hL_ne : (L : ℝ) ≠ 0 := ne_of_gt hL
  convert h using 2
  field_simp
  ring
```

The shape: invoke the general-step lemma at `η := 1/L`, then close the
algebraic gap `(1/L)(1 - L(1/L)/2) = 1/(2L)` using `field_simp` + `ring`
(both relying on `hL : 0 < (L : ℝ)`).

**Common pitfalls.**

* Forgetting that `L : NNReal` needs coercion to `ℝ` consistently.
  The hypothesis `hL : 0 < (L : ℝ)` is the form `field_simp` needs.
* Trying to use `gd_descent_canonical_step` (a separate LTlib carrier
  that already does the algebraic collapse) without checking its exact
  conclusion shape. This is a valid alternative route but requires
  more care matching hypotheses.
* `field_simp` failing because the student didn't supply the `L ≠ 0`
  side-condition.

**Rubric.** Full credit: build passes, ≤ 6 lines, no unnecessary `have`
blocks. Partial credit (75%): proof works but uses `nlinarith` or
`polyrith` as a sledgehammer where `ring` would suffice (signals
incomplete understanding of the algebra). Partial credit (50%): proof
chains through `gd_descent_canonical_step` but doesn't simplify the
algebraic obligation cleanly.

## Problem 3 --- Bach §7.2 Representer theorem (minimizer form)

**File.** [`tasks/student-problems/ch07-representer.lean`](https://github.com/allenhaozhu/LTFP-Lean/blob/textbook-strict/tasks/student-problems/ch07-representer.lean)

**Difficulty.** Medium.

**Expected proof length.** 2-4 lines.

**Bach reference.** §7.2, p. 217, Proposition 7.2 (the representer
theorem: any minimizer of a regularized empirical-risk functional lies
in the span of the training feature vectors).

**What the problem asks.** For a real inner-product space `E` with
training feature vectors `e : Fin n → E`, regularization `Ω` that is
non-decreasing on `[0, ∞)`, and a global minimizer `f` of
`J(g) := L((⟨g, eⱼ⟩)ⱼ) + Ω(‖g‖)`, prove there exists `g*` in the span
`span ℝ {e₁, …, eₙ}` with `J(g*) = J(f)`.

**Suggested LTlib lemma.** `LTFP.representer_theorem_minimizer` in
`LTFP/Ch07_Kernels/Representer.lean`.

**Reference solution sketch.**

```lean
theorem student_problem_ch07_representer_minimizer ... := by
  exact LTFP.representer_theorem_minimizer e L Ω hΩ f hf
```

The carrier's signature matches the problem exactly; this is a "find
the right lemma" exercise.

**Common pitfalls.**

* The
  `[(Submodule.span ℝ (Set.range e)).HasOrthogonalProjection]` typeclass
  instance is required. The problem's `variable` block exposes it; if
  the student moves the instance to an explicit argument, the call to
  `representer_theorem_minimizer` will not fire automatically.
* The `Ω` hypothesis is `non-decreasing on [0, ∞)`, not "monotone
  everywhere" --- the latter is a stronger hypothesis the textbook does
  not need. The Lean carrier matches the weaker textbook hypothesis;
  students who try to "strengthen" Ω will get type-mismatch errors.

**Rubric.** Full credit: build passes, ≤ 4 lines, calls
`representer_theorem_minimizer` directly. Partial credit (75%): proof
works but recasts hypotheses unnecessarily (e.g., introduces a new
typeclass instance via `haveI`). Partial credit (50%): proof reproves
parts of the carrier inline rather than invoking it.

## Problem 4 --- Bach §14.4.2 PAC-Bayes Step 1

**File.** [`tasks/student-problems/ch14-pac-bayes-step1.lean`](https://github.com/allenhaozhu/LTFP-Lean/blob/textbook-strict/tasks/student-problems/ch14-pac-bayes-step1.lean)

**Difficulty.** Medium-Hard.

**Expected proof length.** 1-3 lines.

**Bach reference.** §14.4.2, p. 424, Eq. 14.4 (per-θ Hoeffding MGF in
the four-step PAC-Bayes chain).

**What the problem asks.** For a single fixed hypothesis θ whose loss
`ℓ : 𝒳 → ℝ` is `[0, ℓ∞]`-bounded a.s. under the data distribution `D`,
prove the per-θ Hoeffding MGF bound:

```
∫_S exp(s · gap(S)) dDⁿ(S)  ≤  exp( s² · ℓ∞² / (8n) ),
```

where `gap(S) := R(θ) - R̂ₙ(θ, S) = (∫ ℓ dD) - (1/n) Σᵢ ℓ(Sᵢ)`.

**Suggested LTlib lemma.**
`LTFP.pac_bayes_bach_step1_hoeffding_per_theta` in
`LTFP/Ch14_Probabilistic/PACBayes.lean`.

**Reference solution sketch.**

```lean
theorem student_problem_ch14_pac_bayes_step1 ... := by
  exact LTFP.pac_bayes_bach_step1_hoeffding_per_theta
    D ℓ hℓ_meas linf hbdd hn s
```

**Common pitfalls.**

* Sign convention: Bach (2024) Eq. 14.4 uses
  `gap = R - R̂_n` (population minus empirical), not `R̂_n - R`. The
  carrier matches this orientation; students who negate get the wrong
  conclusion.
* The product measure `Measure.pi (fun _ => D)` is the `n`-fold iid
  product. Students unfamiliar with `Measure.pi` may try to use
  `D.prod D.prod ...` (the binary product, repeated) and get stuck on
  the fact that this is *not* the same measure as the `n`-fold product
  for `n > 2`.

**Rubric.** Full credit: build passes, ≤ 3 lines, calls
`pac_bayes_bach_step1_hoeffding_per_theta` directly. Partial credit
(75%): proof works but unfolds the product measure manually. Partial
credit (50%): proof attempts to re-derive the Hoeffding sub-Gaussian
bound from scratch instead of invoking the carrier.

## Problem 5 --- Bach §15.1 Pinsker / Bretagnolle-Huber

**File.** [`tasks/student-problems/ch15-pinsker-bh.lean`](https://github.com/allenhaozhu/LTFP-Lean/blob/textbook-strict/tasks/student-problems/ch15-pinsker-bh.lean)

**Difficulty.** Medium-Hard.

**Expected proof length.** 1-2 lines.

**Bach reference.** §15.1, p. 434 (the weak Pinsker / Bretagnolle-Huber
inequality `tvDist ≤ √KL`).

**What the problem asks.** For two probability measures `μ, ν` on a
measurable space `α` with `μ ≪ ν` and finite KL divergence, prove

```
tvDist(μ, ν)  ≤  √( KL(μ ‖ ν) ).
```

This is the **unconditional weak form** --- it holds without the Csiszár
scalar lower bound that would tighten the bound to `√(KL/2)` (classical
Pinsker).

**Suggested LTlib lemma.** `LTFP.tvDist_le_sqrt_klDiv` in
`LTFP/Ch15_LowerBounds/Statistical.lean`.

**Reference solution sketch.**

```lean
theorem student_problem_ch15_pinsker_bh ... := by
  exact LTFP.tvDist_le_sqrt_klDiv μ ν hμν hkl
```

**Common pitfalls.**

* Trying to use `pinsker_inequality_tvDist` (the tighter Mathlib form
  `tvDist ≤ √(KL/2)`) without supplying its Csiszár scalar hypothesis.
  This problem targets the weaker unconditional form, where no
  additional hypothesis is needed.
* `ENNReal` vs `Real` confusion. The conclusion is on
  `.toReal` of both sides; the underlying `ENNReal` versions are in
  Mathlib's `Mathlib.InformationTheory.KullbackLeibler.Basic`. Stay
  in `toReal` land for this exercise.
* Forgetting `hkl : klDiv μ ν ≠ ∞` and getting stuck on a `toReal` of
  infinity going to `0`.

**Rubric.** Full credit: build passes, ≤ 2 lines, calls
`tvDist_le_sqrt_klDiv` directly. Partial credit (75%): proof works but
chains through the underlying Bretagnolle-Huber carrier
`tvDist_le_sqrt_one_sub_exp_neg_klDiv` plus the algebraic bound
`1 - exp(-x) ≤ x` explicitly --- a valid alternative route. Partial
credit (50%): proof attempts to re-derive the Bhattacharyya chain from
scratch instead of invoking either carrier.

## Suggested course sequencing

For a one-semester ML theory course meeting weekly, here is one possible
LTlib-integrated sequence:

| Week | Topic | LTlib material |
|---|---|---|
| 1 | Course intro, Lean setup | Install VS Code + Lean, clone repo |
| 3 | Concentration | Read `LTFP/Examples/Bernstein.lean` |
| 4 | Concentration (PSet 1) | Solve `ch01-bernstein-warmup.lean` |
| 6 | Optimization | Read `LTFP/Ch05_Optimization/GD.lean` |
| 7 | Optimization (PSet 2) | Solve `ch05-gd-descent.lean` |
| 9 | Kernels | Read `LTFP/Ch07_Kernels/Representer.lean` |
| 10 | Kernels (PSet 3) | Solve `ch07-representer.lean` |
| 12 | PAC-Bayes | Read `LTFP/Examples/PACBayesMcAllester.lean` |
| 13 | PAC-Bayes (PSet 4) | Solve `ch14-pac-bayes-step1.lean` |
| 14 | Lower bounds | Read `LTFP/Examples/PinskerBH.lean` |
| 15 | Lower bounds (PSet 5) | Solve `ch15-pinsker-bh.lean` |

This pairs each problem set with a prior reading week, giving students
2-3 hours to absorb the relevant LTlib carrier theorems before
attempting the exercise.

## Contributing new problems

See [`TEACHING.md`](../TEACHING.md#contributing-tutorials-and-problems-back)
for the contribution workflow. New problems should:

1. Have a stable Lean signature (no `Type*` if it can be avoided ---
   prefer concrete `Type u` with named universes).
2. Cite a specific Bach section and page.
3. Suggest 1-2 LTlib carriers as hints.
4. List 2-3 common pitfalls based on testing with a real student.
5. Have an expected proof length under 10 lines (otherwise the
   exercise is too open-ended for mechanical grading).
6. Update `tasks/student-problems/README.md` with the new row.

Solutions should not be in the public repository; faculty maintain
solutions in a private fork.
