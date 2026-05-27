# Errata for Bach (2024), *Learning Theory from First Principles*

This file collects discrepancies, ambiguities, and minor corrections
encountered while formalizing the textbook in Lean 4. The intent is
strictly constructive: a proof assistant forces every hypothesis to be
made explicit, and the resulting type signatures occasionally surface
implicit assumptions, off-by-one constants, or notation that could be
clarified in a future edition. Genuine typos are also noted here.

Entries are grouped by chapter. Each entry follows the format below.
Contributions are welcome via pull request.

---

## Entry format

```
### §X.Y[.Z] — <short title>

- **Textbook:** <what the book states>
- **Observation:** <what the formalization made explicit>
- **Suggested clarification:** <one-sentence fix>
- **Lean reference:** `LTFP/Ch<NN>_<Topic>/<File>.lean` (optional)
```

Each entry should be specific (cite a section or page), constructive
(propose a clarification rather than just flag an issue), and brief.
The audience is the textbook author and future readers; keep the tone
neutral and technical.

---

## Chapter 1 — Preliminaries

### §1.2.3 — Proposition 1.7 matrix Bernstein: hypothesis on `M_i` is too weak

- **Textbook:** "`M_i` symmetric, `E[M_i] = 0`, `λ_max(M_i) ≤ c` a.s.,
  `σ² = λ_max((1/n) ∑ E[M_i²])`"; concludes a tail bound on
  `λ_max((1/n) ∑ M_i)`.
- **Observation:** The Tropp matrix-Bernstein MGF chain
  (Tropp 2015, Theorem 6.1.1) requires a two-sided operator-norm bound
  `‖M_i‖_op ≤ c` — equivalently `−c·I ≼ M_i ≼ c·I` — not just
  `λ_max(M_i) ≤ c`. With `E[M_i] = 0` and only `λ_max(M_i) ≤ c`, the
  smallest eigenvalue of `M_i` is unconstrained, so `E[exp(θ M_i)]`
  need not be controlled by `σ² θ² / (1 − c θ / 3)` and the proof
  step breaks down. When formalizing, the hypothesis had to be
  silently strengthened.
- **Suggested clarification:** Replace `λ_max(M_i) ≤ c` with
  `‖M_i‖_op ≤ c`, or state both `λ_max(M_i) ≤ c` *and*
  `λ_min(M_i) ≥ −c`, so the hypothesis matches the MGF lemma actually
  used in the proof.
- **Lean reference:** `LTFP/Ch01_Preliminaries/Concentration.lean`
  (`matrix_bernstein_bound`, docstring and definition).

### §1.2.3 — Proposition 1.6 matrix Hoeffding: `C_i` symmetry left implicit

- **Textbook:** "`M_i² ≼ C_i²` a.s., `σ² = λ_max((1/n) ∑ C_i²)`".
- **Observation:** For `M_i² ≼ C_i²` to be a well-posed PSD-order
  statement, and for `(1/n) ∑ C_i²` to have a real largest eigenvalue,
  the matrices `C_i` must be symmetric (equivalently, Hermitian).
  Otherwise `C_i² = C_i · C_i` and `C_iᵀ · C_i` are distinct objects,
  and `M_i² ≼ C_i²` is ambiguous. The book writes `C_i²` as if `C_i`
  were a scalar; Tropp's theorem requires `C_i` Hermitian.
- **Suggested clarification:** Add "where the `C_i ∈ ℝ^{d×d}` are
  symmetric (equivalently, `C_i²` is positive semidefinite)" to the
  hypothesis list.
- **Lean reference:** `LTFP/Ch01_Preliminaries/Concentration.lean`
  (matrix-Bernstein doc paragraph).

### §1.2.3 — Two `σ²` conventions across Proposition 1.4 and its key lemma

- **Textbook:** Proposition 1.4 defines `σ² = (1/n) ∑ᵢ var(Zᵢ)` — an
  *average* over the sample. The key lemma (a) used in its proof
  writes `σ² = E[Z²]` — a *single-variable* second moment. The same
  symbol is reused without comment.
- **Observation:** A formal proof must apply the key lemma per-variable
  with `sᵢ² = var(Zᵢ) = E[Zᵢ²]` and then sum, recovering `n · σ²` in
  the exponent only because of the averaging convention. This dual
  usage is invisible in the prose and forces a renaming during
  formalization.
- **Suggested clarification:** Either rename the lemma-(a) quantity
  (e.g. `s² = E[Z²]`), or add a sentence noting that applying lemma
  (a) to each `Zᵢ` with `sᵢ² = var(Zᵢ)` and summing yields `n σ²`
  under the average convention.
- **Lean reference:** `LTFP/Ch01_Preliminaries/Concentration.lean`
  (`bernstein_inequality`; the algebraic core uses a single `σ²`
  parameter, masking the per-variable vs. averaged distinction).

### §1.2.3 — Integrability of `exp(s · Z)` in lemma (a) not justified

- **Textbook:** Proposition 1.4's key lemma writes
  `E[exp(s · Z)] ≤ exp((σ²/c²)(exp(s c) − 1 − s c))` without
  justifying that `exp(s · Z)` is integrable.
- **Observation:** The Lean conditional form requires the integrability
  hypothesis `MeasureTheory.Integrable (fun ω => exp(t · X ω)) μ` to
  be supplied explicitly; the Chernoff machinery cannot be invoked
  otherwise. Integrability follows from `|Z| ≤ c` a.s. (so
  `exp(s · Z) ≤ exp(s · c)` a.s.) but the book never says so.
- **Suggested clarification:** Add a one-line remark that
  `exp(s · Z) ≤ exp(s · c)` a.s. under the bounded hypothesis, so the
  MGF is finite.
- **Lean reference:** `LTFP/Ch01_Preliminaries/Concentration.lean`
  (`bernstein_inequality_of_mgf`, hypothesis `h_int`).

### §1.2.3 — Term-by-term expectation in the series expansion of `e^{sZ}`

- **Textbook:** The proof of the key lemma writes "expands
  `e^{s Z} = ∑_k (s Z)^k / k!`" and takes expectation term-by-term,
  without invoking dominated or monotone convergence.
- **Observation:** Interchange of expectation and infinite series is a
  non-trivial step. The bounded hypothesis `|Z| ≤ c` does provide the
  uniform dominator `exp(s · c)`, but the book does not say so. The
  Lean route sidesteps the series argument entirely by taking the MGF
  bound as a hypothesis — precisely because the series-expectation
  interchange is not free.
- **Suggested clarification:** Insert a one-sentence appeal to
  dominated convergence, with dominator `exp(s · c)` (under the
  bounded hypothesis), when moving `E[·]` inside the sum.
- **Lean reference:** `LTFP/Ch01_Preliminaries/Concentration.lean`
  (`bernstein_inequality_of_mgf`).

### §1.2.3 — Lemma 1.2.3(a) is the substantive MGF bound but not labelled

- **Textbook:** §1.2.3 (pp. 14-15) presents the scalar Bernstein
  derivation as one continuous proof. The substantive MGF inequality
  `E[exp(s · Z)] ≤ exp((σ² / c²)(exp(s · c) − 1 − s · c))` (for
  `|Z| ≤ c` a.s., `E[Z] = 0`) — and the Bach-specific Taylor-remainder
  form `≤ exp(s² σ² / (2(1 − |s|c/3)))` derived from it — are presented
  inline as steps inside the Bernstein proof, never assigned a separate
  lemma number.
- **Observation:** When formalizing the textbook-strict variant, this
  per-summand MGF bound has to be extracted as a standalone Lean
  theorem (`bach_taylor_mgf`) so that downstream callers (Bernstein
  tail; PAC-Bayes; matrix Bernstein per-summand) can reuse it without
  re-deriving the Taylor expansion. Readers who follow §1.2.3
  line-by-line lose track of which step is the load-bearing inequality
  reused elsewhere.
- **Suggested clarification:** Label the per-summand Taylor-MGF bound
  as a distinct displayed lemma (e.g., "Lemma 1.2.3(a)") in the text,
  so it can be cited independently from the overall Bernstein tail
  bound that follows from it.
- **Lean reference:**
  `LTFP/MathlibExt/Probability/Moments/BernsteinTextbook.lean`
  (`bach_taylor_mgf`).

### §1.2.3 — Proposition 1.7 matrix Bernstein cited to Tropp 2012 without proof-sketch pointer

- **Textbook:** Proposition 1.7 states the matrix Bernstein bound and
  cites Tropp 2012, Theorem 1.4. No proof sketch is given in §1.2.3.
- **Observation:** The full formal derivation requires three load-
  bearing pieces well beyond the scalar §1.2.3 development:
  (i) Lieb 1973 joint concavity of the trace-exp functional (or the
  Tropp 2012 unnormalized variational reformulation thereof);
  (ii) the matrix MGF chain `tr exp(∑ Mᵢ) ≤ tr exp(∑ Eᵢ[Mᵢ])` derived
  from it via Bochner integration; (iii) a per-summand
  Bennett-Bernstein remainder lifted to Hermitian matrices via the
  continuous functional calculus. Formalizing Proposition 1.7
  end-to-end in LTFP required ~7,000 lines of MathlibExt
  infrastructure. The "cite Tropp" approach is appropriate for a
  textbook but leaves a substantial verification gap that the reader
  cannot recover from the in-book exposition alone.
- **Suggested clarification:** Add a one-paragraph proof sketch in
  §1.2.3 listing the three load-bearing pieces (Lieb-1973 concavity →
  matrix MGF subadditivity chain → per-summand Bennett-Bernstein
  remainder), so a serious reader knows what the citation entails and
  where to look in Tropp 2012 for each piece.
- **Lean reference:**
  `LTFP/MathlibExt/MatrixAnalysis/MatrixBernsteinFinal.lean`
  (`Matrix.bernstein_full`).

### §1.2.5 — Quadrature: two distinct theorems share the section without separate labels

- **Textbook:** §1.2.5 discusses both the left-endpoint Riemann-sum
  bound `L(b − a)² / (2n)` for `L`-Lipschitz integrands and the
  trapezoidal-rule bound `L / (12 n²)` for `C²` integrands with
  `|f''| ≤ L`. These are distinct theorems with different smoothness
  hypotheses, presented in close prose.
- **Observation:** When formalizing, only one variant gets the section's
  identifier. LTFP's carrier `lipschitz_riemann_sum_error` proves the
  left-endpoint Lipschitz variant; the trapezoidal-`C²` variant is a
  different theorem with a faster rate and is not currently formalized.
  Readers may conflate the two when citing "§1.2.5".
- **Suggested clarification:** Label the two variants explicitly (e.g.,
  "Proposition 1.10(a) — left-endpoint, Lipschitz" and
  "Proposition 1.10(b) — trapezoidal, `C²`") so citations are
  unambiguous and the rate-vs-smoothness tradeoff is visible.
- **Lean reference:** `LTFP/Ch01_Preliminaries/Concentration.lean`
  (`lipschitz_riemann_sum_error`).

## Chapter 2 — Supervised Learning

### §2.5 — Proposition 2.2 (No Free Lunch): class of algorithms `A` left implicit

- **Textbook:** "For any `n > 0` and any learning algorithm `A`,
  `sup_p { E[R_p(A(D_n))] − R*_p } ≥ 1/2`."
- **Observation:** The textbook statement does not say whether `A`
  ranges over deterministic learning rules or also includes randomized
  algorithms, nor what the expectation `E[·]` averages over (the
  sample `D_n(p)` alone, or also the algorithm's internal randomness).
  The Lean anchor proves the adversary bound for *deterministic*
  predictors `f : Bool → Bool`; lifting to "any algorithm" requires
  either restricting `A` to deterministic maps
  `(𝒳 × {0,1})^n → (𝒳 → {0,1})` or letting `E[·]` average over
  internal randomness as well.
- **Suggested clarification:** State the quantifier explicitly: "for
  any (possibly randomized) algorithm `A`, with `E[·]` taken over both
  the sample `D_n` and the internal randomness of `A`".
- **Lean reference:** `LTFP/Ch02_SupervisedLearning/Consistency.lean`
  (`nfl_two_distributions`).

### §2.5 — `sup = 1/2` is asymptotic in `k`, never attained at finite `k`

- **Textbook:** "the expected risk … evaluates to
  `(1/2)(1 − 1/k)^n`, which can be made arbitrarily close to `1/2`
  by letting `k → ∞`," concluding `sup_p {…} ≥ 1/2`.
- **Observation:** For every finite `k`, the constructed family gives a
  value strictly below `1/2`; the bound `1/2` is the *supremum over
  `k`*, never a maximum. The conclusion `sup ≥ 1/2` therefore requires
  `𝒳` to be infinite (so `k` is unbounded) and the passage to the
  supremum. The Lean core deliberately formalizes only the per-`k`
  nonnegativity, sidestepping the limit and highlighting the
  asymptotic nature of the bound.
- **Suggested clarification:** Add one sentence — e.g. "since `𝒳` is
  infinite, `k` can be taken arbitrarily large, so the supremum (not
  maximum) reaches `1/2`" — making explicit that the `1/2` bound is
  asymptotic in `k` and uses the infinite-`𝒳` hypothesis essentially.
- **Lean reference:** `LTFP/Ch02_SupervisedLearning/Consistency.lean`
  (`no_free_lunch`).

### §2.5 — `R*_p = 0` uses an unrestricted predictor class implicitly

- **Textbook:** "Build a uniform distribution on `ℕ × {0,1}`
  parametrized by `r ∈ {0,1}^k`: let `x` be uniform on the first `k`
  elements and `y = r_x`. Then `R*_p = 0`."
- **Observation:** The conclusion `R*_p = 0` requires the Bayes
  infimum to be taken over *all* measurable classifiers
  `𝒳 → {0,1}` — the labelling function `x ↦ r_x` on the finite set
  must itself be admissible. The Lean adversaries place a Dirac mass
  at a mislabelled point, which only works because the "ground-truth
  classifier" class is unrestricted; this is an implicit hypothesis
  the book leaves to the reader.
- **Suggested clarification:** State that `R*_p` is the infimum over
  all measurable `𝒳 → {0,1}` classifiers (not over some restricted
  hypothesis class `ℱ`), so that the Bayes risk on the adversarial
  distribution is indeed `0`.
- **Lean reference:** `LTFP/Ch02_SupervisedLearning/Consistency.lean`
  (`adversaryOne`).

## Chapter 3 — Linear Least Squares

### §3.7 — Class of estimators in the minimax `inf_A` is not specified

- **Textbook:** Writes
  `inf_A sup_{θ_* ∈ ℝᵈ} E[R_{θ_*}(A(Φ θ_* + ε))] − R* ≥ σ² d / n`
  without saying which class `A` ranges over.
- **Observation:** The result is much stronger under "all measurable
  estimators" than under "all linear estimators", but the textbook
  prose does not commit. The Bayesian-prior proof technique in the
  section only justifies the bound when `A` ranges over all measurable
  estimators, so this should be stated. The Lean docstring inherits
  the ambiguity.
- **Suggested clarification:** Insert "where the infimum is over all
  measurable estimators `A : ℝⁿ → ℝᵈ`" immediately after the
  displayed minimax inequality.
- **Lean reference:**
  `LTFP/Ch03_LinearLeastSquares/FixedDesign.lean`
  (`mourtada_lower_bound`, docstring).

### §3.7 vs §3.5 — Noise model asymmetry between matching upper and lower bounds

- **Textbook:** The §3.7 lower bound assumes `ε ∼ N(0, σ² I)`
  (Gaussian noise; the proof uses the Gaussian posterior-mean /
  posterior-mode identity). The matching §3.5 upper bound `σ² d / n`
  is proved under sub-Gaussian noise. The book presents the two
  bounds as a matched rate without flagging the noise-model
  asymmetry.
- **Observation:** Whether the lower bound extends to sub-Gaussian or
  only to bounded variance is left unsaid; the "matched rate" claim
  in the prose is therefore qualified in a way the formal statements
  do not reveal.
- **Suggested clarification:** Add a remark that the lower bound as
  proved is Gaussian-noise-specific; extension to sub-Gaussian or
  bounded-variance noise requires a separate argument, and the
  matched-rate phrasing should be qualified accordingly.
- **Lean reference:**
  `LTFP/Ch03_LinearLeastSquares/FixedDesign.lean`
  (file docstring and `mourtada_lower_bound`).

### §3.7 — Constant in the displayed bound is an `Σ̂`-invertible idealization

- **Textbook:** Displays the lower bound as `≥ σ² d / n` (constant 1).
- **Observation:** The proof shown delivers this constant only in the
  limit `λ → 0` and when `Σ̂` has full rank. For finite `λ` or a
  rank-deficient design, the actual constant is
  `(1/n) · tr((Σ̂ + λ I)⁻¹ Σ̂)`, which is strictly less than `d / n`.
  The Lean formalization implicitly acknowledges this by weakening
  the docstring to "`≥ c · σ² d / n` for some `c > 0`".
- **Suggested clarification:** Either restrict the displayed bound to
  "when `Σ̂` is invertible", or state it as
  `≥ σ² · tr((Σ̂ + λ I)⁻¹ Σ̂) / n` with the `→ σ² d / n` limit
  annotated separately.
- **Lean reference:**
  `LTFP/Ch03_LinearLeastSquares/FixedDesign.lean`
  (`mourtada_lower_bound`).

### §3.7 — Mourtada-2022 Bayes-prior route uses an unstated Gaussian-KL identity

- **Textbook:** §3.7 cites Mourtada (2022) for the OLS minimax lower
  bound via a Bayesian-prior argument with `θ* ∼ N(0, (σ²/(λn)) · I)`,
  the posterior identified with ridge regression, and the limit
  `λ → 0` recovering the `σ² d / n` rate for invertible `Σ̂`.
- **Observation:** The Mourtada-2022 derivation as cited implicitly
  uses the closed-form Kullback-Leibler divergence between two
  univariate Gaussians of equal variance,
  `KL(N(μ₀, v) ‖ N(μ₁, v)) = (μ₀ − μ₁)² / (2v)`. This identity is
  folklore but not stated in §3.7 nor in §15.1 — the formalization
  could not invoke a named Mathlib lemma for it at the time of
  writing, and LTFP's general-`d` carrier consequently routes through
  a looser Le-Cam two-point estimate. A reader trying to reconstruct
  the Mourtada-2022 proof will hit this gap.
- **Suggested clarification:** Either state the Gaussian-vs-Gaussian
  KL identity inline in §3.7 (one displayed equation), or add a
  footnote citing the standard reference, so the Mourtada-2022 route
  is self-contained within the textbook.
- **Lean reference:**
  `LTFP/Ch03_LinearLeastSquares/FixedDesign.lean`
  (`ols_minimax_two_point_discharge_multivariate_via_bhattacharyya`).

## Chapter 4 — Empirical Risk Minimization

_No entries yet._

## Chapter 5 — Optimization

_No entries yet._

## Chapter 6 — Local Averaging

_No entries yet._

## Chapter 7 — Kernels

_No entries yet._

## Chapter 8 — Sparse Methods

_No entries yet._

## Chapter 9 — Neural Networks

### §9.3 — Universal approximation: two proof routes share the section without distinction

- **Textbook:** §9.3 (with §9.3.1 + §9.3.4) develops universal
  approximation for single-hidden-layer ReLU networks via the
  constructive route: (a) exact CPA representation by ReLU using the
  partition-of-unity identity `(1/(2R))(x + R)₊ + (1/(2R))(−x + R)₊ = 1`
  on `[−R, R]`; (b) CPA dense in `C([−R, R])` (citing Rudin 1987);
  (c) lift to ℝ^d via Fourier inversion plus a Barron-norm bound. The
  chapter also notes in passing that "universal approximation results
  exist as soon as the activation function is not a polynomial
  (Leshno et al. 1993)" — which is a different, Stone-Weierstrass-style
  / Hahn-Banach argument, not the constructive CPA route.
- **Observation:** These are two distinct proof techniques for the
  same theorem name, with different smoothness/regularity requirements
  on the activation and different teaching trajectories. When
  formalizing, LTFP's `cybenko_uat_ramp_unconditional` uses the
  Stone-Weierstrass route (qualitative density), while a separate
  carrier following the constructive CPA-by-ReLU route would have a
  different signature (quantitative + Barron norm). A reader citing
  "§9.3 universal approximation" cannot tell which proof technique is
  being invoked.
- **Suggested clarification:** Distinguish the two routes explicitly
  in §9.3 (e.g., "Theorem 9.X — universal approximation via
  Stone-Weierstrass / non-polynomial activation" vs "Theorem 9.Y —
  constructive CPA-by-ReLU + Rudin density"), and note the different
  smoothness hypotheses each requires.
- **Lean reference:** `LTFP/MathlibExt/Topology/UAT.lean`
  (`cybenko_uat_ramp_unconditional`).

## Chapter 10 — Ensemble Methods

_No entries yet._

## Chapter 11 — Online Learning and Bandits

_No entries yet._

## Chapter 12 — Overparameterized Models

### §12.4 — NTK lazy-training regime: informal exposition, no in-book formal proof

- **Textbook:** §12 (with NTK material in §12.4) describes the
  lazy-training regime — under which a wide neural network's gradient
  flow is well-approximated by its linearization around initialization
  — informally. The chapter cites Jacot et al. (2018) and Du et al.
  (2019) for the underlying formal results.
- **Observation:** Formalizing the "lazy training carrier" (the
  statement that for sufficiently wide networks, the linearization
  approximation holds uniformly over the optimization trajectory)
  required bespoke clopen-bootstrap-on-trajectory infrastructure and
  perturbation control of the empirical NTK well beyond Bach's
  exposition. This is appropriate textbook style, but readers
  attempting to verify the §12.4 claims rigorously will need to
  follow the references rather than the chapter itself, and the
  chapter does not flag the size of the verification gap.
- **Suggested clarification:** Add a "for formal proofs see..." block
  at the end of §12.4 explicitly pointing readers to Jacot et al.
  (2018) Theorem 1, Du et al. (2019) Theorem 4.1, and noting that
  the in-chapter exposition is intentionally informal.
- **Lean reference:**
  `LTFP/MathlibExt/Probability/NTKLazyCarrierFromTotalMovement.lean`
  (`ntk_lazy_training_carrier_end_to_end`).

## Chapter 13 — Structured Prediction

_No entries yet._

## Chapter 14 — Probabilistic Methods

### §14.4.2 — McAllester PAC-Bayes bound: post-Chernoff inequality is unnumbered

- **Textbook:** §14.4.2 proves the McAllester-style PAC-Bayes bound in
  three displayed equations: the per-θ Hoeffding MGF, the
  Donsker-Varadhan-after-Chernoff joint-event MGF bound (numbered
  Eq. 14.5), and the in-expectation Gibbs form (numbered Eq. 14.6).
  The user-facing form — "with probability ≥ 1 − δ, for all
  `ρ ∈ P(θ)`,
  `∫ R dρ ≤ ∫ R̂ dρ + (1/s) D(ρ‖q) + (1/s) log(1/δ) + s ℓ∞² / (8n)`"
  — appears in prose on p. 424, between Eq. 14.5 and Eq. 14.6, with no
  equation number assigned.
- **Observation:** External sources occasionally cite a non-existent
  "Eq. 14.21" for this McAllester bound; verification against the
  canonical PDF confirms Chapter 14 ends at Eq. (14.6) and that the
  highest equation number in §14.4.2 is (14.6). The unnumbered
  post-Chernoff inequality is the most-cited statement of the section,
  yet has no stable label. This created downstream confusion in the
  formalization workflow.
- **Suggested clarification:** Assign an explicit equation number to
  the post-Chernoff PAC-Bayes inequality in §14.4.2 (the in-prose
  line just before "We thus get a bound on the average generalization
  error..."), so it can be cited unambiguously alongside Eq. 14.5 and
  Eq. 14.6.
- **Lean reference:** `LTFP/Ch14_Probabilistic/PACBayes.lean`
  (`pac_bayes_mcallester`, `pac_bayes_bach_eq_14_5_scalar`).

## Chapter 15 — Lower Bounds

### §15.1 — Pinsker and Bretagnolle-Huber inequalities used but never named

- **Textbook:** §15.1 proves Fano's inequality directly via KL
  convexity (Proposition 15.1 / Corollary 15.1) and uses the scalar
  step `1 + α ≤ exp(α)` silently within the derivation. The
  classically-named inequalities "Pinsker"
  (`tvDist(μ, ν)² ≤ (1/2) KL(μ ‖ ν)`) and "Bretagnolle-Huber"
  (`tvDist(μ, ν) ≤ √(1 − exp(−KL(μ ‖ ν)))`) are used in spirit but
  never introduced by name in Chapter 15. The reference for these
  named results is given as Tsybakov (2008).
- **Observation:** Readers searching the textbook index for "Pinsker"
  or "Bretagnolle-Huber" will not find these inequalities in
  Chapter 15. LTFP's concept registry imports the names from
  Tsybakov 2008 because they are standard, and the formalization
  exposes both inequalities as named theorems
  (`tvDist_le_sqrt_klDiv`, `tvDist_le_sqrt_one_sub_exp_neg_klDiv`).
  The naming asymmetry between book and standard practice is a
  recurring source of confusion when teaching from the chapter.
- **Suggested clarification:** Add explicit naming in §15.1 (e.g.,
  "Lemma X — Pinsker's inequality (after Tsybakov 2008, §2.4)" and
  "Lemma Y — Bretagnolle-Huber inequality") and index entries, so
  the named results are discoverable from Chapter 15 directly without
  routing through Tsybakov.
- **Lean reference:** `LTFP/Ch15_LowerBounds/Statistical.lean`
  (`tvDist_le_sqrt_klDiv`, `tvDist_le_sqrt_one_sub_exp_neg_klDiv`).

---

## Out of scope

The following are **not** errata against the textbook and should not be
filed here:

- Places where Mathlib lacks the infrastructure needed for the
  measure-theoretic formulation (e.g., matrix Lieb concavity,
  continuous-time gradient flow). These are tracked separately in the
  library as anchored algebraic cores; the textbook statement is
  correct, the formalization gap is in Mathlib.
- Stylistic preferences in proof presentation.
- Differences between the textbook's notation and Lean's conventional
  Mathlib notation.

## Contributing

Found a discrepancy while reading the Lean files or the textbook? Open
a pull request adding an entry under the appropriate chapter. Follow
the entry format above. One entry per pull request keeps the review
trivial.

Periodic batches of accepted entries are forwarded to the textbook
author for consideration in future editions.
