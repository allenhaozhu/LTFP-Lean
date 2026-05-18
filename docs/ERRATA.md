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

_No entries yet._

## Chapter 10 — Ensemble Methods

_No entries yet._

## Chapter 11 — Online Learning and Bandits

_No entries yet._

## Chapter 12 — Overparameterized Models

_No entries yet._

## Chapter 13 — Structured Prediction

_No entries yet._

## Chapter 14 — Probabilistic Methods

_No entries yet._

## Chapter 15 — Lower Bounds

_No entries yet._

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
