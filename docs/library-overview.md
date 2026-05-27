# Library overview — concepts, communities, and surprises

This page is a one-shot snapshot of LTlib's knowledge graph, produced by
running a static + semantic extractor over the repository (815 concept
nodes, 1073 edges, 86 communities detected). It complements the
per-concept wiki by surfacing structure that wiki pages don't make
explicit: which abstractions are the most-connected hubs ("god nodes"),
which pairs of concepts are semantically close across chapter boundaries
("cross-cutting connections"), and how the library naturally clusters
into communities of related ideas.

Use this page as a map. If you're trying to understand how a single
result fits into the larger fabric of Bach (2024), find its community
below and follow the links from there.

**Prefer an interactive view?** See the [interactive graph](graphify/) for a navigable D3 visualization of the same data.

## Core abstractions (most-connected nodes)

The ten nodes with the highest edge count — these are the load-bearing
abstractions that the rest of the library leans on.

1. `main()` — 23 edges (tooling entrypoint)
2. `Registry` — 11 edges (concept registry, single source of truth)
3. `parse_lean_target()` — 11 edges
4. `Bach (2024) Learning Theory from First Principles` — 11 edges
5. `Bach (2024) Learning Theory from First Principles` — 10 edges (second referent)
6. `Phi Hinge` — 10 edges
7. `chapter_label()` — 9 edges
8. `Errata for Bach (2024) LTFP` — 9 edges
9. `Population risk R(f) = E[ℓ(f(x), y)]` — 9 edges
10. `Exponential surrogate Φ(u) = exp(-u) — yields AdaBoost` — 9 edges

Two observations worth noting: (a) the `Phi Hinge` and exponential
surrogate land in the top 10, reflecting how much of the convex-
surrogate machinery in chapter 4 reuses the same abstraction. (b) the
errata itself is a hub — a sign that several concepts in the library
exist specifically to repair textbook gaps.

## Cross-cutting connections

Pairs of concepts that the semantic extractor flagged as closely
related, even though they live in different chapters or files. These
are the connections most likely to surprise you when reading linearly
through the book.

- `Pow Nonneg Anchor` ↔ `populationRisk of nonneg loss is nonneg`
  (`docs/wiki/concepts/pow-nonneg-anchor.md` → `docs/wiki/concepts/pop-risk-nonneg.md`)
- `Mu-Strongly Convex` ↔ `McDiarmid Inequality`
  (`docs/wiki/concepts/mu-strongly-convex.md` → `docs/wiki/concepts/mcdiarmid-inequality.md`)

These are flagged AMBIGUOUS by the extractor — the semantic relation is
real but the *kind* of relation isn't fully resolved. Reading the two
pages side-by-side is the fastest way to see why the extractor grouped
them.

## Hyperedges (group relationships)

A small number of higher-order relationships — a group of concepts that
participate jointly in a theorem chain or a coherent build-up.

- **Matrix Bernstein via Lieb concavity end-to-end chain** — links the
  Tier-C Matrix Bernstein anchor to Tropp (2012), Lieb (1973), the
  decomposition wiki page, and the Tier-C ledger.
- **Mathlib PR portfolio pipeline (drafts → open PRs)** — links draft
  pages for the Total Variation, sub-exponential, L1 subgradient,
  adversary, and Pinsker contributions. The live open-PR list is at
  [github.com/leanprover-community/mathlib4/pulls?q=author%3Aallenhaozhu](https://github.com/leanprover-community/mathlib4/pulls?q=author%3Aallenhaozhu).
- **F10 foundational absolute-value Mathlib alias cluster** — the
  family of `abs_*` thin aliases that downstream chapters cite.
- **Ch10 bagging-predictor anchor cluster (Bach §10.1.2)** — the
  bagging-predictor concept and its book-excerpt anchors.
- **Ch15 Le Cam averaging anchors** — the Le Cam minimax machinery
  used in chapter 15.

## Communities

The extractor partitions the 815 nodes into 86 communities. Below are
the labeled ones, in roughly decreasing node count.

### Project Operations & ERRATA (52 nodes)
The errata feed and project ledger: textbook-first proof strategy,
formalization order, coverage status, and the section-by-section errata
entries flagging issues in Bach (2024) §1.2.3, integrability of
`exp(s·Z)`, the matrix-Bernstein hypothesis strength, the `C_i` symmetry
convention, and the two `σ²` conventions.

### Bandit & Risk Foundations (42 nodes)
The chapter-1 risk decomposition (approximation, estimation, excess),
the Bach (2024) anchor itself, and the chapter-15 bandit foundation:
cumulative regret, suboptimality gap, regret with constant action,
regret rewriting in scaled `μ_*`.

### Wiki build pipeline (37 nodes)
The Python tooling that emits the wiki: `build_cid_to_audits()`,
`chapter_label()`, `ensure_clean_dirs()`, `infer_status()`,
`infer_tier()`, `infer_topic_tags()`, `load_book_excerpt()`,
`load_concepts()`, etc.

### Lean–Textbook audit tool (32 nodes)
The library that compares each `.lean` file against Bach's text:
`AuditFinding`, `_block_at()`, `classify()`, `Concept`,
`_count_bach_hypotheses()`, `_count_binders()`, `excerpt_is_anchor()`,
`excerpt_path_for()`, …

### DAG & Concept registry tooling (29 nodes)
`BaseModel`, `build_graph()`, `emit_json()`, `emit_mermaid()`,
`load_registry()`, `main()`, plus the partition-into-antichains
algorithm that produces the wave-by-wave formalization order.

### Wiki index & Triangle/Abs lemmas (25 nodes)
The wiki index pages plus the small triangle / absolute-value
foundational lemmas used everywhere downstream:
`|X| ≤ B → |E[X]| ≤ B`, `|E[X]| ≤ E[|X|]`, `|-x| = |x|` (alias
`abs_neg`), `|x| ≥ 0` (alias `abs_nonneg`), `|a+b| ≤ |a|+|b|`,
`|0| = 0` (alias `abs_zero`).

### Bernstein & Gaussian NLL (24 nodes)
The Bernstein family (♦) and the Gaussian negative-log-likelihood
family: `Gaussian NLL Eq Squared Dispersion`, `Gaussian NLL family`,
`Gaussian NLL Le Iff Square`, `Gaussian NLL Self`,
`Gaussian NLL Sub Zero Nonneg`, `Gaussian NLL Symmetric`, …

### Surrogate Φ (exp / hinge) (22 nodes)
The two main classification surrogates: exponential surrogate
`Φ(u) = exp(-u)` (yielding AdaBoost) and the hinge surrogate. Includes
the antitone properties, anchor points at zero, and the `1 - u` form of
the hinge.

### Empirical risk family (22 nodes)
`Empirical Risk`, `Empirical Risk Minimization`, `Estimation Error`,
`Excess Risk`, `Expectation Operator`, plus the per-concept book
excerpts and tickets.

### PAC-Bayes / KL / Minimax (22 nodes)
`Absolute Continuity (measure theory)`, `KL Divergence`,
`McAllester PAC-Bayes Bound`, `Minimax Lower Bound`,
`Ordinary Least Squares (OLS)`, `Online Convex Optimization`,
`PAC-Bayes Theory`, `Partition Weights`, …

### Loss functions & margins (20 nodes)
`Loss Function`, `Margin Monotonicity`, `Margin Satisfied`,
`Mu-Strongly Convex`, `Multicat Loss Diagonal`, `Multicat Loss in Unit`,
plus the per-concept book excerpts and tickets.

### Ridge & Representer theorem (20 nodes)
`Representer Theorem`, `Ridge Bias-Variance Tradeoff`,
`Ridge Closed-Form Solution`, `Ridge Scalar Multiplication of y`, plus
the book-excerpt anchors.

### Single ReLU & square loss (20 nodes)
`Single Hidden ReLU`, `Single Hidden ReLU Add A`, `Square Nonneg Alias`,
`Sqrt Sq Eq Abs`, `Square Loss`, `Square Loss Convex`,
`Square Loss Eq Sq Diff`, `Square Loss Nonneg`, …

### L1 / L0 norm lemmas (19 nodes)
`l0-norm`, `L1 Norm`, `l1-norm-eq-zero-of-zero`, `l1-norm-fin-one`,
`l1-norm-neg`, `L1 Norm Nonnegativity`, `L1 Norm Triangle Inequality`,
`L1 Triangle Inequality`, …

### Neural net foundation & NTK (10 nodes)
Foundational neural-network book excerpts: `nn-weights`,
`nn-weights-localavg`, `nn-zero-a`, `nn-zero-bias-one-neuron`,
`nn-zero-input`, plus the NTK concentration scalar-Hoeffding ticket and
`ntk-symmetry-anchor`.

### OLS & fixed design (12 nodes)
`ols-add-y`, `ols-closed-form`, `ols-fixed-design-bias-variance`,
`ols-geometric`, plus the per-concept book excerpts and tickets.

### Kernel expansion / KRR (15 nodes)
`is-l-smooth-zero`, `kernel-expansion`, `kernel-expansion-add`,
`kernel-expansion-at-train-input`, `kernel-expansion-eq`,
`kernel-expansion-smul`, `kernel-foundation`, `krr-coeffs`, …

### Bayes predictor & risk lemmas (10 nodes)
`bayes-predictor`, `bayes-risk-le-population-risk`,
`bayes-risk-minimum`, `bayes-risk-nonneg`, plus the Bernstein-inequality
book excerpt.

### Consistency & Phi-risk (14 nodes)
`Consistency`, `Double Descent Non-negative`,
`Empirical Phi-Risk Zero Sample`, `Empirical Risk Monotone Pointwise`,
`Empirical Risk Non-negative`, `Empirical Risk Zero Loss`,
`Empirical Phi-Risk`, `Empirical Phi-Risk Non-negative`, …

### Expectation algebra (13 nodes)
`Expectation Additivity`, `Expectation of Constant`,
`Expectation Greater than Constant`, `Expectation in Interval`,
`Expectation Less than Constant`, `Expectation Monotonicity`,
`Expectation of Negation`, `Expectation Nonnegativity`, …

### Boosting (AdaBoost path) (6 nodes)
`boost-eq`, `boost-one-step`, `boost-zero-coeffs`, `boost-zero-h`,
`boosted-add-coeff`, `boosted-predictor`.

### Gram matrix & implicit bias (12 nodes)
`Gram Matrix`, `Gram Matrix Diagonal`, `Gram Matrix Equals Kernel`,
`Gram matrix family`, `Gram Matrix Symmetry`, `Gram Matrix Zero`,
`Implicit Bias Add Y`, `Implicit bias family`, …

### Gradient descent iterates (11 nodes)
`Gradient Descent Descent Lemma`, `GD Iterate`,
`GD Iterate Fixed Critical`, `GD Iterate Successor`,
`GD Iterate Zero Step`, `GD Step Eq`, `GD Step Zero Step`,
`Gradient Descent family`, …

### ReLU pointwise identities (9 nodes)
`ReLU Add Le`, `ReLU Eq ReLU`, `ReLU Eq Self of Nonneg`,
`ReLU Equals Zero Iff`, `ReLU Bounded by Identity on Nonneg`,
`ReLU Monotonicity`, `ReLU of Negative Equals Zero`,
`ReLU of Nonneg Argument`, …

### Bandit foundation (9 nodes)
`Multi-armed Bandit Theory`, `bandit-foundation`, `bandit-gap`,
`bandit-regret-const-action`, `bandit-regret-eq-rewrite`,
`bandit-regret-eq-sum-gaps-strong`, `bandit-regret-smul`,
`bandit-regret-sum-gaps`, …

### UCB & variance basics (9 nodes)
`Non-negativity Property`, `UCB Algorithm`, `Variance`, `Zero Loss`,
`UCB Bonus Task`, `UCB Bonus Non-negativity Task`,
`Variance Non-negativity (Real) Task`, `Zero Loss Task`, …

### Local averaging (8 nodes)
`Local Averaging`, `Local Average Bias Term`, `Local Average Add Y`,
`Local Average Bias Zero f-star`, `Local Average Negation Y`,
`Local Average Scalar Multiply Y`, plus book excerpts and tickets.

### Quadratic forms & positive-definiteness (8 nodes)
`Positive Definite Is Unit`, `Pow Nonneg Anchor`, `Quadratic Form Min`,
`Quadrature Expectation`, plus book excerpts and tickets.

### Wiki indexes & variance (8 nodes)
`Variance Non-Negative (Real)`, `Wiki Index by Chapter`,
`Wiki Index by Mathlib Dependency`, `Wiki Index by Status`,
`Wiki Index by Tier`, `Wiki Index by Topic`, `Zero Loss`,
`Zero Loss Non-Negative`.

### Is-k-sparse predicate family (8 nodes)
`is-k-sparse` (k-sparsity predicate family), `is-argmax`,
`is-k-sparse-dim`, `is-k-sparse-mono`, `is-k-sparse-succ`,
`is-k-sparse-zero-any`, `is-k-sparse-zero`.

### Kernel expansion family (8 nodes)
`kernel-expansion` (family), `Kernel foundation`,
`kernel-expansion-add`, `kernel-expansion-at-train-input`,
`kernel-expansion-eq`, `kernel-expansion-smul`, `kernel-expansion`,
`kernel-foundation`.

### Explore-then-commit & gap algebra (7 nodes)
`Explore Then Commit`, `Gap Antitone Mu`, `Gap Definition`,
`Gap Eq Diff`, `Gap Monotone Mu Star`, `Gap Nonnegative`,
`Gap Optimal`.

### Is-argmax / is-k-sparse predicates (7 nodes)
`Is Argmax`, `Is K-Sparse`, `Is K-Sparse Dimension`,
`Is K-Sparse Monotone`, `Is K-Sparse Successor`, `Is K-Sparse Zero`,
`Is K-Sparse Zero Any`.

### Information theory foundation (7 nodes)
`Information theory foundation`, `KL divergence (information theory)`,
`infotheory-foundation`, `kl-eq-top-iff`, `kl-ne-top-iff`,
`kl-of-not-ac`, `kl-zero-right`.

### OLS algebra family (6 nodes)
`OLS Add Y`, `OLS Closed Form`, `OLS Fixed Design Bias-Variance`,
`OLS Geometric`, `OLS Minimax Lower Bound`, `OLS Scalar Multiply Y`.

### Sketching linearity (6 nodes)
`Sketch Add Mat`, `Sketch Add Matrix`, `Sketch Linearity`, `Sketch One`,
`Sketch SMul Matrix`, `Sketch Zero Matrix`.

### Absolute-value expectation lemmas (6 nodes)
`Abs Expectation Bounded`, `Abs Expectation Le Exp Abs`,
`Abs Neg Anchor`, `Abs Nonneg Anchor`, `Abs Triangle`, plus the phase-2
handoff anchor.

### Bernoulli NLL anchors (3 nodes)
`bernoulli-at-half`, `bernoulli-nll-correct-zero`, `bernoulli-nll`.

### Double descent & empirical-risk tasks (6 nodes)
`Double Descent Nonnegative Task`, `Empirical Phi-Risk Zero Sample
Task`, `Empirical Risk Monotone Pointwise Task`, `Empirical Risk
Nonnegative Task`, `Empirical Phi-Risk Task`, `Empirical Phi-Risk
Nonnegative Task`.

### Exponential function properties (6 nodes)
`Exponential Function Properties`, `exp-neg-eq-inv`, `exp-pos-alias`,
`exp-strict-mono`, `exp-sub-1-sub-self`, `exp-zero-eq-one`.

### Exponential-function aliases (5 nodes)
`exp(-x) = 1/exp(x)`, `Exponential Positivity Alias`,
`Exponential Strict Monotonicity`, `exp(x) - 1 Self-Subtraction`,
`exp(0) = 1`.

### JMLR MLOSS submission scaffolding (5 nodes)
`JMLR MLOSS Cover Letter`, `JMLR MLOSS Notes`, `JMLR MLOSS README`,
`JMLR2e Template README`, `JMLR2e Sample PDF`.

### Bagging predictor (5 nodes)
`Bagging Predictor`, `bagging-const`, `bagging-index-anchor`,
`bagging-predictor`, `bagging-predictor-zero`.

### Averaging inequalities (5 nodes)
`Averaging Inequalities`, `average-le-sup-anchor`, `average-of-self`,
`average-plus-half-le`, `average-three-self`.

### Cauchy-Schwarz & convex foundation (5 nodes)
`Cauchy-Schwarz Anchor Task`, `Convex Foundation Task`,
`Differential Calc Basics Book Excerpt`,
`Differential Calc Basics Book Excerpt`, `Differential Calc Basics
Ticket`.

### L-smoothness predicate family (5 nodes)
`is-l-smooth`, `implicit-bias-zero-labels`, `is-l-smooth-const-any`,
`is-l-smooth-mono`, `is-l-smooth-zero`.

### No Free Lunch theorem (4 nodes)
`no-free-lunch`, `no-free-lunch` book excerpt, `no-free-lunch` ticket,
`No Free Lunch Theorem`.

### Cumulative loss (4 nodes)
`Cumulative Loss`, `Cumulative Loss (Constant)`,
`Cumulative Loss Zero (Finite Sample)`, `Cumulative Loss Zero
(Horizon)`.

### KL-divergence anchors (4 nodes)
`kl-eq-top-iff`, `kl-ne-top-iff`, `kl-of-not-ac`, `kl-zero-right`.

### PAC-Bayes (KL form) (4 nodes)
`PAC-Bayes KL`, `PAC-Bayes KL Not Absolutely Continuous`,
`PAC-Bayes McAllester`, `PAC-Bayes Zero Prior`.

### Penalized empirical risk (4 nodes)
`Partition Weights`, `Penalized Add Pen`, `Penalized Empirical Risk`,
`Penalized Zero Pen`.

### Supremum & three-point inequalities (4 nodes)
`Sup Singleton`, `Sup Zero Left`, `Three Point Average Le Max`,
`Two Point Sup Lb`.

### Testing-error bounds (4 nodes)
`Testing Error Diff Bound`, `Testing Error Le One`,
`Testing Error Nonneg`, `Two Testing Errors Le Two`.

### Approximation error (4 nodes)
`Approximation Error`, `approx-error-indep-fhat`, `approximation-error`,
`bayes-predictor` book excerpt.

### Block matrix inversion (3 nodes)
`block-matrix-inversion` (book excerpt + ticket).

### Cumulative loss tasks (4 nodes)
`Cumulative Loss Task`, `Cumulative Loss Constant Task`,
`Cumulative Loss Zero FS Task`, `Cumulative Loss Zero Horizon Task`.

### Multivariate Gaussian & RKHS (4 nodes)
`Multivariate Gaussian Measure`, `RKHS / Aronszajn Theorem`, plus phase-2
book excerpts for both.

### Penalized empirical risk minimization (4 nodes)
`Penalized Empirical Risk Minimization`, plus `Penalized Add Pen`,
`Penalized Empirical Risk`, `Penalized Zero Pen` book excerpts.

### Rademacher complexity & uniform convergence (4 nodes)
`Rademacher Complexity`, `Uniform Convergence`,
`Uniform Deviation Rademacher Task`, `Uniform Local Weights Task`.

### Single-node singletons
A handful of communities are size-1 nodes that didn't cluster with
anything else — typically tooling entrypoints or one-off ticket entries:
`Emit doc/order.md — human-readable wave-by-wave formalization order.`,
`Emit one tasks/<id>/ticket.md per pending concept.`,
`add-risks-nonneg book excerpt`.

### Log-exp aliases (3 nodes)
`Log-Exp Alias`, `Log Nonneg of One Le`, `Log One Alias`.

### PAC-Bayes KL definitional triple (3 nodes)
`PAC-Bayes KL Definition`, `PAC-Bayes KL Equals Top Iff`,
`PAC-Bayes KL Not Equal Top Iff`.

### Soft thresholding (3 nodes)
`Soft Threshold`, `Soft Threshold at Lambda`, `Soft Threshold Zero
Zero`.

### Subgradient (3 nodes)
`Subgradient`, `Subgradient Add Const`, `Two Le Exp 1 Plus 1`.

### Talk / presentation materials (3 nodes)
`Talk Main PDF`, `Talk Main TOC`, `Talk README`.

### Consistency artefact bundle (3 nodes)
`Consistency book excerpt`, `Consistency Ticket`, plus the consistency
anchor itself.

### Exponential inequalities (3 nodes)
`Exponential Inequalities`, `One Le Exp Nonneg` book excerpt,
`One Plus Le Exp` book excerpt.

### SVD artefact bundle (3 nodes)
`SVD Book Excerpt`, `SVD Ticket`, plus the SVD anchor itself.

### Thin pairs (2-node communities)
Smaller groupings that the extractor flagged as cohesive but weakly
connected to the rest of the library — read these as "two ideas the
extractor saw as closely related, but with not enough surrounding
context to fully cluster". Examples:

- `Cauchy-Schwarz Anchor` ↔ `Dudley Entropy Bound`
- `Convex Foundation` ↔ `Differential Calculus Basics`
- `Le Cam Average` ↔ `Lieb Concavity Joint`
- `No Free Lunch Theorem` ↔ `Online Convex Foundation`
- `1 ≤ exp(nonneg)` ↔ `1 + x ≤ exp(x)`
- `UCB Bonus` ↔ `UCB Bonus Nonneg`
- `SVD` ↔ `Universal Approximation`
- `Bounded Difference Rademacher Task` ↔ `Dudley Entropy Bound Task`
- `Empirical Risk Zero Loss Task` ↔ `Empirical Risk Zero Sample Task`
- `Gaussian Bayes Risk Ridge Trace` ↔ `Gaussian Conjugate Posterior Mean`
- `Operator Monotone Functions` ↔ `Operator Monotone Fn (ticket)`
- `Subdifferential Sum Rule` ↔ phase-2 book excerpt
- `Universal Approximation Theorem` ↔ `Universal Approximation Task`

## How to use this map

- Looking for the **canonical hub** of a topic? Start in the
  Communities section, find the matching cluster, and follow the wiki
  links from there.
- Want to see **what surprises the linear chapter order hides**?
  Read the Cross-cutting connections section.
- Curious **how much of the library is repair-work vs original
  formalization**? The "Project Operations & ERRATA" community is
  exactly that scope.
- Trying to **find the load-bearing abstractions** to teach from? The
  Core abstractions list is your shortlist.

This is a snapshot, not a live index. The per-concept wiki at
`wiki/` is always the source of truth for current status, audit state,
and proof-tier classification.
