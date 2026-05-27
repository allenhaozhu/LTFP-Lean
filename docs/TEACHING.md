# Teaching with LTlib

LTlib is a Lean 4 formalization of Francis Bach (2024), *Learning
Theory from First Principles* (MIT Press), suitable as a companion
artifact for graduate-level ML theory courses, problem sets that grade
mechanically via `lake build`, and reading groups that step through
proofs in the VS Code Lean infoview.

This document describes how to use LTlib for teaching: as a student,
as a teacher, and as a course organizer.

## Table of contents

1. [Overview](#overview)
2. [For students: how to read along](#for-students-how-to-read-along)
3. [For teachers: course integration patterns](#for-teachers-course-integration-patterns)
4. [The mini-wiki: per-concept navigation](#the-mini-wiki-per-concept-navigation)
5. [The textbook-strict branch: proofs that mirror Bach](#the-textbook-strict-branch-proofs-that-mirror-bach)
6. [Problem sets: starter pack](#problem-sets-starter-pack)
7. [Errata: when Bach is slightly wrong](#errata-when-bach-is-slightly-wrong)
8. [Contributing tutorials and problems back](#contributing-tutorials-and-problems-back)

## Overview

LTlib aims for a complete chapter-by-chapter formalization of Bach
(2024): the supervised-learning preliminaries (Ch. 1-2), linear least
squares and ridge (Ch. 3), ERM and convergence rates (Ch. 4),
optimization (Ch. 5), local averaging (Ch. 6), kernels (Ch. 7),
sparsity (Ch. 8), neural networks (Ch. 9), ensembles (Ch. 10), online
learning and bandits (Ch. 11), overparameterized regimes (Ch. 12),
structured prediction (Ch. 13), probabilistic methods including
PAC-Bayes (Ch. 14), and statistical lower bounds (Ch. 15). A sibling
`LTFP/MathlibExt/` collection provides Mathlib-style extension modules
(total-variation distance, Le Cam's two-point method, Bhattacharyya
coefficient, sub-exponential class, ramp-function UAT building blocks,
RKHS scaffolding, L-smoothness API, etc.) for the prerequisites that
Mathlib does not yet ship.

Two branches serve different audiences:

* `main` --- research release. Optimized for Mathlib compatibility and
  for the open Mathlib pull requests
  ([#39164](https://github.com/leanprover-community/mathlib4/pull/39164),
  [#39165](https://github.com/leanprover-community/mathlib4/pull/39165),
  [#39166](https://github.com/leanprover-community/mathlib4/pull/39166),
  [#39167](https://github.com/leanprover-community/mathlib4/pull/39167),
  [#39168](https://github.com/leanprover-community/mathlib4/pull/39168))
  upstreaming the MathlibExt content.
* `textbook-strict` --- pedagogical companion (the branch this document
  ships on). Proofs are written to mirror Bach's textbook exposition
  step-by-step, with named carrier theorems matching Bach's lemma
  numbering. Worked walkthroughs and student problem sets live here.

For teaching, `textbook-strict` is the recommended starting point.

## For students: how to read along

### Reading along: VS Code + Lean infoview

The lowest-friction setup:

1. Install [VS Code](https://code.visualstudio.com/) and the
   [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4).
2. Clone the repository:
   ```
   git clone https://github.com/allenhaozhu/LTFP-Lean.git
   cd LTFP-Lean
   git checkout textbook-strict
   lake exe cache get      # 5-10 min, fetches Mathlib oleans
   ```
3. Open the folder in VS Code. Open a file under
   `LTFP/Examples/` (e.g., `Bernstein.lean`). Wait for Lean to elaborate
   the file (first time: ~30 s; warm cache: a few seconds).
4. Place the cursor on any `exact`, `apply`, `intro`, or theorem name.
   The Lean infoview pane shows the current goal --- every implicit
   hypothesis becomes visible.

If `lake exe cache get` is slow or fails, `lake build` from a cold
state takes roughly 1-2 hours on a typical laptop; the cache is a
practical necessity.

### Three worked examples (start here)

| File | Bach section | What it shows |
|---|---|---|
| [`LTFP/Examples/Bernstein.lean`](../LTFP/Examples/Bernstein.lean) | §1.2.3 | Bernstein tail via Bach's Taylor-expansion MGF |
| [`LTFP/Examples/PinskerBH.lean`](../LTFP/Examples/PinskerBH.lean) | §15.1 | Pinsker / Bretagnolle-Huber inequality for KL |
| [`LTFP/Examples/PACBayesMcAllester.lean`](../LTFP/Examples/PACBayesMcAllester.lean) | §14.4.2 | McAllester PAC-Bayes via Hoeffding + DV + Chernoff |

Each file is sized for one ~1-hour reading session with a graduate
audience: a textbook-strict carrier theorem at the top, then a series
of `example` blocks that instantiate the carrier at a concrete shape
and discharge it in one line, with rich inline commentary tying every
step back to Bach's textbook proof.

### Self-paced reading order

Suggested order, easiest first:

1. **Bernstein** (`LTFP/Examples/Bernstein.lean`). One-page Bach proof
   (pp. 14-15), three concrete `example` blocks. Good first exposure to
   the textbook-strict naming convention `bach_<lemma>_<descriptor>`.
2. **Pinsker / Bretagnolle-Huber** (`LTFP/Examples/PinskerBH.lean`).
   Probabilistic foundations: total-variation distance, KL divergence,
   the Bhattacharyya coefficient, two routes (direct + Hellinger) to
   the same conclusion.
3. **PAC-Bayes McAllester** (`LTFP/Examples/PACBayesMcAllester.lean`).
   The deepest of the three: four conceptual steps (per-θ Hoeffding,
   integration over prior, Donsker-Varadhan, Chernoff optimization)
   composed into an A-class carrier.

For each example, the narrative walkthroughs under
[`docs/teaching/`](teaching/) re-tell the proof in prose with code
snippets --- useful as a pre-reading or for students who prefer paper to
infoview.

## For teachers: course integration patterns

LTlib supports three classroom patterns. Pick the one that matches your
course constraints and student background.

**Pattern 1: Reading group.** Use the wiki + Examples as weekly-reading
material. A graduate student with prior exposure to ML theory but not
to Lean can read one `Examples/*.lean` file plus its walkthrough in
~1-2 hours. Three sessions cover the three flagship examples; further
sessions can pick chapter files (e.g.,
`LTFP/Ch05_Optimization/GD.lean`) and discuss the proof structure
without expecting students to write Lean themselves.

**Pattern 2: Mechanically graded problem sets.** Assign one or more
files from
[`tasks/student-problems/`](../tasks/student-problems/). Students
replace `sorry` with a proof; grading is `lake build LTFP.<module>`
exit 0 plus a visual inspection (looking for `sorry`/`admit`/`#exit`
escape hatches and confirming that `#print axioms` lists only the
expected axioms). Solution branches stay separate from the public repo;
faculty can fork and maintain a private grading branch. See [Problem
sets](#problem-sets-starter-pack) below for the starter pack.

**Pattern 3: Textbook companion.** Each chapter file's docstrings link
back to Bach by section. Students who encounter a hand-wavy textbook
step ("clearly, σ² is preserved under iid summation"; "by Jensen's
inequality the integral is at most...") can open the LTlib version and
see every implicit hypothesis surfaced. This is particularly useful for
Chapters 14-15, where Bach's exposition deliberately compresses the
information-theoretic technicalities.

### Workload expectations

Rough estimates for a student new to Lean 4 but comfortable with
graduate-level probability and analysis:

* **Reading a worked example** (e.g., `LTFP/Examples/Bernstein.lean`):
  60-90 minutes, including time to step through the infoview.
* **Solving an Easy problem** (e.g., `ch01-bernstein-warmup.lean`):
  2-3 hours total, mostly fighting unfamiliar Lean syntax. Subsequent
  problems get faster.
* **Solving a Medium-Hard problem** (e.g., `ch14-pac-bayes-step1.lean`):
  3-5 hours. The mathematics is settled; the work is finding the right
  Mathlib lemma names.

Course-internal estimates may vary substantially based on prior Lean
exposure. A student who has worked through the
[Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
tutorial will move ~2x faster than one starting cold.

## The mini-wiki: per-concept navigation

A 339-concept mini-wiki at [`docs/wiki/`](wiki/) indexes every formalized
result back to its Bach section. Each concept gets its own page under
[`docs/wiki/concepts/`](wiki/concepts/) containing:

* The verbatim Bach (2024) excerpt (when available).
* The Lean port: file path, theorem name, hypotheses, conclusion.
* The DAG context: which concepts are prerequisites, which depend on
  this one.
* The audit status: A (provably-equivalent to Bach's statement),
  A-leaning (likely-equivalent, minor scope question), B (parametrized
  abstraction; Bach's specific statement is a corollary), Deferred
  (placeholder anchor; full proof pending Mathlib infrastructure).

Five index views aggregate the per-concept pages:

* [Index by chapter](wiki/indexes/by-chapter.md) --- groups concepts by
  Bach chapter (1-15).
* [Index by tier](wiki/indexes/by-tier.md) --- L1 (undergraduate-tier
  algebra), L2 (multi-step analysis), L3 (graduate / measure-theoretic).
* [Index by status](wiki/indexes/by-status.md) --- audit classification.
* [Index by topic](wiki/indexes/by-topic.md) --- coarse keyword tags
  (concentration, optimization, kernels, etc.).
* [Index by Mathlib dependency](wiki/indexes/by-mathlib-dep.md) ---
  groups concepts by which Mathlib subsystems they depend on.

Two Mermaid graphs visualize the dependency structure:

* [Full dependency graph](wiki/graphs/full-deps.mmd) --- every concept,
  every edge.
* [Per-chapter dependency graphs](wiki/graphs/per-chapter.mmd) --- one
  subgraph per chapter, easier to read.

### Walkthrough-style narrative companions

For each of the three flagship `LTFP/Examples/` files, a narrative
companion under [`docs/teaching/`](teaching/) re-tells the proof in
prose with embedded code snippets:

* [`docs/teaching/walkthrough-bernstein.md`](teaching/walkthrough-bernstein.md)
  --- narrative companion to `LTFP/Examples/Bernstein.lean`.
* [`docs/teaching/walkthrough-pacbayes.md`](teaching/walkthrough-pacbayes.md)
  --- narrative companion to `LTFP/Examples/PACBayesMcAllester.lean`.
* [`docs/teaching/problem-sets.md`](teaching/problem-sets.md) --- broader
  curriculum guide listing all five problem sets with grading notes.

Pinsker / Bretagnolle-Huber does not yet have a narrative companion;
the file `LTFP/Examples/PinskerBH.lean` is already self-contained and
heavily commented.

## The textbook-strict branch: proofs that mirror Bach

The `main` branch optimizes for Mathlib compatibility: when Mathlib has
a more general statement, the LTlib theorem is wired to it (e.g., the
generic Hoeffding MGF in
`Mathlib.Probability.Moments.SubGaussian.Basic`), and the Bach-specific
constants emerge as instances.

The `textbook-strict` branch (this one) ships an additional layer of
named carrier theorems that mirror Bach's exposition step-by-step. For
example:

* `bach_taylor_mgf` --- Bach Lemma 1.2.3(a), the per-summand MGF bound,
  proved by Bach's Taylor-expansion + Bochner integration argument.
* `bach_taylor_mgf_iid_sum` --- the iid-sum upgrade Bach writes between
  Lemmas 1.2.3(a) and the displayed Bernstein tail.
* `bach_bernstein_tail_one_sided` --- Bach's one-sided Bernstein tail,
  with Bach's specific exponent `exp(-ε² / (2 (nσ² + cε/3)))`.
* `pac_bayes_bach_step1_hoeffding_per_theta` --- Bach Eq. (14.4), the
  per-θ Hoeffding MGF in the PAC-Bayes chain.
* `pac_bayes_bach_step2_integrate_prior` --- Bach §14.4.2's "integrate
  over the prior" step, factored out as a standalone lemma.
* `pac_bayes_mcallester_bach_path_a_class` --- the full McAllester bound
  (Bach Eq. 14.6) composing Steps 1-4.

These names exist because Bach's textbook compresses many of the
intermediate steps into the running narrative. By naming each Bach lemma
as its own theorem, the formalization can be cited by students and by
downstream callers who want to swap a single step (e.g., use a different
MGF bound while keeping the rest of the PAC-Bayes chain).

For teaching, `textbook-strict` is therefore the recommended branch:
the Lean proofs match the textbook proofs line-for-line where possible,
and deviations are documented in
[`docs/ERRATA.md`](ERRATA.md).

## Problem sets: starter pack

The starter pack lives at
[`tasks/student-problems/`](../tasks/student-problems/) and spans Bach
Chapters 1, 5, 7, 14, and 15. See
[`tasks/student-problems/README.md`](../tasks/student-problems/README.md)
for the table of problems and the verification protocol. Brief summary:

| # | Bach | File | Difficulty | Concept |
|---|---|---|---|---|
| 1 | §1.2.1 | `ch01-bernstein-warmup.lean` | Easy | Scalar Bernstein MGF |
| 2 | §5.1 | `ch05-gd-descent.lean` | Medium | L-smooth descent at η=1/L |
| 3 | §7.2 | `ch07-representer.lean` | Medium | Minimizer in span of features |
| 4 | §14.4.2 | `ch14-pac-bayes-step1.lean` | Medium-Hard | Per-θ Hoeffding linear MGF |
| 5 | §15.1 | `ch15-pinsker-bh.lean` | Medium-Hard | tv ≤ √KL (weak Pinsker / BH) |

Each problem is a Lean 4 stub: a theorem statement with a `sorry`
placeholder. The docstring above the stub lists the Bach section
reference, suggested LTlib carrier lemmas, expected proof length, and
common pitfalls. Students replace `sorry` with a proof and verify with
`lake build LTFP.<module>`.

For grading, the longer-form curriculum guide at
[`docs/teaching/problem-sets.md`](teaching/problem-sets.md) lists
solution sketches, alternative proof routes, and per-problem rubrics.

Solutions are intentionally NOT in the public repository. Faculty
assigning LTlib problem sets are encouraged to fork, add solutions in
a private branch, and grade by `lake build` plus visual inspection of
`#print axioms`.

## Errata: when Bach is slightly wrong

The Lean type system forces every hypothesis to be made explicit. When
porting a textbook proof, the formalization occasionally surfaces an
implicit assumption that the printed proof glosses over, or a stated
bound that does not go through as printed without a small modification.
These observations are collected in [`docs/ERRATA.md`](ERRATA.md), with
the following format:

* **Textbook:** what the book states.
* **Observation:** what the formalization made explicit.
* **Suggested clarification:** a one-sentence fix the next edition
  could adopt.
* **Lean reference:** the file where the textbook-strict port surfaced
  the issue.

For teaching, `docs/ERRATA.md` is itself useful material. A discussion
prompt like *"the textbook says the matrix Bernstein bound holds under
hypotheses X; the Lean port required strengthening to X'. Why?"* turns
a textbook erratum into a 30-minute classroom discussion of when an
implicit hypothesis matters.

Periodic batches of errata are forwarded to the textbook author for
consideration in future editions.

## Contributing tutorials and problems back

See [`CONTRIBUTING.md`](../CONTRIBUTING.md) for the general contribution
workflow. For teaching-specific contributions:

* **Tutorials.** Add a new file to `LTFP/Examples/` following the
  template of `Bernstein.lean` / `PinskerBH.lean` /
  `PACBayesMcAllester.lean`: a top docstring linking back to the Bach
  section, then a series of `example` blocks discharging a named
  carrier at a concrete shape, with rich inline commentary. Add the
  new file to `LTFP/Examples.lean`. Optionally add a narrative
  companion to `docs/teaching/`.
* **Problem sets.** Add a new `.lean` stub to
  `tasks/student-problems/` with a `sorry` placeholder and a docstring
  containing the Bach reference, hints, expected length, and pitfalls.
  Update `tasks/student-problems/README.md` with the new row. Faculty
  forking the repo for grading should maintain solutions in a separate
  branch.
* **Errata.** Add an entry to `docs/ERRATA.md` following the format at
  the top of that file. Cite a specific Bach section and page; propose
  a constructive clarification.
* **Wiki updates.** The wiki under `docs/wiki/` is generated by
  `python -m tools.build_wiki` from `doc/concepts.yaml`. The tooling
  itself is gitignored on the public repo; the generated output is
  pushed to the `textbook-strict` branch. Wiki pull requests are
  accepted as manual edits, but the next `tools.build_wiki` run will
  normalize the layout.

Pull requests targeting `textbook-strict` are reviewed for
pedagogical fit (does the example or problem set advance the
classroom-use case?) in addition to Lean correctness.
