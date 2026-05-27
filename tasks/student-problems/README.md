# LTlib Student Problems

A 5-problem starter set spanning Bach (2024) Chapters 1, 5, 7, 14, and 15.
Each problem is a Lean 4 stub with `sorry` placeholders. Open in VS Code
with the Lean extension; the infoview will display the goal state at each
step.

## Problems by difficulty

| # | Bach § | File | Difficulty | Concept |
|---|---|---|---|---|
| 1 | §1.2.1 | ch01-bernstein-warmup.lean | Easy | Scalar Hoeffding corollary |
| 2 | §5.1 | ch05-gd-descent.lean | Medium | L-smooth descent inequality at η=1/L |
| 3 | §7.2 | ch07-representer.lean | Medium | Minimizer lies in span {k(·,xⱼ)} |
| 4 | §14.4.2 | ch14-pac-bayes-step1.lean | Medium-Hard | Per-θ Hoeffding linear MGF |
| 5 | §15.1 | ch15-pinsker-bh.lean | Medium-Hard | tvDist ≤ √KL (Bretagnolle-Huber weak Pinsker) |

## How to use

1. Pick a problem matching your level.
2. Open the corresponding `.lean` file in VS Code (with the Lean 4
   extension installed).
3. Replace the `sorry` with a proof. The infoview shows the goal at each
   step.
4. Verify with `lake build LTFP.<chapter-module>` to ensure your proof
   composes with the rest of LTlib.

## Hints

Each problem file's docstring lists:
- The exact Bach (2024) section and page reference.
- Suggested LTlib lemmas and Mathlib API to use.
- Expected proof length (line count).
- Common pitfalls.

## Solutions

Solutions are intentionally NOT in this repository. Faculty assigning
LTlib problem sets can fork, add solutions in a separate branch, and
grade by `lake build`. See `docs/TEACHING.md` for grading patterns.
