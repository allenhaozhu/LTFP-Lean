# LTlib — Lean 4 Companion to Bach (2024)

LTlib (package `LTFP-Lean`) is a Lean 4 formalization of Francis Bach's
*Learning Theory from First Principles* (MIT Press, 2024), Chapters
1–15. Every chapter-anchor theorem holds unconditionally with axiom
set `[propext, Classical.choice, Quot.sound]` only (verified by
end-of-session audit).

**Latest release**: [`v6.0.0-tierC-discharged`](https://github.com/allenhaozhu/LTFP-Lean/releases/tag/v6.0.0-tierC-discharged)
on `main`. This site is built from the [`textbook-strict`
branch](https://github.com/allenhaozhu/LTFP-Lean/tree/textbook-strict)
which ships proofs that mirror Bach's exposition step-by-step.

## Start here

- 📖 **[For Students & Teachers](TEACHING.md)** — guided entrypoint
- 🗺️ **[Mini-wiki](wiki/README.md)** — per-concept index across the library
- 📝 **[Walkthroughs](teaching/walkthrough-bernstein.md)** — Bernstein §1.2.3 in prose
- 🧩 **[Problem sets](teaching/problem-sets.md)** — 5 starter stubs across chapters
- 🐛 **[Errata](ERRATA.md)** — textbook corrections surfaced during formalization

## What's in the library

- `LTFP/Ch01_Preliminaries` through `LTFP/Ch15_LowerBounds` — chapter modules
- `LTFP/MathlibExt/` — extension modules carrying Mathlib-absent prerequisites
- `LTFP/Examples/` — worked walkthroughs (Bernstein, Pinsker-BH, PAC-Bayes)
- `LTFP/Foundations/` — vendored kernel ([auto-res/lean-rademacher](https://github.com/auto-res/lean-rademacher))

## Source

[github.com/allenhaozhu/LTFP-Lean](https://github.com/allenhaozhu/LTFP-Lean)
