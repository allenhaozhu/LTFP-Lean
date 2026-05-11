# Contributing

Thank you for your interest in extending LTFP-Lean.

## Scope

This library aims to formalize Bach (2024) *Learning Theory from First
Principles* and to supply the Mathlib-style infrastructure required for
its theorems. Pull requests are welcome that:

- Replace a placeholder / algebraic anchor with a full measure-theoretic
  or matrix-analytic proof.
- Add a chapter result that is not yet formalized.
- Strengthen `LTFP/MathlibExt/*` toward upstream Mathlib quality (so it
  can be PR'd to `leanprover-community/mathlib4`).
- Fix bugs, improve naming, add examples, or tighten proofs.

## Workflow

1. Fork the repo and create a topic branch:
   ```
   git checkout -b ltfp-<short-description>
   ```
2. Make your changes. Each modified or new file should:
   - Build under `lake build` with no `sorry` and no `admit`.
   - Carry full `/-- ... -/` docstrings on every public declaration.
   - Cite a Bach (2024) section or page in the file's header comment
     when applicable.
3. Verify:
   ```
   lake build
   ```
4. Commit using [Conventional Commits](https://www.conventionalcommits.org/)
   prefixes (`feat`, `fix`, `docs`, `refactor`, `chore`).
5. Open a PR against `main`.

## Style

- Imports: only `Mathlib.*` and `LTFP.*` (no `import Foo` from outside).
- Naming: Mathlib conventions — `lowerCamelCase` for `def`, `theorem`,
  and `lemma`; `PascalCase` for types and structures.
- Files: prefer 200-400 lines; split when a file exceeds 500.
- Namespaces: keep chapter content under `namespace LTFP`; keep
  Mathlib-extension content under `namespace LTFP.MathlibExt.<topic>`.

## Reporting issues

Open a GitHub issue with:
- The Bach (2024) section / page the theorem comes from,
- The exact symbol or file at fault (path:line),
- A minimal reproduction (failing `#check` or a 5-line Lean snippet).

## Code of conduct

Be kind. Be precise. Cite the source. When in doubt, follow Mathlib
community norms.
