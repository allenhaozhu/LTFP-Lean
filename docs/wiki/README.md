# LTFP-Lean mini-wiki

This wiki indexes the LTFP-Lean library at the **per-concept** level: each theorem / lemma / definition from Bach (2024), *Learning Theory from First Principles*, has its own page with the verbatim textbook excerpt, dependency edges, audit status, and a pointer to its Lean port.

## Why this exists

Chapter directories are storage organization, not the primary browsing structure. This wiki answers *'does Bach actually prove X, and where is it formalized?'* in seconds, indexed by concept id. Equation labels in synthesized notes can drift relative to the canonical Bach (2024) PDF, so every claim about the textbook is backed here by a verbatim excerpt.

## Retrieval principles

1. **Concept-id is the unit of retrieval.** Each page lives at [`concepts/<id>.md`](./concepts/). Chapter folders are not.
2. **Every claim about Bach's textbook MUST be backed by a verbatim excerpt** under `## Bach's textbook treatment`. If that section says *No book excerpt available*, the claim is unverified.
3. **The DAG is canonical.** Prereqs / dependents are drawn directly from `doc/dag.json`, which is computed by `python -m tools.build_dag` from `doc/concepts.yaml`.
4. **Status is from the audit, not from `status: done`.** PROGRESS.md §10 distinguishes A / A-leaning / B / Deferred — the wiki surfaces this so a downstream reader can see whether a theorem is *actually proved* vs. *parametrized abstraction*.

## Layout

```
docs/wiki/
├── README.md             — this file
├── concepts/<id>.md       — one page per concept
├── indexes/
│   ├── by-chapter.md      — concepts grouped by Ch01..Ch15
│   ├── by-tier.md         — L1/L2/L3 heuristic
│   ├── by-status.md       — A / A-leaning / B / Deferred
│   ├── by-topic.md        — coarse keyword tags
│   └── by-mathlib-dep.md  — Mathlib dependency status
├── graphs/
│   ├── full-deps.mmd      — full Mermaid DAG
│   └── per-chapter.mmd    — per-chapter Mermaid subgraphs
└── BUILD_LOG.md           — generator output: stats + gaps
```

## Build stats

- **Concepts:** 339
- **Concepts with book excerpt:** 331
- **Concepts with inferred_proof.md:** 0
- **Audit-classified A:** 2
- **Audit-classified A-leaning:** 2
- **Audit-classified B:** 6
- **Deferred:** 1
- **Unaudited:** 322

## Quick links

- [Index by chapter](./indexes/by-chapter.md)
- [Index by tier](./indexes/by-tier.md)
- [Index by status](./indexes/by-status.md)
- [Index by topic](./indexes/by-topic.md)
- [Index by Mathlib dependency](./indexes/by-mathlib-dep.md)
- [Full dependency graph](./graphs/full-deps.mmd)
- [Per-chapter dependency graphs](./graphs/per-chapter.mmd)
- [Build log](./BUILD_LOG.md)

## Regenerating

```bash
python -m tools.build_wiki      # or: uv run python -m tools.build_wiki
```

Idempotent: running twice produces byte-identical output (modulo the timestamp in BUILD_LOG.md).

_Generated 2026-05-27 00:15:00 UTC_
