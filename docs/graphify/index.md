# Interactive graph

A navigable knowledge graph of the LTlib codebase: god nodes
(most-connected core abstractions), communities (clusters of
related concepts), and cross-cutting connections (semantic
similarities that span chapters).

The graph below is built by the [graphify](https://pypi.org/project/graphifyy/)
knowledge-graph extractor over the public LTlib corpus
(`LTFP/`, `docs/wiki/`, `docs/teaching/`, errata).
For a plain-language tour of the same data, see
[Library overview](../library-overview.md).

<iframe
  src="graph.html"
  width="100%"
  height="720"
  style="border: 1px solid #ccc; border-radius: 4px;"
  loading="lazy"
></iframe>

[Open in a new tab](graph.html) · [Download graph.json](graph.json)
