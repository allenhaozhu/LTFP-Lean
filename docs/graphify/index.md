# Interactive graph

A navigable knowledge graph of the **336 named theorems, lemmas, and
definitions** in the LTlib wiki. Each node is one Bach result — click
it and you land on the wiki concept page containing the verbatim Bach
excerpt and the corresponding Lean theorem name.

Edges:

- **Structural** — explicit dependency or citation extracted from the
  wiki pages
- **Semantic** — inferred similarity (two results that solve the same
  problem or share an assumption)

Nodes are colored by community and communities are **color-coded with
semantic labels** (e.g. *Surrogate Φ Functions*, *OLS & Fixed Design*,
*PAC-Bayes McAllester*, *|·| Triangle Inequalities*). Hover or click a
node to see its community name in the side panel.

<iframe
  src="graph.html"
  width="100%"
  height="720"
  style="border: 1px solid #ccc; border-radius: 4px;"
  loading="lazy"
></iframe>

[Open in a new tab](graph.html) · [Download graph.json](graph.json)
