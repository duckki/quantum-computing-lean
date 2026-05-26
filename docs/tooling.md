# Lean Tooling

This repo uses standard Lean ecosystem tooling for declaration documentation and
module dependency visualization.

## Tooling Stack

- [`doc-gen4`](https://github.com/leanprover/doc-gen4): generated HTML
  documentation for Lean libraries, including module pages, declaration pages,
  search, cross-links, and source links.
- [`importGraph`](https://github.com/leanprover-community/import-graph):
  generated import graphs for Lean packages.
- [Graphviz](https://graphviz.org/): DOT rendering for the readable SVG
  dependency graph.

The nested Lake tooling project lives in `scripts/docbuild`, keeping
documentation and graph tooling out of the proof library's direct dependency
surface. Tooling build output and package caches live under
`docs-generated/.lake`. Generated documentation cache data and intermediate DOT
files live under `docs-generated/.cache`.

## Setup

Install or refresh the pinned tooling dependencies:

```sh
make tooling-update
```

## Documentation

Build the declaration documentation site:

```sh
make docs
```

The entrypoint is:

```text
docs-generated/doc-gen/index.html
```

The docs target uses `doc-gen4`'s `single` and `fromDb` commands directly for
the `QuantumComputing` library modules. This emits project pages only and skips
`doc-gen4`'s slower Lean/Std/Lake/Init core documentation generation.

## Module Graph

Generate the module dependency graph:

```sh
make graph
```

The output is:

```text
docs-generated/module-graph.svg
```

The graph pipeline uses `importGraph` for Lean import extraction,
`scripts/graphviz/module-graph.gvpr` for box-style graph attributes, and
Graphviz `dot` for the final layered SVG.
