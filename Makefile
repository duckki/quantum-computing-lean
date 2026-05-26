PROJECT_ROOT := $(abspath .)
DOCBUILD_DIR := scripts/docbuild
GENERATED_DIR := $(PROJECT_ROOT)/docs-generated
CACHE_DIR := $(GENERATED_DIR)/.cache
TOOL_LAKE_DIR := $(GENERATED_DIR)/.lake/docbuild
LAKE_DOCBUILD := lake -d $(DOCBUILD_DIR) -KlakeDir=$(TOOL_LAKE_DIR)
DOCGEN_DIR := $(GENERATED_DIR)/doc-gen
GRAPH_RAW_DOT := $(CACHE_DIR)/module-graph.raw.dot
GRAPH_DOT := $(CACHE_DIR)/module-graph.dot
GRAPH_SVG := $(GENERATED_DIR)/module-graph.svg

.PHONY: check tooling-update docs graph tooling

check:
	lake build

tooling-update:
	mkdir -p $(GENERATED_DIR)/.lake
	MATHLIB_NO_CACHE_ON_UPDATE=1 $(LAKE_DOCBUILD) update
	$(LAKE_DOCBUILD) exe cache get --skip-proofwidgets

docs:
	python3 scripts/docbuild/docgen_project.py

graph:
	mkdir -p $(CACHE_DIR)
	$(LAKE_DOCBUILD) build QuantumComputing
	$(LAKE_DOCBUILD) exe graph --to QuantumComputing $(GRAPH_RAW_DOT)
	gvpr -c -f scripts/graphviz/module-graph.gvpr $(GRAPH_RAW_DOT) > $(GRAPH_DOT)
	dot -Tsvg $(GRAPH_DOT) > $(GRAPH_SVG)

tooling: docs graph
