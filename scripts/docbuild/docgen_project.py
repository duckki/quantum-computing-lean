#!/usr/bin/env python3
"""Generate doc-gen4 HTML for this project's Lean library modules only."""

from __future__ import annotations

import shutil
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
DOCBUILD_DIR = ROOT / "scripts" / "docbuild"
GENERATED_DIR = ROOT / "docs-generated"
TOOL_LAKE_DIR = GENERATED_DIR / ".lake" / "docbuild"
CACHE_BUILD_DIR = GENERATED_DIR / ".cache" / "doc-gen-build"
OUTPUT_DIR = GENERATED_DIR / "doc-gen"
DB_NAME = "api-docs.db"
DB_PATH = CACHE_BUILD_DIR / DB_NAME
MANIFEST_PATH = CACHE_BUILD_DIR / "doc-manifest.json"
PROJECT_ROOT_MODULE = "QuantumComputing"


def lake(*args: str) -> None:
    subprocess.run(
        [
            "lake",
            "-d",
            str(DOCBUILD_DIR),
            f"-KlakeDir={TOOL_LAKE_DIR}",
            *args,
        ],
        cwd=ROOT,
        check=True,
    )


def module_name(path: Path) -> str:
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def project_modules() -> list[tuple[str, Path]]:
    root_file = ROOT / f"{PROJECT_ROOT_MODULE}.lean"
    module_dir = ROOT / PROJECT_ROOT_MODULE
    modules = [(module_name(path), path) for path in [root_file, *module_dir.rglob("*.lean")]]
    return sorted(modules)


def main() -> None:
    modules = project_modules()
    if not modules:
        raise SystemExit("no project modules found")

    GENERATED_DIR.mkdir(exist_ok=True)
    CACHE_BUILD_DIR.parent.mkdir(parents=True, exist_ok=True)
    if CACHE_BUILD_DIR.exists():
        shutil.rmtree(CACHE_BUILD_DIR)
    CACHE_BUILD_DIR.mkdir(parents=True)

    print("Building project modules and doc-gen4...", flush=True)
    lake("build", PROJECT_ROOT_MODULE)
    lake("build", "«doc-gen4»:exe")

    print("Preparing doc-gen4 cache...", flush=True)
    lake("env", "doc-gen4", "bibPrepass", "--build", str(CACHE_BUILD_DIR), "--none")

    for index, (name, path) in enumerate(modules, start=1):
        print(f"[{index}/{len(modules)}] documenting {name}", flush=True)
        lake(
            "env",
            "doc-gen4",
            "single",
            "--build",
            str(CACHE_BUILD_DIR),
            name,
            DB_NAME,
            path.resolve().as_uri(),
        )

    print("Rendering project-only HTML...", flush=True)
    lake(
        "env",
        "doc-gen4",
        "fromDb",
        "--build",
        str(CACHE_BUILD_DIR),
        "--manifest",
        str(MANIFEST_PATH),
        str(DB_PATH),
    )

    if OUTPUT_DIR.exists():
        shutil.rmtree(OUTPUT_DIR)
    shutil.copytree(CACHE_BUILD_DIR / "doc", OUTPUT_DIR)
    print(f"Wrote {OUTPUT_DIR.relative_to(ROOT)}", flush=True)


if __name__ == "__main__":
    main()
