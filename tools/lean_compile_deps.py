"""Compile local Lean modules and their imported repository dependencies.

This is a deterministic DAG traversal over import declarations. Lean itself
validates the syntax and semantics; unrecognized imports are resolved by the
pinned toolchain and fail closed if unavailable.
"""
import os
from pathlib import Path
import re
import subprocess
import sys

ROOTS = [Path(p) for p in os.environ["LEAN_PATH"].split(os.pathsep) if p]
VISITED: set[Path] = set()
ACTIVE: set[Path] = set()
IMPORT_RE = re.compile(r"^\s*import\s+(.+?)\s*(?:--.*)?$")


def locate(module: str) -> Path | None:
    relative = Path(*module.split(".")).with_suffix(".lean")
    for directory in ROOTS:
        source = directory / relative
        if source.is_file():
            return source
    return None


def build(source: Path) -> None:
    source = source.resolve()
    if source in VISITED:
        return
    if source in ACTIVE:
        raise RuntimeError(f"cyclic Lean module imports at {source}")
    ACTIVE.add(source)
    for line in source.read_text(encoding="utf-8").splitlines():
        match = IMPORT_RE.match(line)
        if match:
            for name in match.group(1).split():
                child = locate(name)
                if child is not None:
                    build(child)
    print(f"LEAN {source}", flush=True)
    result = subprocess.run(
        ["lean", "-o", str(source.with_suffix(".olean")), str(source)],
        check=False,
        text=True,
    )
    if result.returncode:
        raise SystemExit(result.returncode)
    ACTIVE.remove(source)
    VISITED.add(source)


def main() -> None:
    for target in sys.argv[1:]:
        source = Path(target)
        if not source.is_file():
            raise FileNotFoundError(source)
        build(source)
    print(f"Compiled {len(VISITED)} local Lean modules", flush=True)


if __name__ == "__main__":
    main()
