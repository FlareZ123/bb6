#!/usr/bin/env python3
"""Regression for qualified upstream module paths and flat im-results imports.

Run with:
  python3 tools/test_lean_compile_module_index.py
"""
import importlib.util
from pathlib import Path
import tempfile
import sys

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location(
    "lean_compile_closure", ROOT / "tools/lean_compile_closure.py"
)
assert SPEC and SPEC.loader
MODULE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = MODULE
SPEC.loader.exec_module(MODULE)


def main():
    with tempfile.TemporaryDirectory(prefix="bb6-module-index-") as tmp:
        source_root = Path(tmp)
        (source_root / "Cryptids").mkdir()
        (source_root / "Cryptids" / "Machines.lean").write_text(
            "namespace Cryptids\nend Cryptids\n", encoding="utf-8"
        )
        nested = source_root / "BusyBeaver" / "BB6" / "NonHalt"
        nested.mkdir(parents=True)
        (nested / "Example.lean").write_text(
            "namespace BusyBeaver\nend BusyBeaver\n", encoding="utf-8"
        )
        (source_root / "BB6ModuleIndexFlatProbe.lean").write_text(
            "namespace BB6ModuleIndexFlatProbe\nend BB6ModuleIndexFlatProbe\n", encoding="utf-8"
        )

        index = MODULE.module_index([source_root])
        import_probe = source_root / "ImportModifiers.lean"
        import_probe.write_text(
            "public import Cryptids.Machines\n"
            "meta import BusyBeaver.Basic\n"
            "import Foo Bar\n",
            encoding="utf-8",
        )
        assert MODULE.parse_imports(import_probe) == [
            "Cryptids.Machines", "BusyBeaver.Basic", "Foo", "Bar"
        ]
        old_overrides = MODULE.OVERRIDES.copy()
        MODULE.OVERRIDES.clear()
        try:
            assert MODULE.resolve_source("Cryptids.Machines", index) == (
                source_root / "Cryptids" / "Machines.lean"
            ).resolve()
            assert MODULE.resolve_source(
                "BusyBeaver.BB6.NonHalt.Example", index
            ) == (nested / "Example.lean").resolve()
            assert MODULE.resolve_source("BB6ModuleIndexFlatProbe", index) == (
                source_root / "BB6ModuleIndexFlatProbe.lean"
            ).resolve()
        finally:
            MODULE.OVERRIDES.update(old_overrides)

    print("PASS: qualified upstream and flat repository module imports resolve")


if __name__ == "__main__":
    main()
