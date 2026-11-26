#!/usr/bin/env python3
"""Export only the new .olean objects from one Raw122 parent closure shard."""
from pathlib import Path
import hashlib
import json
import shutil
import sys

FIELDS = (
    "module", "source_path", "source_kind", "source_sha256",
    "project_imports", "olean_path", "olean_sha256",
    "import_closure_sha256", "module_identity_sha256",
)

def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()

def compare(left: dict, right: dict, module: str) -> None:
    differences = [k for k in FIELDS if left.get(k) != right.get(k)]
    if differences:
        raise RuntimeError(
            f"precompiled identity mismatch for {module}: {differences}"
        )

if len(sys.argv) != 6:
    raise SystemExit(
        "usage: export_parent_shard.py BASE_MANIFEST WORKDIR OUTDIR SHARD_ID ROOT_PATH"
    )

base_path, workdir, outdir = map(Path, sys.argv[1:4])
shard_id, root_path = sys.argv[4:6]
base = json.loads(base_path.read_text(encoding="utf-8"))
manifest_path = workdir / "manifest.json"
manifest = json.loads(manifest_path.read_text(encoding="utf-8"))

if manifest.get("schema_version") != base.get("schema_version"):
    raise RuntimeError("schema version differs from base manifest")
if manifest.get("lean_version") != base.get("lean_version"):
    raise RuntimeError("Lean version differs from base manifest")
if manifest.get("lean_binary", {}).get("sha256") != base.get("lean_binary", {}).get("sha256"):
    raise RuntimeError("Lean compiler binary differs from base manifest")

base_modules = {x["module"]: x for x in base.get("modules", [])}
outdir.mkdir(parents=True, exist_ok=True)
new_modules = []
for item in manifest.get("modules", []):
    module = item["module"]
    if module in base_modules:
        compare(base_modules[module], item, module)
        continue

    relative = Path(item["olean_path"])
    if relative.is_absolute() or ".." in relative.parts:
        raise RuntimeError(f"unsafe object path for {module}: {relative}")
    source = workdir / relative
    if not source.is_file():
        raise FileNotFoundError(source)
    actual = sha(source)
    if actual != item["olean_sha256"]:
        raise RuntimeError(
            f"compiled object hash mismatch for {module}: "
            f"{actual} != {item['olean_sha256']}"
        )
    destination = outdir / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    if destination.exists():
        if sha(destination) != actual:
            raise RuntimeError(f"conflicting shard object for {module}")
    else:
        shutil.copy2(source, destination)
    new_modules.append(module)

(outdir / "manifest.json").write_text(
    json.dumps(manifest, indent=2, sort_keys=True) + "\n",
    encoding="utf-8",
)
info = {
    "shard_id": shard_id,
    "root_path": root_path,
    "module_count": len(manifest.get("modules", [])),
    "base_module_count": len(base_modules),
    "new_module_count": len(new_modules),
    "new_modules": sorted(new_modules),
}
(outdir / "shard.json").write_text(
    json.dumps(info, indent=2, sort_keys=True) + "\n",
    encoding="utf-8",
)
print(json.dumps(info, indent=2), flush=True)
