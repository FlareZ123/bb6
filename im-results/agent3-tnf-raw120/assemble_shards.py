"""Merge source-checked raw120 child artifacts from a pinned matrix and its 1LB repair.

Every module is checked against its source and object hashes. A duplicate
module must have the same recursive dependency identity. No acceptance is
inferred from a manifest alone: the final Lean invocation checks the parent.
"""
from pathlib import Path
import hashlib
import json
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
EXPECTED = {"0LA","0LB","0LF","0RA","0RB","0RC","0RF",
            "1LA","1LB","1LF","1RA","1RB","1RC","1RF","cycles"}

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def safe(base, rel):
    p = Path(rel)
    assert not p.is_absolute() and ".." not in p.parts, rel
    return base / p

def assemble(input_dir, output_dir):
    input_dir, output_dir = Path(input_dir), Path(output_dir)
    output_dir.mkdir(parents=True, exist_ok=True)
    assert {p.name.removeprefix("raw120-child-") for p in input_dir.iterdir()} == EXPECTED
    revision = subprocess.check_output(["git","rev-parse","HEAD"], cwd=ROOT, text=True).strip()
    modules, roots, metadata = {}, [], None
    revisions = set()
    old_revision = "3a45edaf85bc519ee64e07f5b1379664b352a023"
    for shard in sorted(input_dir.iterdir()):
        manifest = json.loads((shard / "manifest.json").read_text())
        assert manifest["schema_version"] == 1
        child = shard.name.removeprefix("raw120-child-")
        source_revision = manifest["proof_source_revision"]
        assert source_revision == revision or (child != "1LB" and source_revision == old_revision), (child, source_revision)
        revisions.add(source_revision)
        fields = (manifest["lean_version"], manifest["lean_binary"]["sha256"])
        if metadata is None:
            metadata = fields
        assert fields == metadata, shard
        roots.extend(manifest["roots"])
        for entry in manifest["modules"]:
            name = entry["module"]
            src = safe(shard / "objects", name.replace(".", "/") + ".lean")
            obj = safe(shard / "objects", entry["olean_path"])
            assert digest(src) == entry["source_sha256"], (shard,name,"source")
            assert digest(obj) == entry["olean_sha256"], (shard,name,"object")
            if name in modules:
                previous = modules[name]
                assert entry["module_identity_sha256"] == previous["module_identity_sha256"], (shard,name,"dependency identity")
                assert entry["source_path"] == previous["source_path"], (shard,name,"source path")
                continue
            modules[name] = entry
            original = safe(ROOT, entry["source_path"])
            if original.exists():
                assert digest(original) == entry["source_sha256"], (shard,name,"checkout source")
            else:
                assert entry["source_kind"] != "tracked", (shard,name,"missing tracked source")
                original.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(src, original)
            dest = safe(output_dir, entry["olean_path"])
            dest.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(obj, dest)
    assert metadata is not None
    merged = {"schema_version":1,"proof_source_revision":revision,
              "source_revisions":sorted(revisions),"lean_version":metadata[0],
              "lean_binary":{"sha256":metadata[1]},"roots":roots,
              "module_count":len(modules),"modules":list(modules.values())}
    (output_dir / "manifest.json").write_text(json.dumps(merged,indent=2,sort_keys=True)+"\n")
    print("Merged",len(modules),"source-checked modules from",len(EXPECTED),"shards")

if __name__ == "__main__":
    assert len(sys.argv) == 3
    assemble(*sys.argv[1:])
