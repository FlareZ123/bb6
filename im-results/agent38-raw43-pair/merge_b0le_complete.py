"""Merge the exact accepted proof closures needed for the complete Raw43 B0LE theorem."""
import hashlib
import json
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parents[1] / "agent25-raw43"
src = Path(sys.argv[1])
out = Path(sys.argv[2])
pins = json.loads(sys.argv[3])
variants = ("0la", "0lf", "1le", "1ra", "1la", "1lb", "1lf", "1rf")
assert set(pins) == {"reduced", *variants}
out.mkdir(parents=True, exist_ok=True)

entries = {}
revisions = set()
base = None

def merge_manifest(key, directory, expected_theorem, expected_artifact, expected_bound):
    global base
    m = json.loads((directory / "manifest.json").read_text())
    assert m["schema_version"] == 1
    assert m["workflow"]["run_id"] == str(pins[key]), (key, "wrong run", m["workflow"]["run_id"])
    assert m["claim"]["theorem"] == expected_theorem, (key, m["claim"])
    assert m["claim"]["weighted_bound"] == expected_bound, (key, m["claim"])
    assert m["artifact_name"] == expected_artifact, (key, m["artifact_name"])
    assert m["proof_source_revision"] == m["workflow"]["workflow_head_sha"]
    revisions.add(m["proof_source_revision"])
    if base is None:
        base = m
    assert m["lean_version"] == base["lean_version"]
    assert m["lean_binary"]["sha256"] == base["lean_binary"]["sha256"]
    for e in m["modules"]:
        module = e["module"]
        rel = Path(e["olean_path"])
        assert not rel.is_absolute() and ".." not in rel.parts
        obj = directory / rel
        assert hashlib.file_digest(obj.open("rb"), "sha256").hexdigest() == e["olean_sha256"], (key, module)
        if module in entries:
            assert entries[module]["module_identity_sha256"] == e["module_identity_sha256"], (
                key, module, "identity conflict")
            continue
        entries[module] = e
        target = out / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(obj, target)

merge_manifest(
    "reduced", src / "reduced",
    "BB6.Agent25Raw43B0LE.cover",
    "raw43-b0le-reduced-proof",
    287,
)
for v in variants:
    spec = json.loads((src / v / f"spec_b0le_e{v}.json").read_text())
    merge_manifest(
        v, src / v,
        f"BB6.Agent25Raw43B0LE_E{v.upper()}.all43child",
        "raw43-extra-proof",
        spec["bound"],
    )

merged = dict(
    base,
    source_revisions=sorted(revisions),
    modules=list(entries.values()),
    module_count=len(entries),
    claim={"theorem": None},
    label="raw43-b0le-complete-inputs",
    roots=[],
    provenance_inputs=[],
)
(out / "manifest.json").write_text(json.dumps(merged, indent=2, sort_keys=True) + "\n")
print("Merged", len(entries), "exact dependency-closed modules from reduced B0LE and", len(variants), "accepted child closures")
