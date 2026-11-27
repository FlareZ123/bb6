"""Merge exact Raw43 child proof manifests; lean_compile_closure rechecks the import DAG."""
import hashlib
import json
import shutil
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent
branch = sys.argv[4] if len(sys.argv) > 4 else "b1rc"
VARIANTS = {"b1re": ("0la","0lb","0lc","0le","0lf","0rc","0re","0rf","1la","1lc","1ld","1le","1lf","1rd","1re","1rf"), "b1le": ("0la","0lb","0lc","0ld","0le","0lf","0ra","0rc","0re","0rf","1la","1lb","1lc","1le","1lf","1ra","1rb","1rc","1re","1rf"), "b0le": ("0lc","0le","0ra","0rb","0re","0rf","1lc","1rb","1re"), "b1rc": ("0la", "0le", "0re", "1la", "1le", "1re"), "b0rc": ("0le", "0re", "1le", "1re"), "b0ra": ("0le","0rc","0re","1lb","1le","1re"), "b0la": ("0la","0lb","0le","0re","1la","1lb","1le","1re"), "b1ra": ("0lc","0le","0rc","0re","1lc","1le","1re"), "b1lb": ("0la","0le","0ra","0re","1la","1le","1ra","1re"), "b1la": ("0lb","0lc","0ld","0le","0rc","0re","1lb","1lc","1le","1rc","1re")}[branch]
src, out = map(Path, sys.argv[1:3])
out.mkdir(parents=True, exist_ok=True)
pins = json.loads(sys.argv[3])
if branch == 'b0le' and '1le' in pins:
    VARIANTS += ('1le',)
assert set(pins) == set(VARIANTS)
slot = "e1" if branch == "b1re" else "e" if branch in {"b0le","b1le"} else "a" if branch in {"b0ra","b1ra","b1la"} else "c"
entries = {}
revisions = set()
base = None
for v in VARIANTS:
    d = src / v
    m = json.loads((d / "manifest.json").read_text())
    spec = json.loads((ROOT / f"spec_{branch}_{slot}{v}.json").read_text())
    expected = f"BB6.Agent25Raw43{branch.upper()}_{slot.upper()}{v.upper()}.all43child"
    assert m["schema_version"] == 1
    assert m["workflow"]["run_id"] == str(pins[v]), (v, "wrong run")
    assert m["claim"]["theorem"] == expected, (v, m["claim"])
    assert m["claim"]["weighted_bound"] == spec["bound"]
    assert m["artifact_name"] == "raw43-extra-proof"
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
        obj = d / rel
        h = hashlib.file_digest(obj.open("rb"), "sha256").hexdigest()
        assert h == e["olean_sha256"], (v, module, "object mismatch")
        if module in entries:
            assert entries[module]["module_identity_sha256"] == e["module_identity_sha256"], (v, module, "identity conflict")
        else:
            entries[module] = e
            target = out / rel
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(obj, target)
merged = dict(base, source_revisions=sorted(revisions), modules=list(entries.values()),
              module_count=len(entries), claim={"theorem": None}, label=f"raw43-{branch}-child-precompiled",
              roots=[], provenance_inputs=[])
(out / "manifest.json").write_text(json.dumps(merged, indent=2, sort_keys=True)+"\n")
print("Merged", len(entries), "exact dependency-closed modules from", len(VARIANTS), "accepted children")
