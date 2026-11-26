"""Merge dependency-closed artifacts; reject disagreeing shared object identities."""
import hashlib
import json
import pathlib
import shutil
import sys

work = pathlib.Path(sys.argv[1]).resolve()
parent = work / "conditional" / "parent"
proof = work / "exception"
out = work / "merged"
out.mkdir(parents=True, exist_ok=True)
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
sources = [parent]
if proof.exists():
    sources.append(proof)
modules = {}
revisions = set()
core = None
for src in sources:
    manifest = json.loads((src / "manifest.json").read_text())
    if src == parent:
        assert manifest["claim"]["theorem"] == "BB6.Agent14E0LFParent.weighted_conditional"
        assert manifest["claim"]["weighted_bound"] == 19007
        assert json.loads(manifest["claim"]["parent_table"]) == [7,24,11,24,14,24,24,16,20,11,24,24]
    else:
        assert manifest["claim"]["theorem"] == "BB6.Agent14ZeroLF3862.weighted"
        assert json.loads(manifest["claim"]["parent_table"]) == [7,10,11,19,14,17,24,16,20,11,3,0]
    if core is None:
        core = manifest
    else:
        assert core["lean_version"] == manifest["lean_version"]
        assert core["lean_binary"]["sha256"] == manifest["lean_binary"]["sha256"]
    revisions.update(manifest.get("source_revisions", [manifest["proof_source_revision"]]))
    for entry in manifest["modules"]:
        name = entry["module"]
        relative = pathlib.Path(entry["olean_path"])
        assert not relative.is_absolute() and ".." not in relative.parts
        source = src / "build" / relative
        assert digest(source) == entry["olean_sha256"], name
        if name in modules:
            assert modules[name]["module_identity_sha256"] == entry["module_identity_sha256"], name
            continue
        modules[name] = entry
        target = out / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)
merged = dict(core, modules=list(modules.values()), module_count=len(modules),
              source_revisions=sorted(revisions))
(work / "merged.json").write_text(json.dumps(merged, indent=2) + "\n")
print("Merged", len(modules), "checked module identities from", len(sources), "closures.")
