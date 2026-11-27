"""Integrity-checked merge of independently compiled ZeroLF root13 children."""
import hashlib, json, pathlib, shutil, sys
work = pathlib.Path(sys.argv[1]).resolve()
out = work / "root13-merged"
build = out / "build"
build.mkdir(parents=True, exist_ok=True)
digest = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
core = json.loads((work / "core.json").read_text())
modules = {}
revisions = set(core.get("source_revisions", [core["proof_source_revision"]]))
def ingest(m, root):
    assert m["lean_version"] == core["lean_version"]
    assert m["lean_binary"]["sha256"] == core["lean_binary"]["sha256"]
    revisions.update(m.get("source_revisions", [m["proof_source_revision"]]))
    for e in m["modules"]:
        name = e["module"]
        src = root / e["olean_path"]
        assert src.is_file() and digest(src) == e["olean_sha256"], name
        if name in modules:
            assert modules[name]["module_identity_sha256"] == e["module_identity_sha256"], name
            assert modules[name]["source_sha256"] == e["source_sha256"], name
            assert modules[name]["project_imports"] == e["project_imports"], name
            continue
        modules[name] = e
        dst = build / e["olean_path"]
        dst.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(src, dst)
ingest(core, work / "core")
for i in range(24):
    shard = work / "children" / f"raw139-e0-zeroLF-root13-child{i}-certified"
    m = json.loads((shard / "manifest.json").read_text())
    assert m["claim"]["theorem"] == f"BB6.Agent14E0LFParent.cZLFRoot13_{i}"
    assert m["claim"]["weighted_bound"] == 19007
    ingest(m, shard / "build")
merged = dict(core, modules=list(modules.values()), module_count=len(modules),
              source_revisions=sorted(revisions))
(out / "manifest.json").write_text(json.dumps(merged, indent=2) + "\n")
print("Merged", len(modules), "source/import/olean-identified modules;",
      len(revisions), "source revisions")
