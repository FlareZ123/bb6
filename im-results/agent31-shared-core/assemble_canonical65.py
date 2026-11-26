"""Check the three additional accepted parent closures on the stable 68 roster."""
from assemble_canonical68 import (PINS, SOURCE_REVISIONS, HERE, api_json,
    download, link_reachable, compile_module, gate, sha)
from pathlib import Path
import argparse
import json
import os
import subprocess

THREE = (15001137494, 45560876359, "36c86203f3f7fb589b221046038513097a03534c8dc029cd83c328db53ae09aa")
THREE_REVISION = "735f449865149459df272eb9b858cf8ccf793404"

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    work = ap.parse_args().work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    assert "4.36.0-rc2" in subprocess.check_output(["lean", "--version"], text=True)
    runs = {run: SOURCE_REVISIONS[run] for _, run, _ in PINS[:2]}
    runs[THREE[1]] = THREE_REVISION
    for run, rev in runs.items():
        info = api_json(f"repos/FlareZ123/bb6/actions/runs/{run}")
        assert info["head_sha"] == rev
        if run == 45647053824:
            job = api_json("repos/FlareZ123/bb6/actions/jobs/139320746934")
            assert job["run_id"] == run and job["conclusion"] == "success"
        else:
            assert info["conclusion"] == "success"
    stable = [download(pin, work) for pin in PINS[:2]]
    other = download(THREE, work)
    linked = work / "linked"
    families = [
        ("canonical76", [p for g in reversed(stable) for p in g],
         ["CanonicalTwoParentRosterOnly", "CanonicalRosterRefinement"]),
        ("raw71-77-81", other, ["Raw71Data", "Raw77Data", "Raw81Data"]),
    ]
    link_reachable(stable, work, linked, families=families)
    env = dict(os.environ, LEAN_PATH=str(linked))
    log = compile_module(HERE / "Canonical68StableBatch.lean", linked / "Canonical68StableBatch.olean", env, work / "stable68.log")
    gate(log, ["BB6.Agent31StableParentBatch." + n for n in ["removeParents_sound", "liftCover", "parent_roots", "count68", "sound68", "exact_at_target"]])
    source = HERE / "Canonical65AfterThree.lean"
    obj = linked / "Canonical65AfterThree.olean"
    log = compile_module(source, obj, env, work / "canonical65.log")
    report = {"pins": PINS[:2] + [THREE], "source_revisions": runs,
              "axioms": gate(log, ["BB6.Agent31Canonical65AfterThree." + n for n in ["extra_roots", "extra_covers", "count65", "sound65", "exact_at_target"]]),
              "source_sha256": sha(source), "olean_sha256": sha(obj)}
    (work / "canonical65-axioms.json").write_text(json.dumps(report, indent=2) + "\n")

if __name__ == "__main__":
    main()
