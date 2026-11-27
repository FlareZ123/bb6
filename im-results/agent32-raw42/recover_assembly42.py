#!/usr/bin/env python3
"""Recover missing Raw42 assembly groups without changing any accepted module.

Only the missing groups' generated import closures are eligible for conversion.
Every transformed source is compiled by the existing Lean closure checker.
The old groups are first merged using the existing exact manifest validator.
"""
import json
import re
import subprocess
import sys
from pathlib import Path
from convert_bidfa import convert
from split_small42 import split
from minimize_bidfa import minimize

BRANCHES = {
    "1LA": (45996630344, "9d157b474ac3ce708641ffe65070c7d0b472ae23", {"7"},
            {"Raw421LARun889", "Raw421LARun892"}),
    "1RA": (45996637267, "9d157b474ac3ce708641ffe65070c7d0b472ae23", {"1"},
            {"Raw421RARun7114", "Raw421RARun7242", "Raw421RARun7267"}),
}

def dump(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")

def prepare(repo, g, shards, shared, branch, original):
    run, revision, missing, suspects = BRANCHES[branch]
    cfg = json.loads((g / "shards.json").read_text())
    assert set(cfg["groups"]) == set(map(str, range(8)))
    prefix = cfg["artifact_prefix"]
    good = set(cfg["groups"]) - missing
    assert {p.name for p in shards.iterdir()} == {f"{prefix}-{i}" for i in good}
    for i in good:
        m = json.loads((shards / f"{prefix}-{i}" / "manifest.json").read_text())
        expected = ("cb294f1cff71bb89fc063d8cce01c8f3a0b4d71c"
                    if branch == "1RA" and i == "4" else revision)
        assert m["proof_source_revision"] == expected, (i, m["proof_source_revision"])
    subset = dict(cfg, groups={i: cfg["groups"][i] for i in sorted(good)},
                  allow_mixed_revisions=True)
    subpath = shared.with_name("accepted-groups.json")
    dump(subpath, subset)
    subprocess.run([sys.executable, str(repo / "im-results/agent4-raw109/merge_shards.py"),
                    str(shards), str(shared), str(subpath)], cwd=repo, check=True)
    manifest = json.loads((shared / "manifest.json").read_text())
    accepted = {x["module"] for x in manifest["modules"]}
    generated = {p.stem: p for p in g.glob("*.lean")}
    remaining = set()
    def visit(module):
        if module in accepted or module in remaining or module not in generated:
            return
        remaining.add(module)
        for line in generated[module].read_text().splitlines():
            if line.startswith("import "):
                for dep in line.split()[1:]:
                    visit(dep)
    for i in missing:
        for module in cfg["groups"][i]:
            visit(module)

    changes = {}
    reductions = {}
    for module in sorted(remaining):
        p = generated[module]
        if re.fullmatch(r"Raw42" + branch + r"Run\d+", module):
            # Reuse the original list witness, even if the previous recovery
            # converted this unaccepted module to a trie. Preserve accepted
            # module bytes and identities; only re-encode this missing slice.
            src = (original / p.name).read_text()
            reduced, before, after = minimize(src)
            if before[2] >= 200 or module in suspects or p.stat().st_size >= 50000:
                p.write_text(convert(reduced).replace(":= by decide\n", ":= by decide +kernel\n"))
                changes[module] = ["trie"]
                reductions[module] = {"before": before, "after": after}
    for module in sorted(remaining):
        p = generated[module]
        if re.fullmatch(r".*Root(?:_\d\d)*Small", module) and p.stat().st_size >= 50000:
            outputs = split(p)
            if outputs:
                changes[module] = [x.stem for x in outputs]
    assert set(changes).isdisjoint(accepted)
    assert all(x not in accepted for m, xs in changes.items() for x in xs if x != "trie")
    cfg["allow_mixed_revisions"] = True
    dump(g / "shards.json", cfg)
    dump(g / "recovery-plan.json", {
        "branch": branch, "source_run": run, "source_revision": revision,
        "missing_groups": sorted(missing), "reused_groups": sorted(good),
        "accepted_module_count": len(accepted),
        "changed_modules": changes,
        "relation_quotients": reductions,
        "suspects_already_accepted": sorted(suspects & accepted),
    })
    print("Recovered shared modules:", len(accepted), "changed generated modules:", len(changes))
    print("MISSING_GROUPS=" + json.dumps(sorted(missing)))

if __name__ == "__main__":
    repo, g, shards, shared = (Path(x).resolve() for x in sys.argv[1:5])
    prepare(repo, g, shards, shared, sys.argv[5], Path(sys.argv[6]).resolve())
