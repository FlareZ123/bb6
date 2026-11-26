"""Source-audit the exact Raw124 22-of-24 first-level partial parent cut.

Downloads only the 22 accepted branch source-audit artifacts, verifies their
run/artifact/manifest claims and Lean identity, links the reachable imported
kernel objects with duplicate-declaration checks, then compiles the Raw124
partial-cut theorem. The result is conditional only on F1=0RE and F1=0LF.
"""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "im-results" / "agent31-shared-core"))
import assemble_canonical68 as a68

PREFIX = "1RB---_1RC---_0RD---_1LD1RE_---1LF_---"
BOUND = 4_136_175

# Each artifact is pinned by artifact ID, producer run, digest and exact claim.
# The one legacy matrix run may have failed overall, but every artifact below
# came from an individually successful source-audit job.
ARTIFACTS = [
    dict(label="0RA", run=45840496976, job=139980560426, aid=15130748003,
         name="raw124-legacy-0RA-source-audit", sha="0669f5eb88ab5c1b2ea4f9988f42654d03aac971b5a9bc51ce37f8b39d84c587",
         size=28521429, root="Raw124Z0RAData", theorem="BB6.Agent32Raw124Z0RA.bound_all", branch="0RA", bound=283),
    dict(label="0RF", run=45840496976, job=139980559902, aid=15126744914,
         name="raw124-legacy-0RF-source-audit", sha="21b0786d3ffb682f77a1fd0edeb8bc267e698414698adbedef157cef8058216f",
         size=8724149, root="Raw124Z0RFData", theorem="BB6.Agent32Raw124Z0RF.bound_all", branch="0RF", bound=71),
    dict(label="0LA", run=45839093000, job=None, aid=15127830252,
         name="raw124-0la-complete-source-audit", sha="022bede94c52b9e201a4a39888cb45d1511b1d771ce2f61fa2c9cd6e0b07ec8a",
         size=130452855, root="Raw124ZeroLAComplete", theorem="BB6.Agent32Raw124ZeroLAComplete.bound_all", branch="0LA", bound=5910),
    dict(label="0LB", run=45827503893, job=None, aid=15122105407,
         name="raw124-0lb-complete-source-audit", sha="e08cc30ac83d1efbe513095f469ec79763d7aa917d6f67d75e660b2b74f0238a",
         size=110171112, root="Raw124ZeroLBComplete", theorem="BB6.Agent2Raw124ZeroLBComplete.bound_all", branch="0LB", bound=4136175),
    dict(label="0LC", run=45841021688, job=None, aid=15128591873,
         name="raw124-legacy-0LC-source-audit", sha="0b791d691776e7499945afb6820847f8c36e1aeee6665319079bda3c5a24b032",
         size=21399405, root="Raw124Z0LCData", theorem="BB6.Agent32Raw124Z0LC.bound_all", branch="0LC", bound=145),
    dict(label="0LD", run=45840496976, job=139980560502, aid=15129710694,
         name="raw124-legacy-0LD-source-audit", sha="48947daf674f95712ac375f09387432a2f95537b698cdbb1af96a816f1c3a274",
         size=26283228, root="Raw124Z0LDData", theorem="BB6.Agent32Raw124Z0LD.bound_all", branch="0LD", bound=157),
    dict(label="0LE", run=45836460043, job=None, aid=15129435887,
         name="raw124-0le-complete-source-audit", sha="27115eb6b4217a350156b06be5c6c1710560051e81a6f0a89349f01d66c19e6f",
         size=113255012, root="Raw124New0LEComplete", theorem="BB6.Agent2Raw124New0LE.bound_all", branch="0LE", bound=3006),
    dict(label="0RB", run=45841021688, job=None, aid=15128037834,
         name="raw124-legacy-0RB-source-audit", sha="4b0ceb62158421cde932a099c9bffec4d87b4ee3c557a6f6743e4ee8d91930a7",
         size=26615259, root="Raw124Z0RBData", theorem="BB6.Agent32Raw124Z0RB.bound_all", branch="0RB", bound=272),
    dict(label="0RC", run=45840496976, job=139980560280, aid=15127807592,
         name="raw124-legacy-0RC-source-audit", sha="4e37a09c6970f56a09ae89bf59df47311cc6795e2ad266484d7ef055173a53fd",
         size=26259210, root="Raw124Z0RCData", theorem="BB6.Agent32Raw124Z0RC.bound_all", branch="0RC", bound=2759),
    dict(label="0RD", run=45840496976, job=139980560352, aid=15127941805,
         name="raw124-legacy-0RD-source-audit", sha="7d722693f0bd3e6e2a16a76b302b2fb7d82c7d63488700d697140a3ac34c37a5",
         size=13419948, root="Raw124Z0RDData", theorem="BB6.Agent32Raw124Z0RD.bound_all", branch="0RD", bound=267),
    dict(label="1LA", run=45837006401, job=None, aid=15128682403,
         name="raw124-1la-complete-source-audit", sha="5f65be089125c8130bcedf40ce9ba0c6ea48ddab82be682a9e729a0d4cdfda14",
         size=84555050, root="Raw124New1LA", theorem="BB6.Agent2Raw124New1LA.bound_all", branch="1LA", bound=6230),
    dict(label="1LB", run=45800254828, job=None, aid=15107525242,
         name="raw124-1lb-complete-source-audit", sha="f69a99e9718b36a07b94d906291570f3ef4c3b4653e87baa0fbb0724cc62505c",
         size=67632162, root="Raw124OneLBComplete", theorem="BB6.Agent2Raw124OneLBComplete.bound_all", branch="1LB", bound=3006),
    dict(label="1LC", run=45840496976, job=139980560448, aid=15128955411,
         name="raw124-legacy-1LC-source-audit", sha="2a6fb7296d770853c2ef71d5db9c3a4428d2d8af9630ab3e089acf98634fdff7",
         size=19078861, root="Raw124Z1LCData", theorem="BB6.Agent32Raw124Z1LC.bound_all", branch="1LC", bound=102),
    dict(label="trivial", run=45840496976, job=139980560212, aid=15132051672,
         name="raw124-legacy-trivial-source-audit", sha="7bfdb4b2d5b438d1698004847a630d3728ac40a3a5f31a3c10bc750da76bb57b",
         size=4300582, root="Raw124Trivial", theorem="BB6.Agent32Raw124Trivial.bound1LD", branch="1LD", bound=7,
         extra_branches=["1RE"]),
    dict(label="1LE", run=45840496976, job=139980560359, aid=15130088173,
         name="raw124-legacy-1LE-source-audit", sha="2cbdd250eb2fd81e0ddc39fd9bda35eea14db298a2c2fda8b85c8a0fd02b7a33",
         size=80561169, root="Raw124Z1LEData", theorem="BB6.Agent32Raw124Z1LE.bound_all", branch="1LE", bound=670),
    dict(label="1LF", run=45855224384, job=None, aid=15134859375,
         name="raw124-legacy-1LF-source-audit", sha="c8f36170937e1add82bdb53660a8c131ba390cb3b7f3da2291dfaf7dd75a80b7",
         size=34372362, root="Raw124Z1LFData", theorem="BB6.Agent32Raw124Z1LF.bound_all", branch="1LF", bound=290),
    dict(label="1RA", run=45840496976, job=139980560453, aid=15130536056,
         name="raw124-legacy-1RA-source-audit", sha="eb746e2f555e930663ed022eb2ca9786f5bf61b396ee124686df0cd0ecd0bbbd",
         size=32550944, root="Raw124Z1RAData", theorem="BB6.Agent32Raw124Z1RA.bound_all", branch="1RA", bound=1029),
    dict(label="1RB", run=45840496976, job=139980560344, aid=15130193900,
         name="raw124-legacy-1RB-source-audit", sha="49bec41ab272e759f3182ee3f6de1b4460f3c582c512b9e377d1db2e18508ef2",
         size=28606369, root="Raw124Z1RBData", theorem="BB6.Agent32Raw124Z1RB.bound_all", branch="1RB", bound=184),
    dict(label="1RC", run=45840496976, job=139980560355, aid=15129256141,
         name="raw124-legacy-1RC-source-audit", sha="0f717f1136983916fb8180d3065f36c2ffc3e391a1bc77af2a1b1a8ede9de92b",
         size=24899599, root="Raw124Z1RCData", theorem="BB6.Agent32Raw124Z1RC.bound_all", branch="1RC", bound=688),
    dict(label="1RD", run=45840496976, job=139980560372, aid=15128635425,
         name="raw124-legacy-1RD-source-audit", sha="96076db841374826a2f89cdadd37ffa2b566d517cd48b92c910aa011b453f69d",
         size=13083796, root="Raw124Z1RDData", theorem="BB6.Agent32Raw124Z1RD.bound_all", branch="1RD", bound=80),
    dict(label="1RF", run=45841021688, job=None, aid=15127612983,
         name="raw124-legacy-1RF-source-audit", sha="e06281463166c91a230473be2b743e8a2b399425737961d14c453dd5b43ffd7c",
         size=17575719, root="Raw124Z1RFData", theorem="BB6.Agent32Raw124Z1RF.bound_all", branch="1RF", bound=140),
]

def verify_and_download(spec, work, lean_version, compiler_sha):
    run = a68.api_json(f"repos/{a68.REPO}/actions/runs/{spec['run']}")
    if spec["run"] != 45840496976:
        assert run["conclusion"] == "success", (spec["label"], run.get("conclusion"))
    if spec.get("job"):
        job = a68.api_json(f"repos/{a68.REPO}/actions/jobs/{spec['job']}")
        assert job["run_id"] == spec["run"] and job["conclusion"] == "success", (
            spec["label"], job.get("run_id"), job.get("conclusion")
        )
    info = a68.api_json(f"repos/{a68.REPO}/actions/artifacts/{spec['aid']}")
    assert info["workflow_run"]["id"] == spec["run"], (spec["label"], info["workflow_run"])
    assert info["name"] == spec["name"], (spec["label"], info["name"])
    assert info["digest"] == "sha256:" + spec["sha"], (spec["label"], info["digest"])
    assert info["size_in_bytes"] == spec["size"], (spec["label"], info["size_in_bytes"])
    assert not info["expired"], (spec["label"], "artifact expired")
    dirs = a68.download((spec["aid"], spec["run"], spec["sha"]), work)
    candidates = list((work / "metadata" / str(spec["aid"])).rglob("manifest.json"))
    assert len(candidates) == 1, (spec["label"], [str(p) for p in candidates])
    manifest_path = candidates[0]
    manifest = json.loads(manifest_path.read_text())
    claim = manifest.get("claim") or {}
    assert claim.get("theorem") == spec["theorem"], (spec["label"], claim)
    assert claim.get("weighted_bound") == spec["bound"], (spec["label"], claim)
    if spec["label"] != "trivial":
        expected_table = PREFIX + spec["branch"]
        assert claim.get("parent_table") == expected_table, (spec["label"], claim)
    assert manifest["proof_source_revision"] == run["head_sha"], (
        spec["label"], manifest.get("proof_source_revision"), run["head_sha"]
    )
    assert "4.36.0-rc2" in manifest["lean_version"], (spec["label"], manifest["lean_version"])
    assert manifest["lean_binary"]["sha256"] == compiler_sha, (
        spec["label"], manifest["lean_binary"]["sha256"], compiler_sha
    )
    modules = {entry["module"] for entry in manifest["modules"]}
    assert spec["root"] in modules, (spec["label"], spec["root"], sorted(modules)[:20])
    print(f"Verified {spec['label']}: artifact {spec['aid']} from run {spec['run']} ({spec['root']})", flush=True)
    metadata = {
        "label": spec["label"], "branches": [spec["branch"], *spec.get("extra_branches", [])],
        "run_id": spec["run"], "source_revision": run["head_sha"],
        "artifact_id": spec["aid"], "artifact_name": info["name"],
        "artifact_sha256": spec["sha"], "artifact_size": spec["size"],
        "root_module": spec["root"], "theorem": spec["theorem"],
        "weighted_bound": spec["bound"], "manifest_sha256": a68.sha(manifest_path),
        "module_count": manifest["module_count"],
    }
    return dirs, metadata

def compile_source(source, output, env, log_path):
    result = subprocess.run(
        ["lean", "-o", str(output), str(source)], cwd=source.parent, env=env,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    log_path.write_text(result.stdout)
    print(result.stdout, end="", flush=True)
    result.check_returncode()

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--work", type=Path, required=True)
    args = parser.parse_args()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=True)
    output = work / "output"
    output.mkdir(exist_ok=True)

    lean_version = subprocess.check_output(["lean", "--version"], text=True).strip()
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    compiler_sha = a68.sha(prefix / "bin" / "lean")
    print(lean_version, flush=True)

    families = []
    metadata = []
    # Four concurrent artifact downloads bound network and disk pressure.
    with ThreadPoolExecutor(max_workers=4) as pool:
        futures = [pool.submit(verify_and_download, spec, work, lean_version, compiler_sha)
                   for spec in ARTIFACTS]
        for spec, future in zip(ARTIFACTS, futures):
            dirs, record = future.result()
            families.append((spec["label"], dirs, [spec["root"]]))
            metadata.append(record)

    branches = [b for item in metadata for b in item["branches"]]
    assert len(branches) == 22 and len(set(branches)) == 22, branches
    assert set(branches) == {
        "0RA","0RF","0LA","0LB","0LC","0LD","0LE","0RB","0RC","0RD",
        "1LA","1LB","1LC","1LD","1LE","1LF","1RA","1RB","1RC","1RD","1RE","1RF",
    }, branches
    assert max(item["weighted_bound"] for item in metadata) == BOUND

    linked = work / "linked"
    a68.link_reachable([], work, linked, families=families)
    link_manifest = linked / "kernel-link-manifest.json"

    env = os.environ.copy()
    env["LEAN_PATH"] = str(linked)
    join_source = ROOT / "im-results" / "agent32-raw124-0le" / "Raw124ParentJoin.lean"
    partial_source = HERE / "Raw124ParentPartialCut.lean"
    join_output = work / "Raw124ParentJoin.olean"
    partial_output = work / "Raw124ParentPartialCut.olean"
    compile_source(join_source, join_output, env, work / "Raw124ParentJoin.log")

    env["LEAN_PATH"] = str(work) + os.pathsep + str(linked)
    compile_source(partial_source, partial_output, env, work / "Raw124ParentPartialCut.log")
    partial_log = work / "Raw124ParentPartialCut.log"

    audit_script = ROOT / "im-results" / "agent4-raw109" / "audit_axioms.py"
    audit = subprocess.run(
        [sys.executable, str(audit_script), str(partial_log),
         "BB6.Agent2Raw124ParentPartialCut.covered_iff",
         "BB6.Agent2Raw124ParentPartialCut.cover_of_two"],
        cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
    )
    (work / "axiom-audit.log").write_text(audit.stdout)
    print(audit.stdout, end="", flush=True)
    audit.check_returncode()

    report = {
        "schema_version": 1,
        "status": "source-accepted conditional parent partial cut",
        "parent_table": "1RB---_1RC---_0RD---_1LD1RE_---1LF_------",
        "parent_weighted_bound": BOUND,
        "covered_first_level_branches": sorted(branches),
        "covered_first_level_count": len(branches),
        "uncovered_first_level_branches": ["0RE", "0LF"],
        "coverage_theorem": "BB6.Agent2Raw124ParentPartialCut.covered_iff",
        "conditional_parent_theorem": "BB6.Agent2Raw124ParentPartialCut.cover_of_two",
        "conditional_hypotheses": [
            "Cover (WeightedBound 4136175) for F1=0RE child",
            "Cover (WeightedBound 4136175) for F1=0LF child",
        ],
        "parent_join_source": str(join_source.relative_to(ROOT)),
        "partial_cut_source": str(partial_source.relative_to(ROOT)),
        "source_revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "lean_version": lean_version,
        "compiler_sha256": compiler_sha,
        "artifact_inputs": metadata,
        "linked_module_count": len(json.loads(link_manifest.read_text())["objects"]),
        "kernel_link_manifest_sha256": a68.sha(link_manifest),
        "compile_log_sha256": a68.sha(partial_log),
        "axiom_audit_log_sha256": a68.sha(work / "axiom-audit.log"),
    }
    report_path = output / "raw124-parent-22of24-partial-cut.json"
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    shutil.copy2(join_output, output / join_output.name)
    shutil.copy2(partial_output, output / partial_output.name)
    shutil.copy2(partial_log, output / partial_log.name)
    shutil.copy2(work / "axiom-audit.log", output / "axiom-audit.log")
    shutil.copy2(link_manifest, output / "kernel-link-manifest.json")
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)

if __name__ == "__main__":
    main()
