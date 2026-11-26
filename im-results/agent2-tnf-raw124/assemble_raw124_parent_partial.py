"""Source-audit the exact Raw124 singleton residual parent cut.

Downloads only the 22 accepted branch source-audit artifacts, verifies their
run/artifact/manifest claims and Lean identity, links the reachable imported
kernel objects with duplicate-declaration checks, then compiles the Raw124
partial, nested, and singleton-cut theorems. The final result is conditional
only on F1=0LF/F0=1RC.
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
         size=84555050, root="Raw124New1LAComplete", theorem="BB6.Agent2Raw124New1LA.bound_all", branch="1LA", bound=6230),
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
    parser.add_argument("--rc-run", type=int, help="Successful final-cylinder audit run; enables complete parent assembly")
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

    # The accepted nested frontier contracts the entire F1=0LF obligation
    # to its exact F0=1RC residual. Its artifact includes a complete closure.
    frontier_run = 45883981997
    frontier_aid = 15148163947
    frontier_sha = "43ff61e9d9e64e4bc8a71f2c8dd9f748a98c3b01be6d0c3dbadcc533b54aa343"
    frontier_info = a68.api_json(f"repos/{a68.REPO}/actions/runs/{frontier_run}")
    assert frontier_info["conclusion"] == "success"
    frontier_dirs = a68.download((frontier_aid, frontier_run, frontier_sha), work)
    frontier_dirs = [p for p in frontier_dirs if (p / "Raw124ZeroLFParentFrontier.olean").is_file()]
    assert len(frontier_dirs) == 1
    frontier_manifest = work / "metadata" / str(frontier_aid) / "frontier.manifest.json"
    fm = json.loads(frontier_manifest.read_text())
    assert fm["claim"]["theorem"] == "BB6.Agent2Raw124ZeroLFParentFrontier.parent_cut"
    assert fm["claim"]["parent_table"] == "1RB---_1RC---_0RD---_1LD1RE_---1LF_0LF"
    assert fm["proof_source_revision"] == frontier_info["head_sha"]
    assert fm["lean_binary"]["sha256"] == compiler_sha
    families.append(("0LF-frontier", frontier_dirs, ["Raw124ZeroLFParentFrontier"]))

    # The successful split sparse-FAR repair closes 0RE, including all
    # 24 ordinary F0 children and the first-query halt. Its self-contained
    # proof closure is pinned to the successful assembler job.
    re_run = 45884922679
    re_aid = 15149067775
    re_sha = "f89ca10db12662221fb37728d7c266d8bc2fdb54911085faebffa689ea2fbcbe"
    re_info = a68.api_json(f"repos/{a68.REPO}/actions/runs/{re_run}")
    assert re_info["conclusion"] == "success"
    assert re_info["head_sha"] == "09d6f56a73dc2183c840f92febf7d628d338ec01"
    re_dirs = a68.download((re_aid, re_run, re_sha), work)
    re_manifest_dir = work / "metadata" / str(re_aid) / "a2-raw124-bundle" / "repair-source"
    re_manifest = json.loads((re_manifest_dir / "SPLIT_MANIFEST.json").read_text())
    assert re_manifest["branch"] == "0RE"
    assert re_manifest["source_commit"] == "3a265e67cdf4d5a75e41ffa48dade25e1dfade82"
    re_opt = json.loads((re_manifest_dir / "optimized" / "OPTIMIZED_MANIFEST.json").read_text())
    assert set(re_opt) == {"K04", "K05"}
    families.append(("0RE", re_dirs, ["Raw124B0REData"]))

    rc_metadata = None
    if args.rc_run:
        rc_run = a68.api_json(f"repos/{a68.REPO}/actions/runs/{args.rc_run}")
        assert rc_run["conclusion"] == "success"
        items = a68.api_json(f"repos/{a68.REPO}/actions/runs/{args.rc_run}/artifacts")["artifacts"]
        choices = [a for a in items if a["name"] == "raw124-0lf-1rc-complete" and not a["expired"]]
        assert len(choices) == 1
        item = choices[0]
        rc_sha = item["digest"].removeprefix("sha256:")
        rc_dirs = a68.download((item["id"], args.rc_run, rc_sha), work)
        rm = json.loads((work / "metadata" / str(item["id"]) / "manifest.json").read_text())
        assert rm["claim"] == {
            "theorem": "BB6.Agent12Raw124ZeroLF1RC.bound_all",
            "parent_table": "1RB---_1RC---_0RD---_1LD1RE_---1LF_1RC0LF",
            "weighted_bound": 108667,
        }
        assert rm["proof_source_revision"] == rc_run["head_sha"]
        assert rm["lean_version"] == lean_version
        assert len(rc_dirs) == 1
        assert {p.name: a68.sha(p) for p in rc_dirs[0].glob("*.olean")} == rm["objects"]
        a68.gate(rm["axiom_log"], ["BB6.Agent12Raw124ZeroLF1RC.bound_all"])
        families.append(("0LF/1RC", rc_dirs, ["Agent12RCFinal"]))
        rc_metadata = {"run_id": args.rc_run, "artifact_id": item["id"], "artifact_sha256": rc_sha, "claim": rm["claim"]}

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
    nested_source = HERE / "Raw124ParentNestedCut.lean"
    nested_output = work / "Raw124ParentNestedCut.olean"
    nested_log = work / "Raw124ParentNestedCut.log"
    compile_source(nested_source, nested_output, env, nested_log)
    nested_axioms = a68.gate(nested_log.read_text(), [
        "BB6.Agent2Raw124ParentNestedCut.p0LF_eq",
        "BB6.Agent2Raw124ParentNestedCut.cover_of_nested_two",
    ])

    singleton_source = HERE / "Raw124ParentSingletonCut.lean"
    singleton_output = work / "Raw124ParentSingletonCut.olean"
    singleton_log = work / "Raw124ParentSingletonCut.log"
    compile_source(singleton_source, singleton_output, env, singleton_log)
    singleton_axioms = a68.gate(singleton_log.read_text(), [
        "BB6.Agent2Raw124ParentSingletonCut.child0RE_eq",
        "BB6.Agent2Raw124ParentSingletonCut.cover0RE",
        "BB6.Agent2Raw124ParentSingletonCut.cover_of_last",
    ])

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
        "nested_frontier": {
            "run_id": frontier_run,
            "artifact_id": frontier_aid,
            "artifact_sha256": frontier_sha,
            "theorem": "BB6.Agent2Raw124ParentNestedCut.cover_of_nested_two",
            "hypotheses": ["F1=0RE", "F1=0LF,F0=1RC"],
            "axioms": nested_axioms,
            "source_sha256": a68.sha(nested_source),
            "object_sha256": a68.sha(nested_output),
        },
        "singleton_frontier": {
            "accepted_0RE_run": re_run,
            "accepted_0RE_artifact": re_aid,
            "accepted_0RE_artifact_sha256": re_sha,
            "accepted_0RE_theorem": "BB6.Agent2Raw124B0RE.bound_all",
            "accepted_0RE_weighted_bound": 2473,
            "theorem": "BB6.Agent2Raw124ParentSingletonCut.cover_of_last",
            "hypotheses": ["F1=0LF,F0=1RC"],
            "axioms": singleton_axioms,
            "source_sha256": a68.sha(singleton_source),
            "object_sha256": a68.sha(singleton_output),
        },
        "artifact_inputs": metadata,
        "linked_module_count": len(json.loads(link_manifest.read_text())["objects"]),
        "kernel_link_manifest_sha256": a68.sha(link_manifest),
        "compile_log_sha256": a68.sha(partial_log),
        "axiom_audit_log_sha256": a68.sha(work / "axiom-audit.log"),
    }
    if rc_metadata:
        complete_source = HERE / "Raw124ParentComplete.lean"
        complete_output = work / "Raw124ParentComplete.olean"
        complete_log = work / "Raw124ParentComplete.log"
        compile_source(complete_source, complete_output, env, complete_log)
        axioms = a68.gate(complete_log.read_text(), ["BB6.Agent2Raw124ParentComplete.parent_cover"])
        report["status"] = "source-accepted complete parent Cover"
        # The 22 direct F1 child artifacts are supplemented by the independently
        # accepted 0RE Cover and the 0LF -> 1RC nested Cover. Report the actual
        # 24-way parent coverage rather than leaving the two composed branches
        # misleadingly marked as uncovered.
        report["directly_source_accepted_first_level_branches"] = sorted(branches)
        report["covered_first_level_branches"] = sorted([*branches, "0RE", "0LF"])
        report["covered_first_level_count"] = 24
        report["uncovered_first_level_branches"] = []
        report["composed_branch_covers"] = {
            "0RE": {"theorem": "BB6.Agent2Raw124B0RE.bound_all", "weighted_bound": 2473,
                    "run_id": re_run, "artifact_id": re_aid},
            "0LF": {"theorem": "BB6.Agent2Raw124ParentComplete.parent_cover",
                    "final_child_theorem": "BB6.Agent12Raw124ZeroLF1RC.bound_all",
                    "weighted_bound": BOUND, "run_id": args.rc_run,
                    "artifact_id": rc_metadata["artifact_id"]},
        }
        report["final_cylinder"] = rc_metadata
        report["complete_parent"] = {
            "theorem": "BB6.Agent2Raw124ParentComplete.parent_cover",
            "weighted_bound": BOUND,
            "axioms": axioms,
            "source_sha256": a68.sha(complete_source),
            "object_sha256": a68.sha(complete_output),
        }
        # Include the full imported closure so the canonical consumer can use
        # this proof without repeating the independent parent branch audits.
        for p in [*linked.glob("*.olean"), *work.glob("*.olean")]:
            dest = output / p.name
            assert not dest.exists() or a68.sha(dest) == a68.sha(p), p.name
            shutil.copy2(p, dest)
        shutil.copy2(complete_log, output / "lean.log")
        manifest = {
            "claim": {"theorem": "BB6.Agent2Raw124ParentComplete.parent_cover",
                      "parent_table": report["parent_table"], "weighted_bound": BOUND},
            "proof_source_revision": report["source_revision"],
            "lean_version": lean_version,
            "lean_binary": {"sha256": compiler_sha},
            "objects": {p.name: a68.sha(p) for p in output.glob("*.olean")},
            "module_count": len(list(output.glob("*.olean"))),
            "axiom_log": complete_log.read_text(),
            "final_cylinder": rc_metadata,
        }
        (output / "manifest.json").write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n")

    report_path = output / "raw124-parent-22of24-partial-cut.json"
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    shutil.copy2(join_output, output / join_output.name)
    shutil.copy2(partial_output, output / partial_output.name)
    shutil.copy2(nested_output, output / nested_output.name)
    shutil.copy2(nested_log, output / nested_log.name)
    shutil.copy2(singleton_output, output / singleton_output.name)
    shutil.copy2(singleton_log, output / singleton_log.name)
    shutil.copy2(partial_log, output / partial_log.name)
    shutil.copy2(work / "axiom-audit.log", output / "axiom-audit.log")
    shutil.copy2(link_manifest, output / "kernel-link-manifest.json")
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)

if __name__ == "__main__":
    main()
