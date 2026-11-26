"""Audit five accepted E1 parent Covers into one direct Canonical64 reduction."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE))
import assemble_canonical63 as a63
import assemble_canonical64_champion as champion

a68 = a63.a68

PARENTS = [
    {
        "label": "raw58",
        "run_id": 45762057732,
        "revision": "91ebd1de7ac989c13541f3b30b422097cebc209a",
        "artifact_id": 15090715339,
        "artifact_name": "raw58-parent-proof",
        "digest": "2231c274970b233002894c3fa097e3b81ad1484a3db0809c0148f8c03e26c477",
        "root": "Raw58Exact",
        "theorem": "BB6.Agent4Raw58Exact.coverRaw58",
        "table": "1RB---_1RC---_0RD---_1LD1RE_---0RA_------",
        "bound": 3055746,
        "size": 257300992,
    },
    {
        "label": "raw59",
        "run_id": 45786187618,
        "revision": "a3afaf00d33e66212250c2ad99169b3b7e308363",
        "artifact_id": 15100876549,
        "artifact_name": "raw59-exact-certified",
        "digest": "3659fb6d4c7a9215a60418642bba0d0f23717b7444cf8852f09624418228ba69",
        "root": "Raw59Exact",
        "theorem": "BB6.Agent32Raw59Exact.exact_bound",
        "table": "1RB---_1RC---_0RD---_1LD1RE_---1LA_------",
        "bound": 4136171,
        "size": 816911124,
    },
    {
        "label": "raw108",
        "run_id": 45788380944,
        "revision": "e40934b3e1211b36fd617377f81c3658b23ebffd",
        "artifact_id": 15101731441,
        "artifact_name": "raw108-parent-proof",
        "digest": "77f7274d51f16697b29bcf2fbee1eb25ed3a2084b1e5134e36bd6e3759e6d21c",
        "root": "Raw108Closed",
        "theorem": "BB6.Agent10Raw108Closed.all_closed",
        "table": "1RB---_1RC---_0RD---_1LD1RE_---1LB_------",
        "bound": 4136180,
        "size": 774677658,
    },
    {
        "label": "raw115",
        "run_id": 45783903926,
        "revision": "9416c1292e50f47c06ae29ae4f6d2c80620e1755",
        "artifact_id": 15100255568,
        "artifact_name": "raw115-certified-root",
        "digest": "a4eea4fe3327e993aa402544af9991e03faa56e9f04b3609a41e7f9ee615b453",
        "root": "Raw115Data",
        "theorem": "BB6.Agent47Raw115.all_completions",
        "table": "1RB---_1RC---_0RD---_1LD1RE_---0RD_------",
        "bound": 7014,
        "size": 107302042,
    },
    {
        "label": "raw119",
        "run_id": 45755653372,
        "revision": "4a39c28ab1f00c86047a10c78840676ac7c23df1",
        "artifact_id": 15087741037,
        "artifact_name": "raw119-parent-proof",
        "digest": "b6997b8b530e59357bf8deabbc295f51f03b85567b99773b2fa91248ca3be235",
        "root": "Raw119Data",
        "theorem": "BB6.Agent10Raw119.all_completions",
        "table": "1RB---_1RC---_0RD---_1LD1RE_---0RE_------",
        "bound": 572,
        "size": 114409836,
    },
]

def download_parent(spec, work):
    run_info = a68.api_json(f"repos/{a68.REPO}/actions/runs/{spec['run_id']}")
    assert run_info["conclusion"] == "success", (spec["label"], run_info.get("conclusion"))
    assert run_info["head_sha"] == spec["revision"], (
        spec["label"], run_info["head_sha"], spec["revision"]
    )
    artifacts = a68.api_json(
        f"repos/{a68.REPO}/actions/runs/{spec['run_id']}/artifacts?per_page=100"
    )["artifacts"]
    matches = [item for item in artifacts if item["id"] == spec["artifact_id"]]
    assert len(matches) == 1, (spec["label"], matches)
    item = matches[0]
    assert item["name"] == spec["artifact_name"], (spec["label"], item["name"])
    assert item["digest"] == "sha256:" + spec["digest"], (
        spec["label"], item["digest"], spec["digest"]
    )
    assert item["size_in_bytes"] == spec["size"], (
        spec["label"], item["size_in_bytes"], spec["size"]
    )
    assert not item["expired"], (spec["label"], "artifact expired")
    assert item["workflow_run"]["head_sha"] == spec["revision"], (
        spec["label"], item["workflow_run"]
    )
    dirs = a68.download(
        (spec["artifact_id"], spec["run_id"], spec["digest"]), work
    )
    if spec["label"] == "raw59":
        manifests = list((work / "metadata" / str(spec["artifact_id"])).rglob("manifest.json"))
        assert len(manifests) == 1, [str(p) for p in manifests]
        manifest = json.loads(manifests[0].read_text())
        claim = manifest["claim"]
        assert claim["theorem"] == spec["theorem"], claim
        assert claim["parent_table"] == spec["table"], claim
        assert claim["weighted_bound"] == spec["bound"], claim
        assert manifest["proof_source_revision"] == spec["revision"], (
            manifest["proof_source_revision"], spec["revision"]
        )
        assert "4.36.0-rc2" in manifest["lean_version"], manifest["lean_version"]
        compiler = Path(
            subprocess.check_output(["lean", "--print-prefix"], text=True).strip()
        ) / "bin" / "lean"
        compiler_sha = a68.sha(compiler)
        assert manifest["lean_binary"]["sha256"] == compiler_sha, (
            "Raw59 artifact was built with a different Lean binary",
            manifest["lean_binary"]["sha256"], compiler_sha
        )
    metadata = {
        key: spec[key]
        for key in (
            "label", "run_id", "revision", "artifact_id", "artifact_name",
            "digest", "root", "theorem", "table", "bound", "size",
        )
    }
    print(
        f"Verified {spec['label']} parent artifact {spec['artifact_id']} "
        f"from successful run {spec['run_id']}.",
        flush=True,
    )
    return dirs, metadata


def verify_parent_artifact(spec):
    """Verify a source-accepted parent artifact without downloading its large OLean bundle."""
    run_info = a68.api_json(f"repos/{a68.REPO}/actions/runs/{spec['run_id']}")
    assert run_info["conclusion"] == "success", (spec["label"], run_info.get("conclusion"))
    assert run_info["head_sha"] == spec["revision"], (
        spec["label"], run_info["head_sha"], spec["revision"]
    )
    artifacts = a68.api_json(
        f"repos/{a68.REPO}/actions/runs/{spec['run_id']}/artifacts?per_page=100"
    )["artifacts"]
    matches = [item for item in artifacts if item["id"] == spec["artifact_id"]]
    assert len(matches) == 1, (spec["label"], matches)
    item = matches[0]
    assert item["name"] == spec["artifact_name"], (spec["label"], item["name"])
    assert item["digest"] == "sha256:" + spec["digest"], (
        spec["label"], item["digest"], spec["digest"]
    )
    assert item["size_in_bytes"] == spec["size"], (
        spec["label"], item["size_in_bytes"], spec["size"]
    )
    assert not item["expired"], (spec["label"], "artifact expired")
    assert item["workflow_run"]["head_sha"] == spec["revision"], (
        spec["label"], item["workflow_run"]
    )
    metadata = {
        key: spec[key]
        for key in (
            "label", "run_id", "revision", "artifact_id", "artifact_name",
            "digest", "root", "theorem", "table", "bound", "size",
        )
    }
    metadata["verified_without_download"] = True
    print(
        f"Verified {spec['label']} parent producer {spec['artifact_id']} "
        f"from successful run {spec['run_id']} (no stale OLean objects imported).",
        flush=True,
    )
    return metadata


def is_standard_module(module):
    return any(
        module == prefix or module.startswith(prefix + ".")
        for prefix in ("Lean", "Init", "Std", "Batteries", "Mathlib")
    )


def build_precompiled_manifest(base_linked, work):
    """Build a dependency-closed v1 manifest for the exact linked Canonical64 base."""
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    compiler = prefix / "bin" / "lean"
    compiler_sha = a68.sha(compiler)
    pins = [
        ("canonical65", a63.CANONICAL65_ARTIFACT, a63.CANONICAL65_REVISION),
        ("raw120", a63.RAW120_ARTIFACT, a63.RAW120_REVISION),
    ]
    source_entries = {}
    metadata_conflicts = set()
    source_revisions = []
    artifact_manifests = []
    for label, artifact_id, revision in pins:
        paths = list((work / "metadata" / str(artifact_id)).rglob("manifest.json"))
        assert len(paths) == 1, (label, artifact_id, [str(p) for p in paths])
        path = paths[0]
        manifest = json.loads(path.read_text())
        assert manifest.get("schema_version") == 1, (label, manifest.get("schema_version"))
        assert manifest.get("proof_source_revision") == revision, (
            label, manifest.get("proof_source_revision"), revision
        )
        assert manifest.get("lean_version") == version, (
            label, manifest.get("lean_version"), version
        )
        assert manifest.get("lean_binary", {}).get("sha256") == compiler_sha, (
            label, manifest.get("lean_binary"), compiler_sha
        )
        source_revisions.extend(
            manifest.get("source_revisions", [manifest["proof_source_revision"]])
        )
        artifact_manifests.append({
            "label": label,
            "artifact_id": artifact_id,
            "source_revision": revision,
            "manifest_sha256": a68.sha(path),
            "module_count": manifest["module_count"],
        })
        for entry in manifest["modules"]:
            module = entry["module"]
            previous = source_entries.get(module)
            if previous is None:
                source_entries[module] = dict(entry)
            elif (
                previous.get("source_sha256") != entry.get("source_sha256")
                or previous.get("project_imports") != entry.get("project_imports")
            ):
                metadata_conflicts.add(module)

    # If two accepted inputs describe the same module from different source
    # identities, do not choose one. Let the Raw59 source closure recompile it.
    for module in metadata_conflicts:
        source_entries.pop(module, None)

    candidates = {}
    missing_objects = []
    for module, original in source_entries.items():
        relative = Path(original["olean_path"])
        if relative.is_absolute() or ".." in relative.parts:
            raise ValueError(f"unsafe base object path for {module}: {relative}")
        object_path = base_linked / relative.name
        if not object_path.is_file():
            missing_objects.append(module)
            continue
        entry = dict(original)
        # link_reachable has already selected one object after exact kernel-data
        # comparison. Recompute identities below against that exact linked object.
        entry["olean_path"] = relative.name
        entry["olean_sha256"] = a68.sha(object_path)
        candidates[module] = entry

    # The precompiled checker can only reuse a module if every project import
    # is also represented. Drop incomplete tails; they will be compiled from source.
    changed = True
    while changed:
        changed = False
        for module, entry in list(candidates.items()):
            missing = [
                dep for dep in entry["project_imports"]
                if not is_standard_module(dep) and dep not in candidates
            ]
            if missing:
                candidates.pop(module)
                changed = True

    identities = {}
    visiting = set()

    def module_identity(module):
        if module in identities:
            return identities[module]
        if module in visiting:
            raise RuntimeError(f"cyclic manifest import graph at {module}")
        visiting.add(module)
        entry = candidates[module]
        dependencies = []
        for dep in sorted(entry["project_imports"]):
            dep_identity = (
                f"standard:{version}:{dep}"
                if is_standard_module(dep)
                else module_identity(dep)
            )
            dependencies.append({"module": dep, "identity": dep_identity})
        import_hash = hashlib.sha256(
            json.dumps(dependencies, sort_keys=True, separators=(",", ":")).encode()
        ).hexdigest()
        entry["import_closure_sha256"] = import_hash
        payload = {
            "module": module,
            "source_sha256": entry["source_sha256"],
            "project_imports": entry["project_imports"],
            "olean_sha256": entry["olean_sha256"],
            "import_closure_sha256": import_hash,
        }
        identity = hashlib.sha256(
            json.dumps(payload, sort_keys=True, separators=(",", ":")).encode()
        ).hexdigest()
        entry["module_identity_sha256"] = identity
        visiting.remove(module)
        identities[module] = identity
        return identity

    for module in sorted(candidates):
        module_identity(module)

    modules = [candidates[module] for module in sorted(candidates)]
    source_revisions = sorted(set(source_revisions))
    output = {
        "schema_version": 1,
        "label": "Canonical64 exact linked shared core",
        "proof_source_revision": "composite",
        "source_revisions": source_revisions,
        "lean_version": version,
        "lean_binary": {"path": str(compiler.resolve()), "sha256": compiler_sha},
        "claim": {
            "theorem": "Canonical64 shared dependency core",
            "parent_table": None,
            "weighted_bound": None,
        },
        "artifact_name": "canonical64-base-precompiled-manifest",
        "roots": [],
        "module_count": len(modules),
        "modules": modules,
        "provenance_inputs": [],
        "precompiled_core": {
            "source_artifacts": artifact_manifests,
            "metadata_conflicts_recompiled": sorted(metadata_conflicts),
            "missing_linked_objects": sorted(missing_objects),
            "module_count": len(modules),
        },
    }
    path = work / "canonical64-base-precompiled-manifest.json"
    path.write_text(json.dumps(output, indent=2, sort_keys=True) + "\n")
    info = {
        "manifest_sha256": a68.sha(path),
        "module_count": len(modules),
        "source_revisions": source_revisions,
        "metadata_conflicts_recompiled": sorted(metadata_conflicts),
        "missing_linked_objects": sorted(missing_objects),
    }
    print(
        f"Built Canonical64 precompiled manifest for {len(modules)} "
        "dependency-closed modules.",
        flush=True,
    )
    return path, info


def rebuild_raw59(base_linked, base_manifest, work):
    """Recompile the exact Raw59 proof closure against Canonical64's linked objects."""
    source = ROOT / "im-results" / "agent32-raw59" / "Raw59Exact.lean"
    assert source.is_file(), source
    output_dir = work / "raw59-rebuilt"
    manifest_path = work / "raw59-rebuilt-manifest.json"
    log_path = work / "raw59-rebuild.log"
    command = [
        sys.executable,
        str(ROOT / "tools" / "lean_compile_closure.py"),
        "--workdir", str(output_dir),
        "--jobs", "8",
        "--precompiled-dir", str(base_linked),
        "--precompiled-manifest", str(base_manifest),
        "--manifest", str(manifest_path),
        "--label", "Raw59Exact rebuilt against Canonical64 shared core",
        "--theorem", "BB6.Agent32Raw59Exact.cover",
        "--parent-table", "1RB---_1RC---_0RD---_1LD1RE_---1LA_------",
        "--weighted-bound", "4136171",
        "--artifact-name", "raw59-exact-rebuilt-on-canonical64",
        str(source),
    ]
    result = subprocess.run(
        command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    log_path.write_text(result.stdout)
    print(result.stdout, end="", flush=True)
    result.check_returncode()
    if re.search(r"sorryAx|native_decide", result.stdout):
        raise AssertionError("forbidden proof mechanism in rebuilt Raw59 closure")
    required = [
        "BB6.Agent32Raw59Exact.exact_bound",
        "BB6.Agent32Raw59Exact.retained_cover",
        "BB6.Agent32Raw59Exact.cover",
        "BB6.Agent32Raw59Exact.bound",
    ]
    profiles = a68.gate(result.stdout, required)
    manifest = json.loads(manifest_path.read_text())
    assert manifest["claim"]["theorem"] == "BB6.Agent32Raw59Exact.cover"
    assert manifest["claim"]["parent_table"] == "1RB---_1RC---_0RD---_1LD1RE_---1LA_------"
    assert manifest["claim"]["weighted_bound"] == 4136171
    assert "4.36.0-rc2" in manifest["lean_version"], manifest["lean_version"]
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    compiler_sha = a68.sha(prefix / "bin" / "lean")
    assert manifest["lean_binary"]["sha256"] == compiler_sha
    dirs = sorted({path.parent for path in output_dir.rglob("*.olean")}, key=str)
    assert dirs and any((directory / "Raw59Exact.olean").is_file() for directory in dirs)
    reused = (manifest.get("precompiled_core") or {}).get("reused_module_count", 0)
    metadata = {
        "root_source_sha256": a68.sha(source),
        "manifest_sha256": a68.sha(manifest_path),
        "module_count": manifest["module_count"],
        "reused_module_count": reused,
        "compiled_module_count": manifest["module_count"] - reused,
        "required_axioms": {name: profiles[name] for name in required},
    }
    print(
        f"Raw59 exact source closure rebuilt: {metadata['reused_module_count']} "
        f"reused, {metadata['compiled_module_count']} newly compiled modules.",
        flush=True,
    )
    return dirs, metadata

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    args = ap.parse_args()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)

    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.36.0-rc2" in version, version

    # Check the sharp Raw59 artifact's producer manifest and compiler identity
    # before paying for the large Canonical64 base download. This is the known
    # mixed-revision risk exposed by the first strict link attempt.
    raw59_spec = next(spec for spec in PARENTS if spec["label"] == "raw59")
    raw59_metadata = verify_parent_artifact(raw59_spec)
    parent_dirs = {}
    parent_metadata = [raw59_metadata]

    # First compile only the accepted Canonical64 base and exact table-membership
    # checks. Do not download the remaining parent bundle unless all five matches
    # are unique and the computed residual count is exactly 59.
    parts = a63.download_canonical64_parts(work)
    base_linked = work / "base-linked"
    a68.link_reachable(
        [parts["canonical65"], parts["raw120"]],
        work,
        base_linked,
        families=a63.canonical64_families(parts),
    )
    base_env = dict(os.environ, LEAN_PATH=str(base_linked))
    canonical64_output, canonical64_log, canonical64_axioms = a63.compile_canonical64(
        base_linked, base_env, work
    )

    membership_source = HERE / "Canonical59FiveParentMembership.lean"
    membership_output = base_linked / "Canonical59FiveParentMembership.olean"
    membership_log = a68.compile_module(
        membership_source,
        membership_output,
        base_env,
        work / "membership-preflight.log",
    )
    if re.search(r"sorryAx|native_decide", membership_log):
        raise AssertionError("forbidden proof mechanism in membership preflight")
    membership_required = [
        "BB6.Agent31Canonical59Membership." + name
        for name in [
            "p58_count64", "p59_count64", "p108_count64",
            "p115_count64", "p119_count64", "count59", "parents_root",
        ]
    ]
    membership_axioms = a68.gate(membership_log, membership_required)
    shutil.copy2(
        work / "reachable-link-audit.json",
        work / "base-reachable-link-audit.json",
    )
    print("Membership preflight passed: five unique exact parents, 59 retained.", flush=True)

    # Rebuild Raw59 from its checked-in source against the exact Canonical64
    # linked core. This avoids importing the two stale/conflicting width-two
    # OLean objects from the independent Raw59 artifact.
    base_precompiled_manifest, base_precompiled_info = build_precompiled_manifest(
        base_linked, work
    )
    raw59_dirs, raw59_rebuild_info = rebuild_raw59(
        base_linked, base_precompiled_manifest, work
    )
    parent_dirs["raw59"] = raw59_dirs
    raw59_metadata["rebuild"] = raw59_rebuild_info

    # Reuse only the five accepted original-source proof artifacts. Their
    # conservative bounds already lie below the canonical common score floor.
    for spec in PARENTS:
        if spec["label"] == "raw59":
            continue
        dirs, metadata = download_parent(spec, work)
        parent_dirs[spec["label"]] = dirs
        parent_metadata.append(metadata)
    parent_metadata.sort(key=lambda item: item["label"])

    # Reconstruct and compile the existing blank-start champion witness and
    # score lower-bound source closure; no new champion claim is introduced.
    imports = champion.reconstruct_champion_imports(work)
    champion_build, champion_log_path, champion_manifest = champion.compile_champion_closure(
        work, imports
    )
    champion_log = champion_log_path.read_text()
    champion_profiles = champion.named_axioms(champion_log, [
        "BB6Coverage.Agent48DirectRoot.champion_raw_halts_exact",
        "BB6Coverage.Agent48DirectRoot.champion_weighted_bound",
        "BB6.Agent38ChampionThreshold.sectionResult_firstCost_le",
        "BB6.Agent38ChampionThreshold.first_increment_ge_pow63",
        "BB6.Agent38ChampionThreshold.first_increment_le_first_section",
        "BB6.Agent38ChampionThreshold.sectionResult_cost_le_threeSectionMoves",
        "BB6.Agent38ChampionThreshold.first_section_cost_le_champion_score",
        "BB6.Agent38ChampionThreshold.champion_score_ge_pow63",
        "BB6.Agent38ChampionThreshold.champion_score_ge_6766859",
    ])

    linked = work / "linked"
    families = [
        (
            "canonical64",
            [base_linked],
            ["Canonical64Raw120Integrated", "Canonical59FiveParentMembership"],
        ),
        ("raw58", parent_dirs["raw58"], ["Raw58Exact"]),
        ("raw59", parent_dirs["raw59"], ["Raw59Exact"]),
        ("raw108", parent_dirs["raw108"], ["Raw108Closed"]),
        ("raw115", parent_dirs["raw115"], ["Raw115Data"]),
        ("raw119", parent_dirs["raw119"], ["Raw119Data"]),
        (
            "champion",
            [champion_build],
            ["TM63RawUpperInterface", "ChampionScoreLowerBound"],
        ),
    ]
    groups = [
        [base_linked],
        parent_dirs["raw58"],
        parent_dirs["raw59"],
        parent_dirs["raw108"],
        parent_dirs["raw115"],
        parent_dirs["raw119"],
        [champion_build],
    ]
    a68.link_reachable(groups, work, linked, families=families)

    source = HERE / "Canonical59FiveParentIntegrated.lean"
    output = linked / "Canonical59FiveParentIntegrated.olean"
    log = a68.compile_module(source, output, dict(os.environ, LEAN_PATH=str(linked)),
                             work / "canonical59-five-parent.log")
    if re.search(r"sorryAx|native_decide", log):
        raise AssertionError("forbidden proof mechanism in Canonical59 integration")
    required = [
        "BB6.Agent31Canonical59FiveParentIntegrated." + name
        for name in [
            "p58_source_eq", "p59_source_eq", "p108_source_eq",
            "p115_source_eq", "p119_source_eq", "p58_cover", "p59_cover",
            "p108_cover", "p115_cover", "p119_cover", "parents_pairwise_distinct", "parents_cover",
            "sound59_integrated", "exact_at_target", "exact_at_champion_score",
        ]
    ]
    required += [
        "BB6.Agent31Canonical59Membership.p58_count64",
        "BB6.Agent31Canonical59Membership.p59_count64",
        "BB6.Agent31Canonical59Membership.p108_count64",
        "BB6.Agent31Canonical59Membership.p115_count64",
        "BB6.Agent31Canonical59Membership.p119_count64",
        "BB6.Agent31Canonical59Membership.count59",
        "BB6.Agent31Canonical59Membership.parents_root",
        "BB6Coverage.Agent48DirectRoot.champion_raw_witness",
        "BB6.Agent38ChampionThreshold.champion_score_ge_6766859",
    ]
    profiles = a68.gate(log, required)

    compiler = Path(
        subprocess.check_output(["lean", "--print-prefix"], text=True).strip()
    ) / "bin" / "lean"
    report = {
        "status": "source-audited conditional 64-to-59 Canonical64 quotient reduction; not an exact BB(6) decision",
        "base_residual_count": 64,
        "consumed_parent_count": 5,
        "remaining_residual_count": 59,
        "common_weighted_floor": 6766859,
        "parent_artifacts": parent_metadata,
        "base_precompiled_manifest": base_precompiled_info,
        "raw59_rebuild": raw59_rebuild_info,
        "canonical65_run_id": a63.CANONICAL65_RUN,
        "canonical65_artifact_id": a63.CANONICAL65_ARTIFACT,
        "raw120_run_id": a63.RAW120_RUN,
        "raw120_artifact_id": a63.RAW120_ARTIFACT,
        "canonical64_run_id": a63.CANONICAL64_RUN,
        "canonical64_artifact_id": a63.CANONICAL64_ARTIFACT,
        "canonical64_source_revision": a63.CANONICAL64_REVISION,
        "canonical64_source_blob_sha": a63.CANONICAL64_SOURCE_BLOB_SHA,
        "canonical64_olean_sha256": a68.sha(canonical64_output),
        "canonical64_axioms": canonical64_axioms,
        "membership_preflight_axioms": membership_axioms,
        "membership_source_sha256": a68.sha(membership_source),
        "membership_olean_sha256": a68.sha(membership_output),
        "champion_source_profiles": champion_profiles,
        "integration_axioms": profiles,
        "integration_source_sha256": a68.sha(source),
        "integration_olean_sha256": a68.sha(output),
        "champion_closure_manifest_sha256": a68.sha(champion_manifest),
        "base_reachable_link_audit_sha256": a68.sha(work / "base-reachable-link-audit.json"),
        "reachable_link_audit_sha256": a68.sha(work / "reachable-link-audit.json"),
        "source_revision": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True
        ).strip(),
        "lean_version": version,
        "compiler_sha256": a68.sha(compiler),
        "conditional_exactness": {
            "theorem": "BB6.Agent31Canonical59FiveParentIntegrated.exact_at_champion_score",
            "score": "proposedTM63Moves + 7",
            "remaining_hypotheses": "Cover (WeightedBound (proposedTM63Moves + 7)) for each of the 59 retained representatives",
            "champion_lower_bound": "6766859 <= proposedTM63Moves + 7",
            "champion_witness": "BB6Coverage.Agent48DirectRoot.champion_raw_witness",
        },
    }
    report_path = work / "canonical59-five-parent-integration.json"
    report_path.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n")
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)
    print("Five accepted parent Covers composed in the exact Canonical64 core.", flush=True)

if __name__ == "__main__":
    main()
