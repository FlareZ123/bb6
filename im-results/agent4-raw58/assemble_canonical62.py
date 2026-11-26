"""Strictly integrate the accepted Raw112 and Raw58 Covers into Canonical64."""

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
SHARED = ROOT / "im-results/agent31-shared-core"
sys.path.insert(0, str(SHARED))

import assemble_canonical63 as a63
import assemble_canonical64_champion as a64c

a68 = a63.a68

RAW58_RUN = 45762057732
RAW58_REVISION = "91ebd1de7ac989c13541f3b30b422097cebc209a"
RAW58_ARTIFACT = 15090715339
RAW58_NAME = "raw58-parent-proof"
RAW58_DIGEST = "2231c274970b233002894c3fa097e3b81ad1484a3db0809c0148f8c03e26c477"


def download_raw58(work):
    run = a68.api_json(f"repos/{a68.REPO}/actions/runs/{RAW58_RUN}")
    assert run["conclusion"] == "success" and run["head_sha"] == RAW58_REVISION, run
    item = a68.api_json(f"repos/{a68.REPO}/actions/artifacts/{RAW58_ARTIFACT}")
    assert item["workflow_run"]["id"] == RAW58_RUN
    assert item["name"] == RAW58_NAME
    assert item["digest"] == "sha256:" + RAW58_DIGEST
    assert not item["expired"]
    dirs = a68.download((RAW58_ARTIFACT, RAW58_RUN, RAW58_DIGEST), work)

    candidates = []
    for path in (work / "metadata" / str(RAW58_ARTIFACT)).rglob("manifest.json"):
        try:
            manifest = json.loads(path.read_text())
        except (OSError, json.JSONDecodeError):
            continue
        modules = {entry.get("module") for entry in manifest.get("modules", [])}
        if {"Raw58Exact", "Raw58SharpComposition", "Raw58MoreCut3"} <= modules:
            candidates.append((path, manifest))
    assert len(candidates) == 1, [str(p) for p, _ in candidates]
    manifest_path, manifest = candidates[0]
    assert manifest["proof_source_revision"] == RAW58_REVISION
    assert "4.36.0-rc2" in manifest["lean_version"]
    prefix = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip())
    assert manifest["lean_binary"]["sha256"] == a68.sha(prefix / "bin" / "lean")
    metadata = {
        "run_id": RAW58_RUN,
        "source_revision": RAW58_REVISION,
        "artifact_id": RAW58_ARTIFACT,
        "artifact_name": RAW58_NAME,
        "artifact_digest": "sha256:" + RAW58_DIGEST,
        "manifest_sha256": a68.sha(manifest_path),
        "theorem": "BB6.Agent4Raw58Exact.coverRaw58",
        "parent_table": "1RB---_1RC---_0RD---_1LD1RE_---0RA_------",
        "weighted_bound": 3055746,
        "module_count": manifest["module_count"],
    }
    print(f"Verified Raw58 parent artifact {RAW58_ARTIFACT}.", flush=True)
    return metadata, dirs


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    ap.add_argument("--raw112-run-id", type=int, required=True,
                    help="successful run producing raw112-closed-parent-cover")
    args = ap.parse_args()

    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)
    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.36.0-rc2" in version, version

    parts = a63.download_canonical64_parts(work)
    raw112_meta, raw112_dirs = a68.download_named_artifact(
        args.raw112_run_id, "raw112-closed-parent-cover", work
    )
    raw58_meta, raw58_dirs = download_raw58(work)

    imports = a64c.reconstruct_champion_imports(work)
    champion_build, champion_log_path, champion_manifest = a64c.compile_champion_closure(
        work, imports
    )
    champion_log = champion_log_path.read_text()
    champion_profiles = a68.gate(champion_log, [
        "BB6Coverage.Agent48DirectRoot.champion_raw_halts_exact",
        "BB6Coverage.Agent48DirectRoot.champion_weighted_bound",
        "BB6.Agent38ChampionThreshold.champion_score_ge_6766859",
    ])

    linked = work / "linked"
    families = a63.canonical64_families(parts) + [
        ("raw112", raw112_dirs, ["Raw112ClosedCover"]),
        ("raw58", raw58_dirs, ["Raw58Exact"]),
        ("champion", [champion_build], ["TM63RawUpperInterface", "ChampionScoreLowerBound"]),
    ]
    groups = [parts["canonical65"], parts["raw120"], raw112_dirs, raw58_dirs, [champion_build]]
    a68.link_reachable(groups, work, linked, families=families)
    env = dict(os.environ, LEAN_PATH=str(linked))

    canonical64_output, canonical64_log, canonical64_axioms = a63.compile_canonical64(
        linked, env, work
    )

    champion_source = SHARED / "Canonical64ChampionConsumer.lean"
    champion_output = linked / "Canonical64ChampionConsumer.olean"
    champion_consumer_log = a68.compile_module(
        champion_source, champion_output, env, work / "canonical64-champion-consumer.log"
    )
    if re.search(r"sorryAx|native_decide", champion_consumer_log):
        raise AssertionError("forbidden proof mechanism in Canonical64 champion consumer")
    champion_consumer_axioms = a68.gate(champion_consumer_log, [
        "BB6Coverage.Agent48DirectRoot.champion_raw_witness",
        "BB6.Agent38ChampionThreshold.champion_score_ge_6766859",
        "BB6.Agent31Canonical64Champion.exact_at_champion_score",
    ])

    source = HERE / "Canonical62Raw112Raw58Integrated.lean"
    output = linked / "Canonical62Raw112Raw58Integrated.olean"
    log = a68.compile_module(source, output, env, work / "canonical62.log")
    if re.search(r"sorryAx|native_decide", log):
        raise AssertionError("forbidden proof mechanism in Canonical62 consumer")
    required = [
        "BB6.Agent4Canonical62Raw112Raw58.p112_root",
        "BB6.Agent4Canonical62Raw112Raw58.p58_root",
        "BB6.Agent4Canonical62Raw112Raw58.p112_count",
        "BB6.Agent4Canonical62Raw112Raw58.p58_count",
        "BB6.Agent4Canonical62Raw112Raw58.count62",
        "BB6.Agent4Canonical62Raw112Raw58.raw112_cover",
        "BB6.Agent4Canonical62Raw112Raw58.raw58_cover",
        "BB6.Agent4Canonical62Raw112Raw58.sound62_integrated",
        "BB6.Agent4Canonical62Raw112Raw58.exact_at_target62",
        "BB6.Agent4Canonical62Raw112Raw58.exact_at_champion_score",
    ]
    profiles = a68.gate(log, required)

    compiler = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip()) / "bin" / "lean"
    report = {
        "status": "source-audited conditional 62-residual exact-score interface; not an exact BB(6) decision",
        "theorem": "BB6.Agent4Canonical62Raw112Raw58.exact_at_champion_score",
        "score": "proposedTM63Moves + 7",
        "base_residual_count": 64,
        "removed_parent_count": 2,
        "residual_count": 62,
        "parents": {
            "raw112": raw112_meta,
            "raw58": raw58_meta,
        },
        "canonical64": {
            "run_id": a63.CANONICAL64_RUN,
            "artifact_id": a63.CANONICAL64_ARTIFACT,
            "source_revision": a63.CANONICAL64_REVISION,
            "artifact_digest": "sha256:" + a63.CANONICAL64_DIGEST,
            "recompiled_olean_sha256": a68.sha(canonical64_output),
            "axioms": canonical64_axioms,
        },
        "canonical65": {
            "run_id": a63.CANONICAL65_RUN,
            "artifact_id": a63.CANONICAL65_ARTIFACT,
            "source_revision": a63.CANONICAL65_REVISION,
        },
        "raw120": {
            "run_id": a63.RAW120_RUN,
            "artifact_id": a63.RAW120_ARTIFACT,
            "source_revision": a63.RAW120_REVISION,
        },
        "champion_source_profiles": champion_profiles,
        "champion_consumer_axioms": champion_consumer_axioms,
        "consumer_axioms": profiles,
        "remaining_obligations": (
            "a Cover at the attained score for each of the 62 retained quotient "
            "representatives; the champion score and raw attaining witness are fixed"
        ),
        "source_revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "lean_version": version,
        "compiler_sha256": a68.sha(compiler),
        "champion_closure_manifest_sha256": a68.sha(champion_manifest),
        "consumer_source_sha256": a68.sha(source),
        "consumer_olean_sha256": a68.sha(output),
        "reachable_link_audit_sha256": a68.sha(work / "reachable-link-audit.json"),
    }
    (work / "canonical62-integration.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)
    print("Raw112 and Raw58 consumed into Canonical64; the 62-residual source/axiom gate passed.", flush=True)


if __name__ == "__main__":
    main()
