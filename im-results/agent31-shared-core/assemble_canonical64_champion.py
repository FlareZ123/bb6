"""Source-audit the exact champion score/witness against the accepted Canonical64 base."""
import argparse
import base64
import hashlib
import io
import json
import lzma
import os
from pathlib import Path
import re
import subprocess
import sys
import tarfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent
sys.path.insert(0, str(HERE))
import assemble_canonical63 as a63

a68 = a63.a68
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def sha(path):
    h = hashlib.sha256()
    with Path(path).open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def named_axioms(log, required):
    profiles = {}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", log):
        profiles[name] = {x.strip() for x in axioms.split(",") if x.strip()}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
        profiles[name] = set()
    result = {}
    for name in required:
        assert name in profiles, f"missing axiom profile: {name}"
        bad = profiles[name] - ALLOWED
        assert not bad, (name, bad)
        result[name] = sorted(profiles[name])
    return result


def reconstruct_champion_imports(work):
    imports = work / "imports"
    imports.mkdir(parents=True)
    terminal = ROOT / "im-results/agent42-champion-terminal"
    archive_data = base64.b64decode((terminal / "TerminalProofs.tar.xz.b64").read_text())
    with tarfile.open(fileobj=io.BytesIO(archive_data), mode="r:xz") as archive:
        member = next(
            m for m in archive.getmembers()
            if Path(m.name).name == "TerminalFinish.lean"
        )
        (imports / "TerminalFinish.lean").write_bytes(archive.extractfile(member).read())
    (imports / "TerminalLeft.lean").write_bytes(
        lzma.decompress(base64.b64decode(
            (terminal / "TerminalLeftExact.lean.xz.b64").read_text()
        ))
    )
    coverage = ROOT / "im-results/agent13-coverage/BB6Coverage.lean.xz.b64"
    (imports / "BB6Coverage.lean").write_bytes(
        lzma.decompress(base64.b64decode(coverage.read_text()))
    )
    expected = {
        "BB6Coverage.lean": "fbe453c5c170029885ba328bfdd9262600f918a8ce2371c60ecbb843897fd6bd",
        "TerminalFinish.lean": "12329036c66c3846f9261167b8f9aebd1778d9b6ea6044309956c2fa0b3e49b7",
        "TerminalLeft.lean": "1bce2075fc4e0cd7d740fb71b3796088b190ddb6766e04640d992dadd1b650ff",
    }
    for name, digest in expected.items():
        actual = sha(imports / name)
        assert actual == digest, (name, actual, digest)
    return imports


def compile_champion_closure(work, imports):
    build = work / "champion-build"
    manifest = work / "champion-closure-manifest.json"
    log_path = work / "champion-closure.log"
    cmd = [
        sys.executable, str(ROOT / "tools/lean_compile_closure.py"),
        "im-results/agent48-counted-inc0/TM63RawUpperInterface.lean",
        "im-results/agent38-champion-threshold/ChampionScoreLowerBound.lean",
        "--workdir", str(build),
        "--jobs", "8",
        "--source-root", str(imports),
        "--manifest", str(manifest),
        "--label", "canonical64-exact-champion-score-consumer",
        "--provenance-input", "im-results/agent48-counted-inc0/TM63RawUpperInterface.lean",
        "--provenance-input", "im-results/agent38-champion-threshold/ChampionScoreLowerBound.lean",
        "--provenance-input", "im-results/agent24-champion-time/CostRecurrence.lean",
        "--provenance-input", "im-results/agent42-champion-terminal/TerminalProofs.tar.xz.b64",
        "--provenance-input", "im-results/agent42-champion-terminal/TerminalLeftExact.lean.xz.b64",
        "--provenance-input", "im-results/agent13-coverage/BB6Coverage.lean.xz.b64",
        "--override", "TerminalBridge=im-results/agent42-champion-terminal/TerminalBridge.lean",
        "--override", "OuterLCIncPrelude=im-results/agent8-counted-reset/OuterLCIncPrelude.lean",
        "--override", "M0OddResidueSeven=im-results/agent41-m0-n16r7/M0OddResidueSeven.lean",
        "--override", "M0EvenEightValuationEncoding=im-results/agent48-counted-inc0/M0EvenEightValuationEncoding.lean",
        "--override", "M2EvenResidueTwo=im-results/agent42-champion-terminal/M2EvenResidueTwo.lean",
    ]
    with log_path.open("w") as stream:
        try:
            subprocess.run(cmd, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT, check=True, text=True)
        except subprocess.CalledProcessError:
            lines = log_path.read_text().splitlines()
            print("=== champion source-closure failure log (last 180 lines) ===", file=sys.stderr, flush=True)
            print("\n".join(lines[-180:]), file=sys.stderr, flush=True)
            raise
    print(log_path.read_text(), flush=True)
    return build, log_path, manifest


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--work", type=Path, required=True)
    args = ap.parse_args()
    work = args.work.resolve()
    work.mkdir(parents=True, exist_ok=False)

    version = subprocess.check_output(["lean", "--version"], text=True).strip()
    assert "4.36.0-rc2" in version, version
    parts = a63.download_canonical64_parts(work)

    imports = reconstruct_champion_imports(work)
    champion_build, champion_log_path, champion_manifest = compile_champion_closure(work, imports)
    champion_log = champion_log_path.read_text()
    champion_profiles = named_axioms(champion_log, [
        "BB6Coverage.Agent48DirectRoot.champion_raw_halts_exact",
        "BB6Coverage.Agent48DirectRoot.champion_weighted_bound",
        "BB6.Agent38ChampionThreshold.first_section_cost_decomposition",
        "BB6.Agent38ChampionThreshold.first_increment_ge_pow63",
        "BB6.Agent38ChampionThreshold.first_increment_le_first_section",
        "BB6.Agent38ChampionThreshold.first_section_cost_le_champion_score",
        "BB6.Agent38ChampionThreshold.champion_score_ge_pow63",
        "BB6.Agent38ChampionThreshold.champion_score_ge_6766859",
    ])

    linked = work / "linked"
    families = a63.canonical64_families(parts) + [
        ("champion", [champion_build], ["TM63RawUpperInterface", "ChampionScoreLowerBound"])
    ]
    a68.link_reachable(
        [parts["canonical65"], parts["raw120"], [champion_build]],
        work,
        linked,
        families=families,
    )
    env = dict(os.environ, LEAN_PATH=str(linked))
    canonical64_output, canonical64_log, canonical64_axioms = a63.compile_canonical64(
        linked, env, work
    )

    source = HERE / "Canonical64ChampionConsumer.lean"
    output = linked / "Canonical64ChampionConsumer.olean"
    consumer_log = a68.compile_module(source, output, env, work / "consumer.log")
    if re.search(r"sorryAx|native_decide", consumer_log):
        raise AssertionError("forbidden proof mechanism in Canonical64 champion consumer")
    consumer_profiles = named_axioms(consumer_log, [
        "BB6Coverage.Agent48DirectRoot.champion_raw_witness",
        "BB6.Agent38ChampionThreshold.champion_score_ge_6766859",
        "BB6.Agent31Canonical64Champion.exact_at_champion_score",
    ])

    compiler = Path(subprocess.check_output(["lean", "--print-prefix"], text=True).strip()) / "bin" / "lean"
    report = {
        "status": "source-audited conditional exact-score consumer; not an exact BB(6) decision",
        "theorem": "BB6.Agent31Canonical64Champion.exact_at_champion_score",
        "score": "proposedTM63Moves + 7",
        "hypotheses": "Cover (WeightedBound (proposedTM63Moves + 7)) for each of the 64 retained Canonical64 representatives",
        "base_residual_count": 64,
        "remaining_cover_count": 64,
        "champion_lower_bound": "6766859 <= proposedTM63Moves + 7",
        "canonical65_run_id": a63.CANONICAL65_RUN,
        "canonical65_artifact_id": a63.CANONICAL65_ARTIFACT,
        "raw120_run_id": a63.RAW120_RUN,
        "raw120_artifact_id": a63.RAW120_ARTIFACT,
        "canonical64_run_id": a63.CANONICAL64_RUN,
        "canonical64_artifact_id": a63.CANONICAL64_ARTIFACT,
        "canonical64_source_revision": a63.CANONICAL64_REVISION,
        "canonical64_source_blob_sha": a63.CANONICAL64_SOURCE_BLOB_SHA,
        "canonical64_olean_sha256": sha(canonical64_output),
        "canonical64_axioms": canonical64_axioms,
        "champion_source_profiles": champion_profiles,
        "consumer_axioms": consumer_profiles,
        "source_revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "lean_version": version,
        "compiler_sha256": sha(compiler),
        "champion_closure_manifest_sha256": sha(champion_manifest),
        "champion_consumer_source_sha256": sha(source),
        "consumer_olean_sha256": sha(output),
        "reachable_link_audit_sha256": sha(work / "reachable-link-audit.json"),
    }
    (work / "canonical64-score-consumer.json").write_text(
        json.dumps(report, indent=2, sort_keys=True) + "\n"
    )
    print(json.dumps(report, indent=2, sort_keys=True), flush=True)
    print("Canonical64 exact champion score/witness consumer passed the source and axiom gates.", flush=True)


if __name__ == "__main__":
    main()
