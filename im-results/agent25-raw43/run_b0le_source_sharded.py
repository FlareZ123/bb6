#!/usr/bin/env python3
"""Resumable original-source acceptance for heavy Raw43 BiDFA-backed children."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import zipfile

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
VARIANTS = {
    "b0le_e0la", "b0le_e1la", "b0le_e1lf", "b0le_e1ra",
    "b1la_a0la",
    "b1le_e0lf", "b1le_e0ra", "b1le_e1rb",
    "b1re_e11le",
}
DEEP = {
    "b0le_e1la": (
        46069234034,
        15232890025,
        "0ce54c834787a572269c89c55652c705785c9f01e8afa430d6692f231d7e1db0",
    ),
    "b0le_e1lf": (
        46069244516,
        15231499915,
        "d1e3377f1d3f2fc05b35cd198eed3c97171ae4fcfc3cd4fc6e948fd139250a46",
    ),
}
DEEP_HEAD = "6ab825d15c9e361e7867a7651b09755bfadb0e40"


def run(args: list[str], *, env: dict[str, str] | None = None) -> None:
    print("+", " ".join(args), flush=True)
    subprocess.run(args, cwd=REPO, env=env, check=True)


def capture(args: list[str]) -> str:
    print("+", " ".join(args), flush=True)
    return subprocess.check_output(args, cwd=REPO, text=True).strip()


def run_logged(args: list[str], log: Path, *, env: dict[str, str] | None = None) -> None:
    print("+", " ".join(args), flush=True)
    log.parent.mkdir(parents=True, exist_ok=True)
    with log.open("w", encoding="utf-8") as handle:
        proc = subprocess.Popen(
            args,
            cwd=REPO,
            env=env,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1,
        )
        assert proc.stdout is not None
        for line in proc.stdout:
            sys.stdout.write(line)
            handle.write(line)
        code = proc.wait()
    if code != 0:
        raise subprocess.CalledProcessError(code, args)


def prepare(variant: str) -> Path:
    if variant not in VARIANTS:
        raise ValueError(f"unsupported Raw43 source-shard variant: {variant}")
    run(["python", "im-results/agent13-coverage/unpack.py"])
    run(["python", "im-results/agent31-three-hole-tnf/generate_sweeps.py"])
    run(["python", "im-results/agent31-three-hole-tnf/generate_four_hole.py"])

    if variant in DEEP:
        run_id, artifact_id, expected_digest = DEEP[variant]
        meta = json.loads(capture([
            "gh", "api", f"repos/{os.environ['GITHUB_REPOSITORY']}/actions/runs/{run_id}"
        ]))
        if meta.get("conclusion") != "success" or meta.get("head_sha") != DEEP_HEAD:
            raise RuntimeError(f"deep proof source gate no longer matches pin for {variant}")
        archive = Path("/tmp") / f"{variant}-deep.zip"
        with archive.open("wb") as handle:
            subprocess.run(
                ["gh", "api", f"repos/{os.environ['GITHUB_REPOSITORY']}/actions/artifacts/{artifact_id}/zip"],
                cwd=REPO,
                stdout=handle,
                check=True,
            )
        digest = hashlib.sha256(archive.read_bytes()).hexdigest()
        if digest != expected_digest:
            raise RuntimeError(f"deep artifact digest mismatch for {variant}: {digest}")
        short = variant.removeprefix("b0le_e")
        member_name = f"spec_b0le_e{short}.json"
        with zipfile.ZipFile(archive) as zf:
            matches = [name for name in zf.namelist() if Path(name).name == member_name]
            if len(matches) != 1:
                raise RuntimeError(f"expected exactly one {member_name} in deep artifact: {matches}")
            deep_spec = Path("/tmp") / f"{variant}-deep.json"
            deep_spec.write_bytes(zf.read(matches[0]))
        run([
            "python",
            str(HERE / "prepare_b0le_bank.py"),
            short,
            str(deep_spec),
            str(HERE / f"spec_{variant}.json"),
        ])

    env = os.environ.copy()
    env["RAW43_BIDFA_BATCH"] = "6"
    run(["python", str(HERE / "generate.py"), variant], env=env)
    generated = HERE / f"generated_{variant}"
    if not generated.is_dir():
        raise RuntimeError(f"generator did not create {generated}")
    return generated


def batch_key(path: Path) -> int:
    match = re.search(r"BiDFABatch(\d+)\.lean$", path.name)
    if not match:
        raise ValueError(path)
    return int(match.group(1))


def shard(variant: str, index: int, count: int) -> None:
    if not 0 <= index < count:
        raise ValueError("shard index out of range")
    generated = prepare(variant)
    batches = sorted(generated.glob("Raw43*BiDFABatch*.lean"), key=batch_key)
    roots = [path for pos, path in enumerate(batches) if pos % count == index]
    if not roots:
        raise RuntimeError(f"no batch roots selected for shard {index}/{count}")
    work = Path(f"/tmp/a25-b0le-shard-{index}")
    log = work / "audit.log"
    run_logged([
        "python", "tools/lean_compile_closure.py",
        "--workdir", str(work),
        "--jobs", "1",
        "--override", "FastBiDFA=im-results/agent32-raw59/FastBiDFA.lean",
        "--manifest", str(work / "manifest.json"),
        "--label", f"raw43-{variant}-shard-{index}",
        "--artifact-name", f"raw43-b0le-shard-{index}",
        *[str(path.relative_to(REPO)) for path in roots],
    ], log)
    print(
        f"PASS shard {index}/{count}: {len(roots)} of {len(batches)} BiDFA batch modules",
        flush=True,
    )


def assemble(variant: str, count: int, shards_root: Path) -> None:
    generated = prepare(variant)
    revision = os.environ["GITHUB_SHA"]
    union = Path("/tmp/a25-b0le-shard-union")
    run([
        "python", str(HERE / "merge_b0le_source_shards.py"),
        "--shards-root", str(shards_root),
        "--generated-dir", str(generated),
        "--out", str(union),
        "--variant", variant,
        "--revision", revision,
        "--expected-shards", str(count),
    ])

    suffix = variant.upper()
    theorem = f"BB6.Agent25Raw43{suffix}.all43child"
    spec = HERE / f"spec_{variant}.json"
    bound = int(json.loads(spec.read_text(encoding="utf-8"))["bound"])
    work = Path("/tmp/a25-b0le-sharded-complete")
    log = Path("/tmp/a25-b0le-sharded.log")
    data = generated / f"Raw43{suffix}Data.lean"
    run_logged([
        "python", "tools/lean_compile_closure.py",
        "--workdir", str(work),
        "--jobs", "1",
        "--override", "FastBiDFA=im-results/agent32-raw59/FastBiDFA.lean",
        "--override", "M44Proof=im-results/agent38-raw43-pair/M44Proof.lean",
        "--override", "M44Data=im-results/agent38-raw43-pair/M44Data.lean",
        "--precompiled-manifest", str(union / "manifest.json"),
        "--precompiled-dir", str(union),
        "--manifest", str(work / "manifest.json"),
        "--label", f"raw43-{variant}-sharded",
        "--theorem", theorem,
        "--weighted-bound", str(bound),
        "--artifact-name", "raw43-extra-proof",
        "--provenance-input", str(spec.relative_to(REPO)),
        "--provenance-input", str((HERE / "generate.py").relative_to(REPO)),
        "--provenance-input", "im-results/agent2-tnf-raw124/fast_partition.cpp",
        str(data.relative_to(REPO)),
    ], log)
    run(["python", "im-results/agent4-raw109/audit_axioms.py", str(log), theorem])
    (work / "audit.log").write_bytes(log.read_bytes())
    (work / spec.name).write_bytes(spec.read_bytes())
    print(f"PASS source-accepted {variant}: {theorem}, weighted bound {bound}", flush=True)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    sub = ap.add_subparsers(dest="mode", required=True)

    p_shard = sub.add_parser("shard")
    p_shard.add_argument("--variant", required=True)
    p_shard.add_argument("--index", type=int, required=True)
    p_shard.add_argument("--count", type=int, default=4)

    p_assemble = sub.add_parser("assemble")
    p_assemble.add_argument("--variant", required=True)
    p_assemble.add_argument("--count", type=int, default=4)
    p_assemble.add_argument("--shards-root", type=Path, required=True)

    args = ap.parse_args()
    if args.mode == "shard":
        shard(args.variant, args.index, args.count)
    else:
        assemble(args.variant, args.count, args.shards_root)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
