#!/usr/bin/env python3
"""Rebuild the exact Agent14 raw139 1LD/1RF Lean sources without running a second full closure."""
from __future__ import annotations

import base64
import hashlib
import shutil
import subprocess
import sys
import tarfile
from pathlib import Path, PurePosixPath

ROOT = Path.cwd()
TMP = ROOT / ".tmp/a14-f1-ld-rf"
LD = ROOT / "im-results/agent14-raw139-f1-oneLD"
RF = ROOT / "im-results/agent14-raw139-f1-oneRF"


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def run(argv: list[str], cwd: Path) -> None:
    subprocess.run(argv, cwd=cwd, check=True)


def verify(root: Path, expected: dict[str, str]) -> None:
    for name, want in expected.items():
        path = root / name
        if not path.is_file():
            raise SystemExit(f"missing generated source: {path}")
        got = digest(path.read_bytes())
        if got != want:
            raise SystemExit(f"source hash mismatch for {path}: {got} != {want}")


def extract_safe(archive_path: Path, destination: Path) -> None:
    destination.mkdir(parents=True, exist_ok=True)
    with tarfile.open(archive_path, mode="r:xz") as archive:
        for member in archive.getmembers():
            if not member.isfile():
                continue
            rel = PurePosixPath(member.name)
            if rel.is_absolute() or ".." in rel.parts:
                raise SystemExit(f"unsafe archive member: {member.name}")
            source = archive.extractfile(member)
            if source is None:
                raise SystemExit(f"unreadable archive member: {member.name}")
            target = destination.joinpath(*rel.parts)
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(source.read())


def merge_sources(source: Path, destination: Path) -> int:
    count = 0
    for path in source.rglob("*.lean"):
        rel = path.relative_to(source)
        target = destination / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists():
            old, new = digest(target.read_bytes()), digest(path.read_bytes())
            if old != new:
                raise SystemExit(f"conflicting generated module {rel}: {old} != {new}")
        else:
            shutil.copy2(path, target)
        count += 1
    return count


def main() -> None:
    ld_stage = TMP / "ld/imports"
    rf_stage = TMP / "rf/imports"
    merged = TMP / "imports"
    for p in (ld_stage, rf_stage, merged):
        if p.exists():
            shutil.rmtree(p)
        p.mkdir(parents=True)

    for name in ("recipes.txt", "Agent14OneLDCarry.lean"):
        shutil.copy2(LD / name, ld_stage / name)
    run([sys.executable, str(LD / "replay.py")], ld_stage)
    run([sys.executable, str(LD / "package.py")], ld_stage)
    verify(ld_stage, {
        "Agent14OneLDCarry.lean": "24d2b82d1c9a11c33b28ab9e7fb460ce2b9ea05db919dd6840d4ebceb76bf34a",
        "Agent14OneLDHard.lean": "b436a77405c29314f7f75e9d773326591f7eeb8ad7098b6b854b93afa83818d0",
        "Agent14OneLDCover.lean": "c1e905c2103d30b39bac253c5015f5a51da87aa57c6c5c9acd35e677e022f225",
    })

    archive = base64.b64decode((RF / "source.tar.xz.b64").read_text().strip())
    if digest(archive) != "8b87050c5b7088d8e27159fcea9501a4f66999e4382c92e3e039696643d0492e":
        raise SystemExit("1RF source archive hash mismatch")
    archive_path = TMP / "oneRF-source.tar.xz"
    archive_path.write_bytes(archive)
    extract_safe(archive_path, rf_stage)
    run([sys.executable, "replay.py"], rf_stage)
    run([sys.executable, "chunk.py"], rf_stage)
    verify(rf_stage, {
        "WordShift.lean": "7f93ab9ad25543375c7c30e23b8fac780b77a716b00347f6c657719771f1cadf",
        "RunCarry.lean": "2cb41161279c8eaec09cc89030634f77c6da5d6ddacd590aedfa225a442c078b",
        "FastQuery.lean": "3bdf42ec78668cfa36707f3ca31bcafdc6a32ca1f918710fce414b9412037cc7",
        "Agent14OneRFHard.lean": "075d364b997245763ad33de079f3b9f34c44c993b112930432a50e4b10fc3bb3",
        "Agent14OneRFCover.lean": "b94cb7678d30cf3521b3e3eed19181019878101f50c901f675035d9031bf58a2",
    })

    wordshift_candidates = [
        ROOT / ".tmp/a14-f1-batch/imports/WordShift.lean",
        ROOT / ".tmp/a48-f1-oneLA/imports/WordShift.lean",
    ]
    core_wordshift = next((p for p in wordshift_candidates if p.is_file()), None)
    if core_wordshift is None:
        raise SystemExit("missing canonical precompiled WordShift source (Agent6 F1 batch or Agent48 artifact)")
    if digest(core_wordshift.read_bytes()) != "7f93ab9ad25543375c7c30e23b8fac780b77a716b00347f6c657719771f1cadf":
        raise SystemExit("core WordShift differs from the pinned 1RF WordShift")
    (rf_stage / "WordShift.lean").unlink()

    n = merge_sources(ld_stage, merged) + merge_sources(rf_stage, merged)
    for name in ("Agent14OneLDCover.lean", "Agent14OneRFCover.lean",
                 "Agent14OneLDHard.lean", "Agent14OneRFHard.lean"):
        if not (merged / name).is_file():
            raise SystemExit(f"missing merged source {name}")
    print(f"prepared {n} Lean sources; reused exact precompiled WordShift")


if __name__ == "__main__":
    main()
