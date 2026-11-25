#!/usr/bin/env python3
"""Reconstruct four accepted raw139 F1 sibling source modules for one shared Lean build."""
from __future__ import annotations

import base64
import hashlib
import io
import shutil
import subprocess
import sys
import tarfile
from pathlib import Path, PurePosixPath

ROOT = Path.cwd()
TMP = ROOT / ".tmp"


def archive_bytes(path: Path, expected_sha256: str) -> bytes:
    data = base64.b64decode(path.read_text().strip())
    actual = hashlib.sha256(data).hexdigest()
    if actual != expected_sha256:
        raise SystemExit(f"archive hash mismatch for {path}: {actual} != {expected_sha256}")
    return data


def extract_archive(data: bytes, dest: Path, members: set[str] | None = None) -> None:
    dest.mkdir(parents=True, exist_ok=True)
    extracted: set[str] = set()
    with tarfile.open(fileobj=io.BytesIO(data), mode="r:xz") as archive:
        for member in archive.getmembers():
            if not member.isfile():
                continue
            rel = PurePosixPath(member.name)
            if rel.is_absolute() or ".." in rel.parts:
                raise SystemExit(f"unsafe archive path: {member.name}")
            if members is not None and member.name not in members:
                continue
            source = archive.extractfile(member)
            if source is None:
                raise SystemExit(f"cannot read archive member: {member.name}")
            target = dest.joinpath(*rel.parts)
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(source.read())
            extracted.add(member.name)
    if members is not None:
        missing = members - extracted
        if missing:
            raise SystemExit(f"missing archive members in {dest}: {sorted(missing)}")


def run_generators(work: Path, *scripts: str) -> None:
    for script in scripts:
        if not (work / script).is_file():
            raise SystemExit(f"missing generator {script} in {work}")
        subprocess.run([sys.executable, script], cwd=work, check=True)


def check_files(work: Path, expected: dict[str, str]) -> None:
    for name, digest in expected.items():
        path = work / name
        if not path.is_file():
            raise SystemExit(f"missing generated source: {path}")
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != digest:
            raise SystemExit(f"generated source hash mismatch for {path}: {actual} != {digest}")


def merge_lean_sources(source: Path, destination: Path) -> int:
    destination.mkdir(parents=True, exist_ok=True)
    count = 0
    for path in source.rglob("*.lean"):
        rel = path.relative_to(source)
        target = destination / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists():
            old = hashlib.sha256(target.read_bytes()).hexdigest()
            new = hashlib.sha256(path.read_bytes()).hexdigest()
            if old != new:
                raise SystemExit(f"conflicting Lean source {rel}: {old} != {new}")
        else:
            shutil.copy2(path, target)
        count += 1
    return count


def main() -> None:
    a41 = ROOT / "im-results/agent41-raw139-f1-zeroLF"
    a14 = ROOT / "im-results"
    a14_common = a14 / "agent14-raw139-f1-oneRF/source.tar.xz.b64"
    common = archive_bytes(a14_common, "8b87050c5b7088d8e27159fcea9501a4f66999e4382c92e3e039696643d0492e")

    # Agent41's 0RB proof reuses the exact symbolic-gap interpreter from 0LF.
    zero_rb_work = TMP / "a41-f1-zeroRB/imports"
    prior = archive_bytes(a41 / "Agent41F1ZeroLFProofs.tar.xz.b64",
                          "15b951ad6c8c9b988e2a2f44a39671a938b4c2b0fbc264c72a4afe1a972b62bb")
    extract_archive(prior, zero_rb_work, {"Agent41SymSweep.lean"})
    zero_rb = archive_bytes(a41 / "Agent41F1ZeroRBProofs.tar.xz.b64",
                            "dedb53f31b5493b240d1b1d89fa1c409f0ced92ef1d6486c5415e6d98fe75aba")
    extract_archive(zero_rb, zero_rb_work)
    if not (zero_rb_work / "Agent41F1ZeroRBCover.lean").is_file():
        raise SystemExit("0RB archive did not reconstruct Agent41F1ZeroRBCover.lean")
    merge_lean_sources(zero_rb_work, TMP / "a41-f1-zeroLF/imports")

    # Generate each Agent14 sibling in isolation, then merge the Lean sources
    # into one source root so the shared WordShift module has one identity.
    common_members = {"WordShift.lean", "autopump.py", "scan.py"}
    work_zero_la = TMP / "a14-f1-zeroLA/imports"
    extract_archive(common, work_zero_la,
                    common_members | {"emitproof.py"})
    delta_zero_la = archive_bytes(a14 / "agent14-raw139-f1-zeroLA/source-delta.tar.xz.b64",
                                  "c7a9fbcaac3a8bfb87db80c5fd9e33065ecd1c8c85e939c00141cfd802f6bb4f")
    extract_archive(delta_zero_la, work_zero_la)
    for pattern in ("pump-*.json",):
        for path in work_zero_la.glob(pattern):
            path.unlink()
    run_generators(work_zero_la, "replay.py", "gencarry.py", "chunk.py")
    check_files(work_zero_la, {
        "WordShift.lean": "7f93ab9ad25543375c7c30e23b8fac780b77a716b00347f6c657719771f1cadf",
        "LAOuter.lean": "b11a441fccca78e0cba65657a39bd36e581f998be97314e221271135b2c39e37",
        "LACarry.lean": "1f96d23975885ab07e7d78692ab818333ec207c9eb0a335e953ef70749ff7b82",
        "Agent14OneLAHard.lean": "465b2dae949b5f4e92137263365fc61f988b278e97314b7caaa58343490fbdef",
        "Agent14OneLACover.lean": "b8b2b30f870210b1b153c0207f660b1c25811f069bbecf42e36d0d12cbe9e16e",
    })

    work_one_lb = TMP / "a14-f1-oneLB/imports"
    extract_archive(common, work_one_lb, common_members)
    delta_one_lb = archive_bytes(a14 / "agent14-raw139-f1-oneLB/source-delta.tar.xz.b64",
                                 "b2d32c975b385cf2ba441ff67ae45aea2c2ff7af64c6be61da84fbc2d5f468b7")
    extract_archive(delta_one_lb, work_one_lb)
    for path in work_one_lb.glob("pump-*.json"):
        path.unlink()
    run_generators(work_one_lb, "replay.py", "chunk.py")
    check_files(work_one_lb, {
        "WordShift.lean": "7f93ab9ad25543375c7c30e23b8fac780b77a716b00347f6c657719771f1cadf",
        "LBOuter.lean": "359a5ec5e3705158d8d78b3225c5304f4bf3599297c9834dc723b70fd578c266",
        "LBCarry.lean": "0856337e7594a41d5435bd332ade5c9ce38566e5b07ff1565619cb5d9edc3aee",
        "Agent14OneLBHard.lean": "b5ac0ec59b778eb587be9ad9568c585aa842dabbd0e7b09845446045cf715042",
        "Agent14OneLBCover.lean": "a31688ac0ccccaaa492f806cf2bb9dad0a52ec8b56ceaf99b21d3d298d78a42a",
    })

    work_one_rd = TMP / "a14-f1-oneRD/imports"
    extract_archive(common, work_one_rd, common_members)
    delta_one_rd = archive_bytes(a14 / "agent14-raw139-f1-oneRD/source-delta.tar.xz.b64",
                                 "d50cae0d3410b0f52dcbf84242b706b26ff7f9b99bf6fc57a4af85fa8868115f")
    extract_archive(delta_one_rd, work_one_rd)
    # The 1RD emitter is shared with the already reconstructed 1LB source.
    extract_archive(delta_one_lb, work_one_rd, {"emitproof.py"})
    for path in work_one_rd.glob("pump-*.json"):
        path.unlink()
    run_generators(work_one_rd, "replay.py", "chunk.py")
    check_files(work_one_rd, {
        "WordShift.lean": "7f93ab9ad25543375c7c30e23b8fac780b77a716b00347f6c657719771f1cadf",
        "Agent14OneRDHard.lean": "545101fe2a7a74cd294b9e894ea21cb3fb4af433eb17c15b657c9111a9dae81f",
        "Agent14OneRDCover.lean": "9e10874098f0674b3c4959db593bd80ee08e02db8a42317ff969b347dc8a51df",
    })

    batch_root = TMP / "a14-f1-batch/imports"
    total = 0
    for work in (work_zero_la, work_one_lb, work_one_rd):
        total += merge_lean_sources(work, batch_root)
    for required in ("Agent14OneLACover.lean", "Agent14OneLBCover.lean", "Agent14OneRDCover.lean"):
        if not (batch_root / required).is_file():
            raise SystemExit(f"missing merged source {required}")
    print(f"reconstructed Agent41 0RB and Agent14 0LA/1LB/1RD; merged {total} Lean sources")


if __name__ == "__main__":
    main()
