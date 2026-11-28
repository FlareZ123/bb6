#!/usr/bin/env python3
"""Rejoin the exact successful Box12 branches of run 46112001673.

This deliberately does not regenerate any leaf or rebuild a successful shard.
The branch objects and their common sources are authenticated by fixed ZIP
hashes. The corrected final source is compiled with the same Lean version.
"""
from __future__ import annotations

import argparse
import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess
import tarfile
import zipfile

REPO = "FlareZ123/bb6"
ARTIFACTS = {
    "agent48-box6-deps.zip": (15158192432, "783b0daa58f8d42e6bc49bb29b6cb743b70acc6070337faa2686aa02379c55e9"),
    "box12-common.zip": (15250836225, "bf8ed92ad5dc8a2ef10c0c86df6602c82afcf027d2cf149ff960239ef5b33706"),
    "box12-e-0.zip": (15250867660, "aec98802a6f6e41275b3fdc0a61d64da51742719bc308119b55b8291674f8deb"),
    "box12-e-3.zip": (15250257532, "86ff5eacf74c0fb0a6ed1242f384f488f1630a72f129adb3b16615bc3708a0d8"),
    "box12-e-4.zip": (15250282903, "bf4105fe7d0cb4eb2351a805202080a8e59da59a2f248128835b57681d9db0e8"),
    "box12-e-12.zip": (15250413318, "25ad0490e61f35b4bec887293f0cbaf183096f94594964e327abfb69ca7ae2b4"),
    "box12-e-18.zip": (15250722050, "1374b17c8f39bd468f5f294c315fa5d4b66e6313319a7efc44f9a14e19f0b1b1"),
    "box12-e-20.zip": (15250644150, "76a04f1015746f0902287ebb19632c59f3b93bb926dab430b2372bd8dc50975b"),
    "box12-e-21.zip": (15250573871, "4cc7ae21e9f4978b659406bf8dc715e66141b0d886e20911ab97857d1c15a182"),
    "box12-e-22.zip": (15250078534, "e67448ab6a52e654bfee85df9cfd8c6539aa94c67a3f533e18f51decdefc08f8"),
    "box12-e-23.zip": (15250976840, "554fa1d20ecd6e8327f2b704f2b364e13d000d4930c14eb3d3ff16c6f55cf6c5"),
    "box12-e-24.zip": (15251158360, "3494f33acc4fc18fd2300add0c5f5236f4498b999c9780e917b55d9d1c69b003"),
}
THEOREMS = (
    "BB6.Agent48Box12.box12_weighted",
    "BB6.Agent48Raw10RefinedBox12.parentCover29",
    "BB6.Agent48Raw10RefinedBox12.parentCover27",
)
STANDARD = {"propext", "Classical.choice", "Quot.sound"}


def digest(path: Path) -> str:
    with path.open("rb") as src:
        return hashlib.file_digest(src, "sha256").hexdigest()


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--artifact-dir", type=Path, required=True)
    p.add_argument("--work", type=Path, required=True)
    p.add_argument("--out", type=Path, required=True)
    p.add_argument("--lean", default="lean")
    p.add_argument("--offline", action="store_true")
    args = p.parse_args()
    artifacts, work, out = (v.resolve() for v in (args.artifact_dir, args.work, args.out))
    work.mkdir(parents=True, exist_ok=False)
    out.mkdir(parents=True, exist_ok=True)
    artifacts.mkdir(parents=True, exist_ok=True)
    version = subprocess.check_output([args.lean, "--version"], text=True).strip()
    if "4.36.0-rc2" not in version or "b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a" not in version:
        raise RuntimeError(f"Wrong Lean toolchain: {version}")
    print(version, flush=True)

    for name, (artifact_id, expected) in ARTIFACTS.items():
        path = artifacts / name
        if not path.is_file():
            if args.offline:
                raise FileNotFoundError(path)
            temp = path.with_suffix(".part")
            with temp.open("wb") as dst:
                subprocess.run(["gh", "api", f"repos/{REPO}/actions/artifacts/{artifact_id}/zip"],
                               stdout=dst, check=True)
            if digest(temp) != expected:
                raise RuntimeError(f"Hash mismatch: artifact {artifact_id}")
            temp.replace(path)
        if digest(path) != expected:
            raise RuntimeError(f"Hash mismatch: {path}")
        print(f"verified {name} {artifact_id} {expected}", flush=True)

    with zipfile.ZipFile(artifacts / "agent48-box6-deps.zip") as archive:
        archive.extractall(work / "deps")
    deps = work / "deps/tmp/a49-raw10-box6-probe"
    with zipfile.ZipFile(artifacts / "box12-common.zip") as archive:
        with archive.open("box12-common.tar.gz") as member:
            with tarfile.open(fileobj=member, mode="r|gz") as tar:
                tar.extractall(work, filter="data")

    for name in ARTIFACTS:
        if name.startswith("box12-e-"):
            with zipfile.ZipFile(artifacts / name) as archive:
                for member in archive.namelist():
                    if Path(member).name != member or not member.endswith(".olean"):
                        raise RuntimeError(f"Unexpected branch member: {member}")
                    if (work / "tree" / member).exists():
                        raise RuntimeError(f"Duplicate branch member: {member}")
                archive.extractall(work / "tree")

    if digest(work / "tree/Box12Cover.lean") != "2358b8248f6cc44d205a3f2fda2764e224a35719fc85ab9fac296258a3622757":
        raise RuntimeError("Unexpected generated join source")
    source = Path(__file__).resolve().with_name("Raw10RefinedBox12.lean")
    shutil.copyfile(source, work / source.name)
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [work, work / "tree", deps])))
    log = version + "\n"
    for target in ("tree/Box12Cover", "Raw10RefinedBox12"):
        run = subprocess.run([args.lean, "-j1", "-o", target + ".olean", target + ".lean"],
                             cwd=work, env=env, capture_output=True, text=True)
        log += run.stdout + run.stderr
        print(run.stdout + run.stderr, end="", flush=True)
        (out / "box12-final.log").write_text(log)
        run.check_returncode()

    for theorem in THEOREMS:
        match = re.search(r"'" + re.escape(theorem) + r"' depends on axioms: \[([^\]]*)\]", log)
        if not match or set(map(str.strip, match.group(1).split(","))) != STANDARD:
            raise RuntimeError(f"Unexpected or missing axiom audit: {theorem}")
    if re.search(r"sorryAx|native_decide|Lean.ofReduceBool", log):
        raise RuntimeError("Unapproved trust dependency")
    with tarfile.open(out / "box12-final.tar.gz", "w:gz") as tar:
        for pattern in ("*.lean", "*.olean", "tree/*.lean", "tree/*.olean"):
            for path in sorted(work.glob(pattern)):
                tar.add(path, arcname=path.relative_to(work))
    print("Final source join and all three axiom audits passed.", flush=True)


if __name__ == "__main__":
    main()
